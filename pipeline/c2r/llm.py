"""Logged OpenRouter requests and replay of previously captured responses."""

from __future__ import annotations

import json
import multiprocessing
import os
import signal
import time
from importlib.metadata import version
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Protocol

from .config import ModelConfig
from .rust_project import _atomic_json, _sha


class ModelError(RuntimeError):
    def __init__(self, message: str, *, details: dict | None = None,
                 completion: Completion | None = None):
        super().__init__(message)
        self.details = details or {}
        self.completion = completion

    def record(self) -> dict:
        record = {"status": "error", "message": str(self), "provider_error": self.details}
        for name in ("elapsed_seconds", "deadline_seconds", "timeout", "provider", "error_type", "code"):
            if name in self.details:
                record[name] = self.details[name]
        if self.completion is not None:
            record.update({name: getattr(self.completion, name) for name in (
                "model", "usage", "cost", "response_id", "finish_reason", "elapsed_seconds")})
        return record


@dataclass
class Completion:
    text: str
    model: str
    usage: dict
    cost: float | None
    finish_reason: str | None
    response_id: str | None
    elapsed_seconds: float


class ModelClient(Protocol):
    def identity(self) -> dict: ...
    def complete(self, messages: list[dict], schema: dict | None, *, seed: int, directory: Path,
                 job_id: str, call_number: int) -> Completion: ...


def _request_worker(directory: str, key: str, base_url: str, timeout: int, payload: dict) -> None:
    """One request in a killable process; credentials are never written to disk."""
    signal.signal(signal.SIGINT, signal.SIG_IGN)  # The supervisor handles interruption and cleanup.
    root = Path(directory)
    try:
        from openai import OpenAI
        # No SDK retries: a recorded reservation represents one HTTP request.
        with OpenAI(api_key=key, base_url=base_url, timeout=timeout, max_retries=0) as client:
            response = client.chat.completions.create(**payload)
            raw = response.model_dump(mode="json", exclude_none=True)
            _atomic_json(root / "response.json", raw)
    except Exception as exc:
        error = {"error_type": type(exc).__name__, "message": str(exc).replace(key, "[REDACTED]")}
        if getattr(exc, "status_code", None) is not None:
            error["code"] = exc.status_code
        _atomic_json(root / "error.json", error)


def _stop_worker(worker) -> None:
    if worker.is_alive():
        worker.terminate()
        worker.join(1)
    if worker.is_alive():
        worker.kill()
        worker.join(1)


class OpenRouterClient:
    def __init__(self, config: ModelConfig):
        if not config.id:
            raise ValueError("set model.id before running live translation")
        key = os.environ.get(config.api_key_env)
        if not key:
            raise ValueError(f"{config.api_key_env} is required for live translation")
        self.config = config
        self._key = key

    def identity(self) -> dict:
        identity = {"transport": "openrouter", "model": self.config.id, "base_url": self.config.base_url,
                "temperature": self.config.temperature, "max_tokens": self.config.max_tokens,
                "timeout": self.config.timeout, "response_format": self.config.response_format,
                "sdk_version": version("openai")}
        if self.config.reasoning_effort is not None:
            identity["reasoning_effort"] = self.config.reasoning_effort
        return identity

    def _request(self, payload: dict, directory: Path) -> tuple[dict, float]:
        started = time.monotonic()
        worker = multiprocessing.get_context("spawn").Process(target=_request_worker,
            args=(str(directory), self._key, self.config.base_url, self.config.timeout, payload),
            daemon=True)
        worker_started = False
        try:
            worker.start()
            worker_started = True
            worker.join(max(0, self.config.timeout - (time.monotonic() - started)))
            elapsed = time.monotonic() - started
            if worker.is_alive():
                _stop_worker(worker)
                raise ModelError(f"model request exceeded the {self.config.timeout}s wall-clock deadline; request worker terminated",
                    details={"error_type": "RequestDeadlineExceeded", "timeout": True,
                             "deadline_seconds": self.config.timeout, "elapsed_seconds": elapsed,
                             "remote_cancellation_confirmed": False})
            error_path = directory / "error.json"
            if error_path.is_file():
                error = json.loads(error_path.read_text())
                error["elapsed_seconds"] = elapsed
                error["timeout"] = error.get("error_type") == "APITimeoutError"
                raise ModelError(error["message"], details=error)
            response_path = directory / "response.json"
            if worker.exitcode != 0 or not response_path.is_file():
                raise ModelError(f"model request worker exited without a response (exit {worker.exitcode})",
                    details={"error_type": "RequestWorkerError", "elapsed_seconds": elapsed})
            return json.loads(response_path.read_text()), elapsed
        finally:
            if worker_started:
                _stop_worker(worker)
                if not worker.is_alive():
                    worker.close()

    def complete(self, messages: list[dict], schema: dict | None, *, seed: int, directory: Path,
                 job_id: str, call_number: int) -> Completion:
        payload = {"model": self.config.id, "messages": messages, "temperature": self.config.temperature,
                   "max_tokens": self.config.max_tokens, "seed": seed, "stream": False}
        if schema is not None and self.config.response_format == "json_schema":
            payload["response_format"] = {"type": "json_schema", "json_schema": {
                "name": "rust_translation", "strict": True, "schema": schema}}
        elif schema is not None and self.config.response_format == "json_object":
            payload["response_format"] = {"type": "json_object"}
        extra_body = {}
        if self.config.reasoning_effort is not None:
            extra_body["reasoning"] = {"effort": self.config.reasoning_effort}
        if extra_body or (schema is not None and self.config.response_format != "none"):
            # Ask the router to select a provider that supports the requested controls.
            extra_body["provider"] = {"require_parameters": True}
        if extra_body:
            payload["extra_body"] = extra_body
        directory.mkdir(parents=True, exist_ok=False)
        _atomic_json(directory / "request.json", {"job_id": job_id, "call_number": call_number,
                     "started_at": datetime.now(timezone.utc).isoformat(), "request": payload,
                     "deadline_seconds": self.config.timeout, "deadline_enforced": True})
        try:
            raw, elapsed = self._request(payload, directory)
        except ModelError as exc:
            _atomic_json(directory / "error.json", {**exc.details, "message": str(exc)})
            raise
        choices = raw.get("choices") or []
        choice = choices[0] if choices and isinstance(choices[0], dict) else {}
        message = choice.get("message") or {}
        message = message if isinstance(message, dict) else {}
        text = message.get("content")
        usage = raw.get("usage") or {}
        cost = usage.get("cost")
        result = Completion(text if isinstance(text, str) else "", raw.get("model", self.config.id), usage,
                            float(cost) if isinstance(cost, (int, float)) else None,
                            choice.get("finish_reason"), raw.get("id"), elapsed)
        _atomic_json(directory / "metrics.json", {**result.__dict__, "text": None})
        error = raw.get("error") or choice.get("error")
        provider = raw.get("provider") or "OpenRouter"
        if error or result.finish_reason == "error" or not choices:
            error = error if isinstance(error, dict) else {"message": str(error)} if error else {}
            metadata = error.get("metadata") or {}
            metadata = metadata if isinstance(metadata, dict) else {}
            description = error.get("message") or ("returned finish_reason=error without a final answer"
                                                   if choices else "returned no completion")
            code = error.get("code")
            description = f"{provider}{f' ({code})' if code is not None else ''}: {description}"
            description = description.replace(self._key, "[REDACTED]")
            details = {"provider": provider, "error_type": metadata.get("error_type", "ProviderError"),
                       "code": code, "finish_reason": result.finish_reason, "elapsed_seconds": elapsed}
            _atomic_json(directory / "error.json", {**details, "message": description})
            raise ModelError(description, details=details, completion=result)
        # Reasoning-only truncations are charged responses too. Let the runner
        # record usage and finish_reason before applying its bounded retry rule.
        if result.finish_reason == "length":
            return result
        if message.get("refusal") or not result.text.strip():
            description = f"{provider}: " + ("provider refused the request" if message.get("refusal")
                                            else "provider returned an empty final answer")
            details = {"provider": provider, "error_type": "Refusal" if message.get("refusal") else "EmptyCompletion",
                       "finish_reason": result.finish_reason, "elapsed_seconds": elapsed}
            _atomic_json(directory / "error.json", {**details, "message": description})
            raise ModelError(description, details=details, completion=result)
        return result

    def close(self) -> None:
        pass  # Each request closes its client and its supervised worker.


class ReplayClient:
    """Replay a JSON list of {job_id, response} records; never contacts a provider.

    A record's response is either raw model text or the structured output object.
    Global call_number indexing makes replay consumption stable after resume.
    """
    def __init__(self, path: Path):
        self.path = path.resolve()
        raw = self.path.read_bytes()
        self.digest = _sha(raw)
        self.records = json.loads(raw)
        if not isinstance(self.records, list):
            raise ValueError("replay input must be a list of job_id/response records")

    def identity(self) -> dict:
        return {"transport": "replay", "responses_sha256": self.digest}

    def complete(self, messages: list[dict], schema: dict | None, *, seed: int, directory: Path,
                 job_id: str, call_number: int) -> Completion:
        if call_number > len(self.records):
            raise ModelError("replay input has no response for this call number")
        entry = self.records[call_number - 1]
        if not isinstance(entry, dict) or entry.get("job_id") != job_id or "response" not in entry:
            raise ModelError(f"replay record {call_number} does not match {job_id}")
        content = entry["response"]
        text = content if isinstance(content, str) else json.dumps(content)
        directory.mkdir(parents=True, exist_ok=False)
        _atomic_json(directory / "request.json", {"job_id": job_id, "call_number": call_number,
                     "seed": seed, "messages": messages, "schema": schema, "replay": True})
        _atomic_json(directory / "response.json", {"text": text, "replay": True})
        result = Completion(text, "replay", {}, None, "stop", None, 0.0)
        _atomic_json(directory / "metrics.json", {**result.__dict__, "text": None})
        return result
