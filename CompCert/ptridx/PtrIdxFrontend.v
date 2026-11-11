(** * The refactoring from CompCert C (PtrIdx.v after CompCert's front end)

    ptridxgen produces Clight exactly as clightgen does, then refactors it
    (PtrIdxDriver.ml): SimplExpr turns the CompCert C program into Clight,
    SimplLocals turns local variables whose address is never taken into
    temporaries, and [PtrIdx.transf_program] rewrites the result. CompCert
    proves the first two passes correct, and PtrIdxproof.v the third; all
    three are forward simulations, so they compose into one from the CompCert
    C program to the refactored Clight.

    As in CompCert, the theorem starts at the CompCert C program: the
    preprocessor, the lexer, and the elaboration of C source into CompCert C
    are outside it, and so is printing the refactored Clight as C. *)

Require Import Errors Smallstep.
Require Csyntax Cstrategy Clight.
Require SimplExpr SimplLocals SimplExprproof SimplLocalsproof.
Require Import PtrIdx PtrIdxproof.

Theorem c_to_refactored_correct: forall (p: Csyntax.program) p1 p2 tp,
  SimplExpr.transl_program p = OK p1 ->
  SimplLocals.transf_program p1 = OK p2 ->
  PtrIdx.transf_program p2 = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Clight.semantics2 tp).
Proof.
  intros p p1 p2 tp T1 T2 T3.
  apply compose_forward_simulations with (L2 := Clight.semantics1 p1).
  - apply SimplExprproof.transl_program_correct.
    apply SimplExprproof.transf_program_match; exact T1.
  - apply compose_forward_simulations with (L2 := Clight.semantics2 p2).
    + apply SimplLocalsproof.transf_program_correct.
      apply SimplLocalsproof.match_transf_program; exact T2.
    + apply PtrIdxproof.transf_program_correct; exact T3.
Qed.
