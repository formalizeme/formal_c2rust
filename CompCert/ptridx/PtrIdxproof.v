(** * Correctness of the pointer-arithmetic refactoring (PtrIdx.v)

    This file is built in stages. Stage 1 is the arithmetic every rewrite
    relies on. Stages 2 and 3 ([transf_program_correct_nocache]) are the simulation for the pass
    without caches ([transf_program_plan share false]), with or without
    shared bases; [transf_program_correct], at the end, states it for
    [transf_program]. The caches for pointers stored in memory are not
    covered: ptridxgen leaves them off unless given -memory. A member of a group whose base was rewritten for
    another member is dead there ([plan_ok]'s liveness check), so the
    simulation only relates live members ([kill]).

    A split pointer [p] is represented by a base [b] and a [long] index [i],
    and its value is [b + sz * i] computed exactly as Clight computes pointer
    arithmetic ([at_index]). Offsetting [p] by [n] elements is offsetting its
    index by [n], and the widened [n] is exactly the [n] Clight adds. All of
    this is modulo 2^64, like Clight's pointer offsets. The target has 64-bit
    pointers ([Archi.ptr64]). *)

Require Import Coqlib Maps Integers Floats Values AST Memory Globalenvs.
Require Import Ctypes Cop Clight.
Require Import PtrIdx.

Lemma ptr64: Archi.ptr64 = true.
Proof. reflexivity. Qed.

(** ** Values a pointer can hold where its value is used

    A use of a pointer that converts it (arithmetic, comparison, dereference,
    cast, call argument) succeeds only on a pointer [Vptr] or an integer
    pointer [Vlong], on a 64-bit target. *)
Definition ptrish (v: val) : Prop :=
  match v with Vptr _ _ | Vlong _ => True | _ => False end.

(** ** Base plus index *)

Definition at_index (sz: Z) (b: val) (i: int64) : option val :=
  match b with
  | Vptr blk ofs => Some (Vptr blk (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 i))))
  | Vlong n => Some (Vlong (Int64.add n (Int64.mul (Int64.repr sz) i)))
  | _ => None
  end.

Lemma at_index_ptrish: forall sz b i v, at_index sz b i = Some v -> ptrish v /\ ptrish b.
Proof.
  unfold at_index; intros. destruct b; inv H; simpl; auto.
Qed.

(** [base + idx] as Clight evaluates it: [sem_add_ptr_long]. *)
Lemma sem_add_ptr_long_at: forall ce ty b i,
  sem_add_ptr_long ce ty b (Vlong i) = at_index (sizeof ce ty) b i.
Proof.
  intros. unfold sem_add_ptr_long, at_index. rewrite ptr64. destruct b; auto.
Qed.

(** Ptrofs and Int64 agree on 64 bits. *)
Lemma of_int64_add: forall i j,
  Ptrofs.of_int64 (Int64.add i j) = Ptrofs.add (Ptrofs.of_int64 i) (Ptrofs.of_int64 j).
Proof.
  intros. apply Ptrofs.agree64_of_int_eq.
  apply (Ptrofs.agree64_add ptr64); apply (Ptrofs.agree64_of_int ptr64).
Qed.

Lemma of_int64_sub: forall i j,
  Ptrofs.of_int64 (Int64.sub i j) = Ptrofs.sub (Ptrofs.of_int64 i) (Ptrofs.of_int64 j).
Proof.
  intros. apply Ptrofs.agree64_of_int_eq.
  apply (Ptrofs.agree64_sub ptr64); apply (Ptrofs.agree64_of_int ptr64).
Qed.

Lemma of_int64_zero: Ptrofs.of_int64 Int64.zero = Ptrofs.zero.
Proof.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_zero. reflexivity.
Qed.

(** The index Clight adds for an [int] offset, [ptrofs_of_int], is the
    widened offset [cast_int_long]. *)
Lemma ptrofs_of_int_long: forall si n,
  ptrofs_of_int si n = Ptrofs.of_int64 (cast_int_long si n).
Proof.
  intros. unfold ptrofs_of_int, cast_int_long, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int64.
  destruct si; apply Ptrofs.eqm_samerepr; apply (proj1 (Ptrofs.eqm64 ptr64 _ _)); apply Int64.eqm_unsigned_repr.
Qed.

Lemma at_index_zero: forall sz v, ptrish v -> at_index sz v Int64.zero = Some v.
Proof.
  unfold at_index; intros. destruct v; try contradiction.
  - rewrite Int64.mul_zero, Int64.add_zero; auto.
  - rewrite of_int64_zero, Ptrofs.mul_zero, Ptrofs.add_zero; auto.
Qed.

(** Moving a pointer by [j] elements moves its index by [j]. *)
Lemma at_index_add: forall sz b i v j,
  at_index sz b i = Some v ->
  at_index sz v j = at_index sz b (Int64.add i j).
Proof.
  unfold at_index; intros. destruct b; inv H; f_equal.
  - f_equal. rewrite Int64.add_assoc, Int64.mul_add_distr_r. auto.
  - f_equal. rewrite of_int64_add, Ptrofs.mul_add_distr_r, Ptrofs.add_assoc. auto.
Qed.

Lemma at_index_sub: forall sz b i v j,
  at_index sz b i = Some v ->
  at_index sz v (Int64.neg j) = at_index sz b (Int64.sub i j).
Proof.
  intros. rewrite (at_index_add _ _ _ _ _ H). rewrite Int64.sub_add_opp. auto.
Qed.

(** ** Clight's pointer offsets on a value in base + index form *)

Lemma sem_add_ptr_int_at: forall ce ty si b i v n,
  at_index (sizeof ce ty) b i = Some v ->
  sem_add_ptr_int ce ty si v (Vint n) = at_index (sizeof ce ty) b (Int64.add i (cast_int_long si n)).
Proof.
  intros. rewrite <- (at_index_add _ _ _ _ _ H).
  unfold sem_add_ptr_int, at_index. rewrite ptr64.
  destruct v; auto. rewrite ptrofs_of_int_long. auto.
Qed.

Lemma sem_add_ptr_long_at': forall ce ty b i v n,
  at_index (sizeof ce ty) b i = Some v ->
  sem_add_ptr_long ce ty v (Vlong n) = at_index (sizeof ce ty) b (Int64.add i n).
Proof.
  intros. rewrite <- (at_index_add _ _ _ _ _ H). apply sem_add_ptr_long_at.
Qed.

(** Clight's pointer-minus-integer, as an offset by the negated index. *)
Lemma sub_ptr_int_at: forall ce ty si b i v n,
  at_index (sizeof ce ty) b i = Some v ->
  match v, Vint n with
  | Vptr b1 ofs1, Vint n2 =>
      Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ce ty)) (ptrofs_of_int si n2))))
  | Vlong n1, Vint n2 =>
      if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ce ty)) (cast_int_long si n2))))
      else None
  | _, _ => None
  end = at_index (sizeof ce ty) b (Int64.sub i (cast_int_long si n)).
Proof.
  intros. rewrite <- (at_index_sub _ _ _ _ _ H). rewrite ptr64.
  unfold at_index. destruct v; auto.
  - rewrite Int64.sub_add_opp, Int64.neg_mul_distr_r. auto.
  - rewrite ptrofs_of_int_long, Ptrofs.sub_add_opp, Ptrofs.neg_mul_distr_r. do 4 f_equal.
    symmetry. apply Ptrofs.agree64_of_int_eq.
    apply (Ptrofs.agree64_neg ptr64). apply (Ptrofs.agree64_of_int ptr64).
Qed.

Lemma sub_ptr_long_at: forall ce ty b i v n,
  at_index (sizeof ce ty) b i = Some v ->
  match v, Vlong n with
  | Vptr b1 ofs1, Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2 in
      Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ce ty)) n2)))
  | Vint n1, Vlong n2 =>
      let n2 := Int.repr (Int64.unsigned n2) in
      if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof ce ty)) n2)))
  | Vlong n1, Vlong n2 =>
      if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ce ty)) n2))) else None
  | _, _ => None
  end = at_index (sizeof ce ty) b (Int64.sub i n).
Proof.
  intros. rewrite <- (at_index_sub _ _ _ _ _ H). rewrite ptr64.
  unfold at_index. destruct v; auto.
  - rewrite Int64.sub_add_opp, Int64.neg_mul_distr_r. auto.
  - rewrite Ptrofs.sub_add_opp, Ptrofs.neg_mul_distr_r. do 4 f_equal.
    symmetry. apply Ptrofs.agree64_of_int_eq.
    apply (Ptrofs.agree64_neg ptr64). apply (Ptrofs.agree64_of_int ptr64).
Qed.

(** ** Arithmetic on [long] indices *)

Lemma long_add: forall (ce: composite_env) m i j si a,
  sem_binary_operation ce Oadd (Vlong i) tlong (Vlong j) (Tlong si a) m = Some (Vlong (Int64.add i j)).
Proof.
  intros. simpl. unfold sem_add, classify_add, tlong. simpl.
  unfold sem_binarith. simpl. destruct si; simpl; try rewrite ptr64; reflexivity.
Qed.

Lemma long_sub: forall (ce: composite_env) m i j si a,
  sem_binary_operation ce Osub (Vlong i) tlong (Vlong j) (Tlong si a) m = Some (Vlong (Int64.sub i j)).
Proof.
  intros. simpl. unfold sem_sub, classify_sub, tlong. simpl.
  unfold sem_binarith. simpl. destruct si; simpl; try rewrite ptr64; reflexivity.
Qed.

(** ** Evaluating the rewritten expressions *)

Section EVAL.

Variable ge: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

(** The three shapes [widen] produces for an [int] offset. *)
Lemma widen_cases: forall si n,
  (exists i ty, n = Econst_int i ty /\ widen (Some si) n = Econst_long (cast_int_long si i) tlong)
  \/ (exists a, typeof n = Tint I32 si a /\ widen (Some si) n = Ecast n tlong)
  \/ widen (Some si) n = Ecast (Ecast n (Tint I32 si noattr)) tlong.
Proof.
  intros. destruct n;
    try (left; do 2 eexists; split; [reflexivity | destruct si; reflexivity]);
    right; simpl; destruct si;
    repeat match goal with [ |- context[match ?x with _ => _ end] ] => destruct x end;
    first [left; eexists; split; reflexivity | right; reflexivity].
Qed.

(** [widen si n] evaluates to Clight's widening of [n]'s value. *)
Lemma eval_widen_int: forall si n v sz si' a,
  eval_expr ge e le m n (Vint v) ->
  typeof n = Tint sz si' a ->
  eval_expr ge e le m (widen (Some si) n) (Vlong (cast_int_long si v)).
Proof.
  intros si n v sz si' a EV TY.
  destruct (widen_cases si n) as [(i & ty & N & W) | [(a' & TY' & W) | W]]; rewrite W.
  - subst n. inv EV. constructor. inv H.
  - econstructor; eauto. unfold sem_cast, classify_cast, tlong. rewrite TY'. reflexivity.
  - econstructor. econstructor. eauto.
    unfold sem_cast, classify_cast. rewrite TY. reflexivity.
    reflexivity.
Qed.


(** [B + I], with [B] a pointer temporary and [I] a [long] index. *)
Lemma eval_base_plus: forall xb t a xi b i v ty,
  le!xb = Some b -> le!xi = Some (Vlong i) ->
  at_index (sizeof ge t) b i = Some v ->
  eval_expr ge e le m (Ebinop Oadd (Etempvar xb (Tpointer t a)) (Etempvar xi tlong) ty) v.
Proof.
  intros. econstructor; try (constructor; eauto).
  simpl. unfold sem_add, classify_add. simpl. rewrite sem_add_ptr_long_at. auto.
Qed.

(** [B + (I +/- w)], with [w] a [long]. *)
Lemma eval_base_plus_offset: forall xb t a xi b i w c si wa (sub: bool) ty v,
  le!xb = Some b -> le!xi = Some (Vlong i) ->
  eval_expr ge e le m w (Vlong c) -> typeof w = Tlong si wa ->
  at_index (sizeof ge t) b (if sub then Int64.sub i c else Int64.add i c) = Some v ->
  eval_expr ge e le m (Ebinop Oadd (Etempvar xb (Tpointer t a))
                              (Ebinop (if sub then Osub else Oadd) (Etempvar xi tlong) w tlong) ty) v.
Proof.
  intros. destruct sub.
  - eapply eval_Ebinop with (v2 := Vlong (Int64.sub i c)). constructor; eauto.
    eapply eval_Ebinop. constructor; eauto. eauto. simpl; rewrite H2; apply (long_sub ge).
    simpl. unfold sem_add, classify_add. simpl. rewrite sem_add_ptr_long_at. auto.
  - eapply eval_Ebinop with (v2 := Vlong (Int64.add i c)). constructor; eauto.
    eapply eval_Ebinop. constructor; eauto. eauto. simpl; rewrite H2; apply (long_add ge).
    simpl. unfold sem_add, classify_add. simpl. rewrite sem_add_ptr_long_at. auto.
Qed.

End EVAL.

(** Destructs what a hypothesis matches on, innermost match first (so that
    each case reduces), until the hypothesis is refuted. *)
Ltac refute_matches :=
  repeat match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] =>
      lazymatch x with
      | context[match _ with _ => _ end] => fail
      | _ => destruct x; simpl in H; try discriminate
      end
  end; try discriminate.

Ltac unfold_ops H :=
  unfold sem_add, sem_sub, sem_mul, sem_div, sem_mod, sem_and, sem_or, sem_xor, sem_shl, sem_shr,
         sem_cmp, sem_binarith, sem_shift, classify_add, classify_sub, classify_binarith, classify_shift,
         classify_cmp, cmp_ptr, Val.cmplu_bool, option_map in H; try rewrite ptr64 in H; simpl in H.

(** ** Uses that need a pointer

    Each of these operations, applied to an operand of pointer type,
    succeeds only on a pointer or an integer pointer. *)

Lemma binop_ptr_left: forall ce op v1 t a v2 t2 m v,
  sem_binary_operation ce op v1 (Tpointer t a) v2 t2 m = Some v -> ptrish v1.
Proof.
  intros. destruct v1; simpl; auto; exfalso; destruct op; simpl in H; unfold_ops H; refute_matches.
Qed.

Lemma binop_ptr_right: forall ce op v1 t1 v2 t a m v,
  sem_binary_operation ce op v1 t1 v2 (Tpointer t a) m = Some v -> ptrish v2.
Proof.
  intros. destruct v2; simpl; auto; exfalso; destruct op; simpl in H; unfold_ops H; refute_matches.
Qed.

Lemma unop_ptr: forall op v t a m v',
  sem_unary_operation op v (Tpointer t a) m = Some v' -> ptrish v.
Proof.
  intros. destruct v; simpl; auto; exfalso; destruct op; simpl in H;
  unfold sem_notbool, bool_val, classify_bool, sem_notint, classify_notint, sem_neg, classify_neg,
         sem_absfloat in H; try rewrite ptr64 in H; simpl in H; refute_matches.
Qed.

Lemma bool_val_ptr: forall v t a m b,
  bool_val v (Tpointer t a) m = Some b -> ptrish v.
Proof.
  intros. destruct v; simpl; auto; exfalso; unfold bool_val, classify_bool in H; try rewrite ptr64 in H; simpl in H;
  refute_matches.
Qed.

(** Every cast of a pointer needs a pointer, except the cast to [void]. *)
Lemma cast_ptr: forall v t a ty m v',
  sem_cast v (Tpointer t a) ty m = Some v' -> ty <> Tvoid -> ptrish v.
Proof.
  intros. destruct v; simpl; auto; exfalso; unfold sem_cast, classify_cast in H; destruct ty;
  try congruence; try rewrite ptr64 in H; simpl in H; refute_matches.
Qed.

(** * Stages 2 and 3: the simulation, without caches

    [transf_program_plan share false]: groups share a base when [share] is
    set (and [plan_ok]'s liveness check holds), and pointers stored in memory
    are left alone. *)

Require Import Errors Linking Smallstep Events.

(** ** The two programs *)

Section PROGRAMS.

Variable share: bool.
Variable prog: program.

Let ce := prog_comp_env prog.
Let nw := nonwriting (prog_defs prog).

Definition tprog := fst (transf_program_plan share false prog).

Inductive match_fundef (ctx: AST.program fundef type) : fundef -> fundef -> Prop :=
  | match_fundef_internal: forall f next tf sps cl fb n,
      transf_function ce nw share false f next = (tf, sps, cl, fb, n) ->
      match_fundef ctx (Internal f) (Internal tf)
  | match_fundef_external: forall ef targs tres cc,
      match_fundef ctx (External ef targs tres cc) (External ef targs tres cc).

Lemma transf_defs_match: forall defs next,
  list_forall2 (match_ident_globdef match_fundef eq prog) defs (fst (transf_defs ce nw share false defs next)).
Proof.
  induction defs as [ | [id gd] defs IH]; intros; simpl.
  - constructor.
  - destruct gd as [[f | ef targs tres cc] | v].
    + destruct (transf_function ce nw share false f next) as [[[[tf sps] cl] fb] n] eqn:TF.
      destruct (transf_defs ce nw share false defs n) as [defs' pl] eqn:TD. simpl.
      constructor. split; auto. econstructor. apply linkorder_refl. econstructor; eauto.
      specialize (IH n). rewrite TD in IH. exact IH.
    + destruct (transf_defs ce nw share false defs next) as [defs' pl] eqn:TD. simpl.
      constructor. split; auto. econstructor. apply linkorder_refl. constructor.
      specialize (IH next). rewrite TD in IH. exact IH.
    + destruct (transf_defs ce nw share false defs next) as [defs' pl] eqn:TD. simpl.
      constructor. split; auto. constructor. destruct v; constructor; auto.
      specialize (IH next). rewrite TD in IH. exact IH.
Qed.

Lemma tprog_match: match_program match_fundef eq prog tprog.
Proof.
  unfold match_program, match_program_gen, tprog, transf_program_plan.
  destruct (transf_defs (prog_comp_env prog) (nonwriting (prog_defs prog)) share false (prog_defs prog)
                        (Pos.succ (max_program prog))) as [defs' pl] eqn:TD.
  simpl. split; auto.
  pose proof (transf_defs_match (prog_defs prog) (Pos.succ (max_program prog))) as M.
  unfold ce, nw in M. rewrite TD in M. exact M.
Qed.

Lemma tprog_comp_env: prog_comp_env tprog = prog_comp_env prog.
Proof.
  unfold tprog, transf_program_plan.
  destruct (transf_defs _ _ _ _ _ _) as [defs' pl]. reflexivity.
Qed.

Let ge := Clight.globalenv prog.
Let tge := Clight.globalenv tprog.

Lemma comp_env_preserved: genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. simpl. apply tprog_comp_env.
Qed.

Lemma symbols_preserved: forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. exact (Genv.find_symbol_match tprog_match). Qed.

Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_match tprog_match). Qed.

Lemma functions_translated: forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ match_fundef prog f tf.
Proof.
  intros. exploit (Genv.find_funct_match tprog_match); eauto. intros (cu & tf & A & B & C).
  exists tf; split; auto. inv B; econstructor; eauto.
Qed.

Lemma function_ptr_translated: forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ match_fundef prog f tf.
Proof.
  intros. exploit (Genv.find_funct_ptr_match tprog_match); eauto. intros (cu & tf & A & B & C).
  exists tf; split; auto. inv B; econstructor; eauto.
Qed.

(** The rewritten function has the same signature: [transf_function] only
    changes temporaries and the body, or returns [f] itself. *)
Lemma transf_function_sig: forall f next tf sps cl fb n,
  transf_function ce nw share false f next = (tf, sps, cl, fb, n) ->
  fn_params tf = fn_params f /\ fn_return tf = fn_return f /\ fn_callconv tf = fn_callconv f
  /\ fn_vars tf = fn_vars f.
Proof.
  unfold transf_function; intros.
  destruct (plan_function ce share f next) as [[sps0 labs] next1].
  destruct (PTree.elements sps0); simpl in H.
  - inv H; auto.
  - destruct (tr_stmt ce sps0 nil nw (fn_vars f) empty_state (fn_body f)) as [[body' o] | ]; simpl in H.
    + destruct (plan_ok _ _ _ _ _ _ _); inv H; auto.
    + inv H; auto.
Qed.

Lemma type_of_fundef_preserved: forall f tf,
  match_fundef prog f tf -> type_of_fundef tf = type_of_fundef f.
Proof.
  intros. inv H; auto. simpl. unfold type_of_function.
  destruct (transf_function_sig _ _ _ _ _ _ _ H0) as (A & B & C & D). rewrite A, B, C. auto.
Qed.

End PROGRAMS.

(** ** Index comparisons: the same base, elements of size 1 *)

Lemma of_int64_eq: forall i1 i2,
  Ptrofs.eq (Ptrofs.of_int64 i1) (Ptrofs.of_int64 i2) = Int64.eq i1 i2.
Proof.
  intros. generalize (Int64.eq_spec i1 i2). destruct (Int64.eq i1 i2); intro EQ.
  - subst. apply Ptrofs.eq_true.
  - apply Ptrofs.eq_false. intro E. apply EQ.
    rewrite <- (Ptrofs.to_int64_of_int64 ptr64 i1), <- (Ptrofs.to_int64_of_int64 ptr64 i2), E. auto.
Qed.

Lemma at_index_one: forall b i,
  at_index 1 b i = match b with
                   | Vptr blk o => Some (Vptr blk (Ptrofs.add o (Ptrofs.of_int64 i)))
                   | Vlong n => Some (Vlong (Int64.add n i))
                   | _ => None
                   end.
Proof.
  intros. unfold at_index. destruct b; auto.
  - rewrite Int64.mul_commut, Int64.mul_one. auto.
  - rewrite Ptrofs.mul_commut, Ptrofs.mul_one. auto.
Qed.

(** The comparison of two longs, as Clight computes it. *)
Lemma long_cmp: forall ce m op c i1 i2,
  (op = Oeq /\ c = Ceq) \/ (op = One /\ c = Cne) ->
  sem_binary_operation ce op (Vlong i1) tlong (Vlong i2) tlong m = Some (Val.of_bool (Int64.cmp c i1 i2)).
Proof.
  intros. destruct H as [[A B] | [A B]]; subst; simpl; unfold sem_cmp, sem_binarith, tlong; simpl;
  try rewrite ptr64; reflexivity.
Qed.

Lemma cmp_index: forall ce m op b i1 i2 v1 v2 ta1 ta2 r,
  op = Oeq \/ op = One ->
  classify_cmp ta1 ta2 = cmp_case_pp ->
  at_index 1 b i1 = Some v1 -> at_index 1 b i2 = Some v2 ->
  sem_binary_operation ce op v1 ta1 v2 ta2 m = Some r ->
  sem_binary_operation ce op (Vlong i1) tlong (Vlong i2) tlong m = Some r.
Proof.
  intros until r; intros OP CL A1 A2 SEM.
  assert (C: exists c, (op = Oeq /\ c = Ceq) \/ (op = One /\ c = Cne)).
  { destruct OP; subst; eauto. }
  destruct C as [c C]. rewrite (long_cmp ce m op c i1 i2 C).
  assert (S: sem_binary_operation ce op v1 ta1 v2 ta2 m = cmp_ptr m c v1 v2).
  { destruct C as [[X Y] | [X Y]]; subst; simpl; unfold sem_cmp; rewrite CL; auto. }
  rewrite S in SEM. clear S.
  rewrite at_index_one in A1, A2. unfold cmp_ptr in SEM. rewrite ptr64 in SEM.
  destruct b; inv A1; inv A2; simpl in SEM.
  - inv SEM. destruct C as [[X Y] | [X Y]]; subst; simpl;
    rewrite (Int64.add_commut i i1), (Int64.add_commut i i2), Int64.translate_eq; auto.
  - destruct (eq_block b b); [ | congruence].
    destruct (_ && _); inv SEM.
    destruct C as [[X Y] | [X Y]]; subst; simpl; f_equal; f_equal;
    rewrite (Ptrofs.add_commut i (Ptrofs.of_int64 i1)), (Ptrofs.add_commut i (Ptrofs.of_int64 i2));
    rewrite Ptrofs.translate_eq, of_int64_eq; auto.
Qed.

Lemma sub_index: forall ce m b i1 i2 v1 v2 ta1 ta2 t r,
  classify_sub ta1 ta2 = sub_case_pp t -> sizeof ce t = 1 ->
  at_index 1 b i1 = Some v1 -> at_index 1 b i2 = Some v2 ->
  sem_binary_operation ce Osub v1 ta1 v2 ta2 m = Some r ->
  sem_binary_operation ce Osub (Vlong i1) tlong (Vlong i2) tlong m = Some r.
Proof.
  intros until r; intros CL SZ A1 A2 SEM.
  transitivity (Some (Vlong (Int64.sub i1 i2))). exact (long_sub ce m i1 i2 Signed noattr).
  simpl in SEM. unfold sem_sub in SEM. rewrite CL, SZ in SEM.
  rewrite at_index_one in A1, A2.
  destruct b; inv A1; inv A2; try discriminate.
  destruct (eq_block b b); [ | congruence]. simpl in SEM.
  destruct (zle 1 Ptrofs.max_signed); simpl in SEM; [ | discriminate]. inv SEM.
  unfold Vptrofs. rewrite ptr64. f_equal. f_equal.
  rewrite (Ptrofs.add_commut i (Ptrofs.of_int64 i1)), (Ptrofs.add_commut i (Ptrofs.of_int64 i2)).
  rewrite Ptrofs.sub_shifted, <- of_int64_sub.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one.
  symmetry; apply (Ptrofs.to_int64_of_int64 ptr64).
  unfold Ptrofs.zwordsize, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize. rewrite ptr64. simpl. lia.
Qed.

(** ** Expressions with split temporaries *)

Lemma widen_typeof: forall si n, typeof (widen (Some si) n) = tlong.
Proof.
  intros. destruct (widen_cases si n) as [(i & ty & N & W) | [(a & TY & W) | W]]; rewrite W; auto.
Qed.

Lemma typeconv_int: forall t sz si a, typeconv t = Tint sz si a -> exists sz' si' a', t = Tint sz' si' a'.
Proof.
  intros. destruct t; simpl in H; try discriminate; eauto.
Qed.

Lemma typeconv_long: forall t si a, typeconv t = Tlong si a -> exists a', t = Tlong si a'.
Proof.
  intros. destruct t; simpl in H; try (destruct i); try discriminate; inv H; eauto.
Qed.

(** What Clight computes for [p + n] or [p - n] when [p] is [b + s * i]: [b]
    plus the index moved by [c], where [c] is how [n] is widened. *)
Lemma offset_sem: forall ce m op a1 a2 tq sub si v1 v2 v t ta b i,
  ptr_offset op a1 a2 = Some (tq, sub, si) ->
  tq = Tpointer t ta ->
  sem_binary_operation ce op v1 (typeof a1) v2 (typeof a2) m = Some v ->
  at_index (sizeof ce t) b i = Some v1 ->
  exists c, at_index (sizeof ce t) b (if sub then Int64.sub i c else Int64.add i c) = Some v
    /\ match si with
       | None => v2 = Vlong c /\ exists si' a', typeof a2 = Tlong si' a'
       | Some si0 => exists n sz si' a', v2 = Vint n /\ c = cast_int_long si0 n /\ typeof a2 = Tint sz si' a'
       end.
Proof.
  intros until i; intros PO TQ SEM AT.
  unfold ptr_offset in PO. destruct op; try discriminate.
  - (* + *)
    simpl in SEM. unfold sem_add in SEM.
    destruct (classify_add (typeof a1) (typeof a2)) as [ty0 s0 | ty0 | s0 ty0 | ty0 | ] eqn:CA; try discriminate;
    injection PO as E1 E2 E3; subst tq sub si;
    unfold classify_add in CA; rewrite TQ in CA; simpl in CA;
    destruct (typeconv (typeof a2)) eqn:TC; inv CA.
    + (* pointer + int *)
      destruct (typeconv_int _ _ _ _ TC) as (sz' & si' & a' & T2).
      destruct v2 as [ | n | n | f | f | b' o']; try (destruct v1; simpl in SEM; try rewrite ptr64 in SEM; discriminate).
      exists (cast_int_long s0 n). split.
      * rewrite <- (sem_add_ptr_int_at _ _ _ _ _ _ _ AT). auto.
      * simpl. eauto 7.
    + (* pointer + long *)
      destruct (typeconv_long _ _ _ TC) as (a' & T2).
      destruct v2 as [ | n | n | f | f | b' o']; try (destruct v1; simpl in SEM; try rewrite ptr64 in SEM; discriminate).
      exists n. split.
      * rewrite <- (sem_add_ptr_long_at' _ _ _ _ _ _ AT). auto.
      * simpl. eauto.
  - (* - *)
    simpl in SEM. unfold sem_sub in SEM.
    destruct (classify_sub (typeof a1) (typeof a2)) as [ty0 s0 | ty0 | ty0 | ] eqn:CS; try discriminate;
    injection PO as E1 E2 E3; subst tq sub si;
    unfold classify_sub in CS; rewrite TQ in CS; simpl in CS;
    destruct (typeconv (typeof a2)) eqn:TC; inv CS.
    + destruct (typeconv_int _ _ _ _ TC) as (sz' & si' & a' & T2).
      destruct v2 as [ | n | n | f | f | b' o']; try (destruct v1; simpl in SEM; try rewrite ptr64 in SEM; discriminate).
      exists (cast_int_long s0 n). split.
      * rewrite <- (sub_ptr_int_at _ _ s0 _ _ _ n AT). auto.
      * simpl. eauto 7.
    + destruct (typeconv_long _ _ _ TC) as (a' & T2).
      destruct v2 as [ | n | n | f | f | b' o']; try (destruct v1; simpl in SEM; try rewrite ptr64 in SEM; discriminate).
      exists n. split.
      * rewrite <- (sub_ptr_long_at _ _ _ _ _ n AT). auto.
      * simpl. eauto.
Qed.

Section EXPRESSIONS.

Variable ge tge: genv.
Hypothesis CENV: genv_cenv tge = genv_cenv ge.
Hypothesis SYMB: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.

Let ce := genv_cenv ge.

Variable sps: splits.
Variable top: positive.

(** From [plan_ok]: a split's base has a pointer type, whose target's size is
    the index unit. *)
Hypothesis SHAPE: forall x s, sps!x = Some s ->
  exists t ta, sp_type s = Tpointer t ta /\ sp_size s = sizeof ce t.

(** A split temporary that holds a pointer (or an integer pointer) [v] is
    [base + sz * idx] in the target. Anything else it holds is never used
    (only copied), so nothing is required of it. *)
Definition rel (s: split) (v: val) (tle: temp_env) : Prop :=
  ptrish v -> exists b i, tle!(sp_base s) = Some b /\ tle!(sp_idx s) = Some (Vlong i)
                          /\ at_index (sp_size s) b i = Some v.

(** The source's temporaries are [f]'s own identifiers, all at most [top];
    the new ones are above [top]. *)
Record match_temps (le tle: temp_env) : Prop := {
  mt_same: forall x, Ple x top -> sps!x = None -> tle!x = le!x;
  mt_split: forall x s v, sps!x = Some s -> le!x = Some v -> rel s v tle;
  mt_defined: forall x s, sps!x = Some s -> tle!(sp_base s) <> None /\ tle!(sp_idx s) <> None;
  mt_above: forall x, Plt top x -> le!x = None
}.

Let TR := tr_expr ce sps nil nil.

Lemma index_form_typeof: forall op a1 n ty e',
  index_form ce sps nil op a1 n ty = Some e' -> typeof e' = ty.
Proof.
  unfold index_form; intros. destruct (ptr_offset op a1 n) as [[[tq sub] si] | ]; try discriminate.
  simpl in H. destruct a1; try discriminate. destruct (sps!i) as [s | ]; try discriminate.
  destruct (Z.eqb _ _); inv H; auto.
Qed.

Lemma index_compare_typeof: forall op a1 a2 a1' a2' ty e',
  index_compare ce sps nil op a1 a2 a1' a2' ty = Some e' -> typeof e' = ty.
Proof.
  unfold index_compare; intros.
  destruct (base_index sps nil a1') as [[[b1 t1] i1] | ]; try discriminate.
  destruct (base_index sps nil a2') as [[[b2 t2] i2] | ]; try discriminate.
  destruct (_ && _); try discriminate.
  destruct op; try discriminate;
  repeat match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] => destruct x; try discriminate
  end; inv H; auto.
Qed.

Lemma tr_expr_typeof: forall a, typeof (TR a) = typeof a.
Proof.
  unfold TR; intros. destruct a; simpl; auto.
  - destruct (sps!i); auto.
  - destruct (index_form ce sps nil b a1 (tr_expr ce sps nil nil a2) t) eqn:IF.
    + eapply index_form_typeof; eauto.
    + destruct (index_compare _ _ _ _ _ _ _ _ _) eqn:IC; auto. eapply index_compare_typeof; eauto.
Qed.

Lemma ptr_offset_typeof: forall op a n tq sub si,
  ptr_offset op a n = Some (tq, sub, si) -> tq = typeof a.
Proof.
  unfold ptr_offset; intros. destruct op; try discriminate;
  repeat match goal with
  | [ H: context[match ?x with _ => _ end] |- _ ] => destruct x; try discriminate
  end; inv H; auto.
Qed.

Lemma index_form_inv: forall op a1 n ty e',
  index_form ce sps nil op a1 n ty = Some e' ->
  exists q tq s sub si,
    a1 = Etempvar q tq /\ sps!q = Some s /\ ptr_offset op a1 n = Some (tq, sub, si)
    /\ elem_size ce tq = sp_size s
    /\ e' = Ebinop Oadd (base_of s) (index_expr s sub si n) ty.
Proof.
  unfold index_form; intros.
  destruct (ptr_offset op a1 n) as [[[tq sub] si] | ] eqn:PO; try discriminate.
  simpl in H. destruct a1; try discriminate. destruct (sps!i) as [s | ] eqn:S; try discriminate.
  destruct (Z.eqb (elem_size ce tq) (sp_size s)) eqn:Z; try discriminate. inv H.
  assert (tq = t) by (exact (ptr_offset_typeof _ _ _ _ _ _ PO)). subst tq.
  exists i, t, s, sub, si. split; [auto | split; [auto | split; [auto | split; [apply Z.eqb_eq; auto | auto]]]].
Qed.

Lemma bare_pointer: forall a,
  uses_ok sps a = true -> bare_split sps a = true -> exists t ta, typeof a = Tpointer t ta.
Proof.
  intros. destruct a; simpl in *; try discriminate.
  rewrite H0 in H. simpl in H. destruct t; try discriminate. eauto.
Qed.

Lemma tr_lv_expr: forall a,
  match a with Evar _ _ | Ederef _ _ | Efield _ _ _ => True | _ => False end ->
  TR a = tr_lv ce sps nil nil a.
Proof.
  unfold TR; intros. destruct a; try contradiction; reflexivity.
Qed.


Lemma ptr_offset_typeof_eq: forall op a n n',
  typeof n' = typeof n -> ptr_offset op a n' = ptr_offset op a n.
Proof.
  intros. unfold ptr_offset. rewrite H. auto.
Qed.

Lemma type_eqb_true: forall t u, type_eqb t u = true -> t = u.
Proof.
  unfold type_eqb; intros. destruct (type_eq t u); congruence.
Qed.

Lemma elem_size_one: forall t, elem_size ce t = 1 -> exists t' ta, t = Tpointer t' ta /\ sizeof ce t' = 1.
Proof.
  unfold elem_size, pointee; intros. destruct t; try discriminate. eauto.
Qed.

Lemma index_compare_inv: forall op a1 a2 a1' a2' ty e',
  index_compare ce sps nil op a1 a2 a1' a2' ty = Some e' ->
  exists b t ta i1 i2 t2 ta2 ty1 ty2,
    a1' = Ebinop Oadd (Etempvar b (Tpointer t ta)) i1 ty1 /\ a2' = Ebinop Oadd (Etempvar b (Tpointer t2 ta2)) i2 ty2
    /\ typeof i1 = tlong /\ typeof i2 = tlong /\ sizeof ce t = 1 /\ sizeof ce t2 = 1
    /\ e' = Ebinop op i1 i2 ty
    /\ ((op = Oeq \/ op = One) /\ classify_cmp (typeof a1) (typeof a2) = cmp_case_pp
        \/ op = Osub /\ exists tp, classify_sub (typeof a1) (typeof a2) = sub_case_pp tp /\ sizeof ce tp = 1).
Proof.
  unfold index_compare; intros.
  destruct (base_index sps nil a1') as [[[b1 t1] i1] | ] eqn:B1; try discriminate.
  destruct (base_index sps nil a2') as [[[b2 t2] i2] | ] eqn:B2; try discriminate.
  destruct (Pos.eqb b1 b2 && Z.eqb (elem_size ce t1) 1 && Z.eqb (elem_size ce t2) 1) eqn:C; try discriminate.
  apply andb_true_iff in C. destruct C as [C C3]. apply andb_true_iff in C. destruct C as [C1 C2].
  apply Pos.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3. subst b2.
  destruct (elem_size_one _ C2) as (t & ta & T1 & SZ). subst t1.
  destruct (elem_size_one _ C3) as (t' & ta' & T2 & SZ2). subst t2.
  unfold base_index in B1, B2.
  destruct a1'; try discriminate. destruct b; try discriminate. destruct a1'1; try discriminate.
  destruct (is_base sps nil i && type_eqb (typeof a1'2) tlong) eqn:K1; inv B1.
  destruct a2'; try discriminate. destruct b; try discriminate. destruct a2'1; try discriminate.
  destruct (is_base sps nil i && type_eqb (typeof a2'2) tlong) eqn:K2; inv B2.
  apply andb_true_iff in K1. apply andb_true_iff in K2. destruct K1 as [_ K1]. destruct K2 as [_ K2].
  apply type_eqb_true in K1. apply type_eqb_true in K2.
  destruct op; try discriminate.
  - destruct (classify_sub (typeof a1) (typeof a2)) as [ | tp | | ] eqn:CS; try discriminate.
    destruct (Z.eqb (sizeof ce tp) 1 && type_eqb ty tlong) eqn:K; inv H.
    apply andb_true_iff in K. destruct K as [K _]. apply Z.eqb_eq in K.
    do 9 eexists. repeat (split; [solve [eauto] | ]). right; split; eauto.
  - destruct (classify_cmp (typeof a1) (typeof a2)) eqn:CC; inv H.
    do 9 eexists. repeat (split; [solve [eauto] | ]). left; split; auto.
  - destruct (classify_cmp (typeof a1) (typeof a2)) eqn:CC; inv H.
    do 9 eexists. repeat (split; [solve [eauto] | ]). left; split; auto.
Qed.

Lemma tr_lv_typeof: forall a, typeof (tr_lv ce sps nil nil a) = typeof a.
Proof.
  intros. destruct a; reflexivity.
Qed.

Lemma eval_lvalue_shape: forall e le m a b ofs bf,
  eval_lvalue ge e le m a b ofs bf ->
  match a with Evar _ _ | Ederef _ _ | Efield _ _ _ => True | _ => False end.
Proof.
  intros. inv H; auto.
Qed.

Section MATCH.

Variable le tle: temp_env.
Hypothesis MT: match_temps le tle.

Lemma le_top: forall x v, le!x = Some v -> Ple x top.
Proof.
  intros. destruct (plt top x) as [LT | GE].
  - rewrite (mt_above _ _ MT x LT) in H. discriminate.
  - apply Pos.le_nlt. auto.
Qed.

(** A split temporary holding a pointer evaluates, in the target, to
    [base + idx] with the same value. *)
Lemma eval_split: forall e m x s v ty,
  sps!x = Some s -> le!x = Some v -> ptrish v ->
  eval_expr tge e tle m (value_of s ty) v.
Proof.
  intros. destruct (mt_split _ _ MT _ _ _ H H0 H1) as (b & i & B & I & AT).
  destruct (SHAPE _ _ H) as (t & ta & T & SZ).
  unfold value_of, base_of, idx_of. rewrite T. eapply eval_base_plus; eauto.
  rewrite CENV. fold ce. rewrite <- SZ. exact AT.
Qed.


(** In the target, [B + i] evaluates to [b + sz * i] for the value [b] of [B]. *)
Lemma eval_base_index_inv: forall e m b t ta i ty v,
  eval_expr tge e tle m (Ebinop Oadd (Etempvar b (Tpointer t ta)) i ty) v -> typeof i = tlong ->
  exists bv iv, tle!b = Some bv /\ eval_expr tge e tle m i (Vlong iv) /\ at_index (sizeof tge t) bv iv = Some v.
Proof.
  intros e m b t ta i ty v EV TI.
  inv EV; [ | match goal with H: eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end].
  match goal with H: eval_expr _ _ _ _ (Etempvar _ _) _ |- _ =>
    inv H; [ | match goal with H': eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inv H' end] end.
  match goal with H: sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ => rename H into SEM end.
  rewrite TI in SEM. simpl in SEM. unfold sem_add, classify_add in SEM. simpl in SEM.
  match goal with H: eval_expr _ _ _ _ i ?w |- _ => rename H into EI; destruct w as [ | n | n | f | f | b' o'] end;
  try (match goal with H: _ ! b = Some ?bv |- _ => destruct bv end; simpl in SEM; try rewrite ptr64 in SEM;
       discriminate).
  match goal with H: _ ! b = Some ?bv |- _ => exists bv, n; split; [exact H | split; auto] end.
  all: rewrite <- sem_add_ptr_long_at; auto.
Qed.

Lemma tr_expr_correct: forall e m,
  (forall a v, eval_expr ge e le m a v ->
     uses_ok sps a = true -> (bare_split sps a = true -> ptrish v) ->
     eval_expr tge e tle m (TR a) v)
  /\ (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
     uses_ok sps a = true ->
     eval_lvalue tge e tle m (tr_lv ce sps nil nil a) b ofs bf).
Proof.
  intros e m.
  apply (eval_expr_lvalue_ind ge e le m
    (fun a v => uses_ok sps a = true -> (bare_split sps a = true -> ptrish v) -> eval_expr tge e tle m (TR a) v)
    (fun a b ofs bf => uses_ok sps a = true -> eval_lvalue tge e tle m (tr_lv ce sps nil nil a) b ofs bf));
  unfold TR; intros; cbn [tr_expr tr_lv find_cache uses_ok bare_split] in *.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - (* temporary *)
    destruct (sps!id) as [s | ] eqn:S.
    + apply eval_split with id; auto.
    + constructor. rewrite (mt_same _ _ MT); eauto. eapply le_top; eauto.
  - (* &a *)
    constructor. auto.
  - (* unary *)
    econstructor. apply H0; auto. intros B.
    destruct (bare_pointer _ H2 B) as (t & ta & T). rewrite T in H1. eapply unop_ptr; eauto.
    fold (TR a). rewrite tr_expr_typeof. eauto.
  - (* binary *)
    apply andb_true_iff in H4. destruct H4 as [U1 U2].
    assert (T2: eval_expr tge e tle m (TR a2) v2).
    { apply H2; auto. intros B. destruct (bare_pointer _ U2 B) as (t & ta & T). rewrite T in H3.
      eapply binop_ptr_right; eauto. }
    assert (T1: eval_expr tge e tle m (TR a1) v1).
    { apply H0; auto. intros B. destruct (bare_pointer _ U1 B) as (t & ta & T). rewrite T in H3.
      eapply binop_ptr_left; eauto. }
    fold (TR a2). destruct (index_form ce sps nil op a1 (TR a2) ty) as [e' | ] eqn:IF.
    + (* [p + n], [p - n] on a split [p]: [base + (idx +/- n)] *)
      destruct (index_form_inv _ _ _ _ _ IF) as (q & tq & s & sub & si & A1 & S & PO & ES & E').
      subst a1 e'.
      assert (LQ: le!q = Some v1) by (inv H; [auto | inv H4]).
      simpl in U1. rewrite S in U1. simpl in U1. destruct tq as [ | | | | t ta | | | | ]; try discriminate.
      assert (P1: ptrish v1) by (eapply binop_ptr_left; eauto).
      destruct (mt_split _ _ MT _ _ _ S LQ P1) as (b & i & B & I & AT).
      destruct (SHAPE _ _ S) as (t' & ta' & T & SZ).
      simpl in ES. rewrite <- ES in AT.
      rewrite (ptr_offset_typeof_eq _ _ _ _ (tr_expr_typeof a2)) in PO.
      destruct (offset_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PO eq_refl H3 AT) as (c & AT' & SI).
      unfold index_expr, base_of, idx_of. rewrite T.
      destruct si as [si0 | ].
      * destruct SI as (n & sz & si' & a' & V2 & C & TY2). subst v2 c.
        eapply eval_base_plus_offset with (b := b) (i := i); eauto.
        eapply eval_widen_int; eauto. rewrite tr_expr_typeof; eauto.
        apply widen_typeof.
        rewrite CENV. fold ce. rewrite <- SZ, <- ES. auto.
      * destruct SI as (V2 & si' & a' & TY2). subst v2.
        eapply eval_base_plus_offset with (b := b) (i := i); eauto.
        simpl. rewrite tr_expr_typeof; eauto.
        rewrite CENV. fold ce. rewrite <- SZ, <- ES. auto.
    + fold (TR a1). destruct (index_compare ce sps nil op a1 a2 (TR a1) (TR a2) ty) as [e' | ] eqn:IC.
      * (* [p == q], [p != q], [p - q] on one base, 1-byte elements: on the indices *)
        destruct (index_compare_inv _ _ _ _ _ _ _ IC)
          as (b & t & ta & i1 & i2 & t2 & ta2 & ty1 & ty2 & A1 & A2 & TI1 & TI2 & SZ & SZ2 & E' & OP).
        subst e'. rewrite A1 in T1. rewrite A2 in T2.
        destruct (eval_base_index_inv _ _ _ _ _ _ _ _ T1 TI1) as (bv & iv1 & B1 & I1 & AT1).
        destruct (eval_base_index_inv _ _ _ _ _ _ _ _ T2 TI2) as (bv' & iv2 & B2 & I2 & AT2).
        rewrite B1 in B2. inv B2.
        rewrite CENV in AT1, AT2. fold ce in AT1, AT2. rewrite SZ in AT1. rewrite SZ2 in AT2.
        econstructor; eauto. rewrite TI1, TI2, CENV. fold ce.
        destruct OP as [[OP CC] | [OP (tp & CS & SZP)]].
        -- eapply cmp_index; eauto.
        -- subst op. eapply sub_index; eauto.
      * econstructor; eauto. rewrite !tr_expr_typeof, CENV. auto.
  - (* cast *)
    apply andb_true_iff in H2. destruct H2 as [U NV].
    econstructor. apply H0; auto. intros B.
    destruct (bare_pointer _ U B) as (t & ta & T). rewrite T in H1. eapply cast_ptr; eauto.
    intro V; subst ty. rewrite B in NV. discriminate.
    fold (TR a). rewrite tr_expr_typeof. eauto.
  - (* sizeof *)
    rewrite <- CENV. constructor.
  - (* alignof *)
    rewrite <- CENV. constructor.
  - (* an lvalue's value *)
    pose proof (eval_lvalue_shape _ _ _ _ _ _ _ H) as SH.
    fold (TR a). rewrite (tr_lv_expr a SH). eapply eval_Elvalue; eauto.
    rewrite tr_lv_typeof. eauto.
  - (* local variable *)
    constructor; auto.
  - (* global variable *)
    apply eval_Evar_global; auto. rewrite SYMB; auto.
  - (* *a *)
    constructor. apply H0; auto. simpl; auto.
  - (* struct field *)
    eapply eval_Efield_struct; eauto.
    apply H0; auto. intros; simpl; auto.
    fold (TR a). rewrite tr_expr_typeof; eauto.
    rewrite CENV; eauto.
    rewrite CENV; eauto.
  - (* union field *)
    eapply eval_Efield_union; eauto.
    apply H0; auto. intros; simpl; auto.
    fold (TR a). rewrite tr_expr_typeof; eauto.
    rewrite CENV; eauto.
    rewrite CENV; eauto.
Qed.

End MATCH.

End EXPRESSIONS.

(** ** Statements without caches

    With no caches ([cl = nil]), [tr_stmt] does not depend on the cache
    state: it is the structural translation [tr2]. *)

Scheme statement_ind2 := Induction for statement Sort Prop
  with labeled_statements_ind2 := Induction for labeled_statements Sort Prop.
Combined Scheme statement_lstmt_ind from statement_ind2, labeled_statements_ind2.

Lemma sseq_skip_l: forall s, sseq Sskip s = s.
Proof. auto. Qed.

Lemma sseq_skip_r: forall s, sseq s Sskip = s.
Proof. destruct s; auto. Qed.

Section TR2.

Variable ce: composite_env.
Variable sps: splits.
Variable nw: PTree.t unit.
Variable vars: list (ident * type).

Let TR := tr_expr ce sps nil nil.

Fixpoint tr2 (s: statement) : option statement :=
  match s with
  | Sset x e => tr_set ce sps nil nil x e
  | Sassign a e => Some (Sassign (tr_lv ce sps nil nil a) (TR e))
  | Scall optid a al => Some (with_result sps optid (fun dst => Scall dst (TR a) (map TR al)))
  | Sbuiltin optid ef tys al => Some (with_result sps optid (fun dst => Sbuiltin dst ef tys (map TR al)))
  | Ssequence s1 s2 =>
      match tr2 s1, tr2 s2 with Some t1, Some t2 => Some (Ssequence t1 t2) | _, _ => None end
  | Sifthenelse a s1 s2 =>
      match tr2 s1, tr2 s2 with Some t1, Some t2 => Some (Sifthenelse (TR a) t1 t2) | _, _ => None end
  | Sloop s1 s2 =>
      match tr2 s1, tr2 s2 with Some t1, Some t2 => Some (Sloop t1 t2) | _, _ => None end
  | Sreturn (Some a) => Some (Sreturn (Some (TR a)))
  | Sswitch a ls =>
      match tr2_l ls with Some tls => Some (Sswitch (TR a) tls) | None => None end
  | Slabel l s1 =>
      match tr2 s1 with Some t1 => Some (Slabel l t1) | None => None end
  | _ => Some s
  end
with tr2_l (ls: labeled_statements) : option labeled_statements :=
  match ls with
  | LSnil => Some LSnil
  | LScons c s ls' =>
      match tr2 s, tr2_l ls' with Some t, Some tl => Some (LScons c t tl) | _, _ => None end
  end.

Definition nil_state (st: cstate) : Prop := cs_valid st = nil /\ cs_copies st = nil.

Definition nil_out (o: option cstate) : Prop :=
  match o with Some st => nil_state st | None => True end.

Lemma nil_default: forall o, nil_out o -> nil_state (default_state o).
Proof.
  intros [st|]; simpl; auto. split; auto.
Qed.

Lemma nil_meet: forall a b, nil_state a -> nil_state b -> nil_state (meet a b).
Proof.
  unfold nil_state, meet; intros a b [A1 A2] [B1 B2]. simpl. rewrite A1, A2. auto.
Qed.

Lemma nil_meet_opt: forall a b, nil_out a -> nil_out b -> nil_out (meet_opt a b).
Proof.
  intros [a|] [b|]; simpl; auto. apply nil_meet.
Qed.

Lemma nil_reloads: forall s st, reloads ce sps nil s st = (Sskip, st).
Proof. reflexivity. Qed.

Lemma nil_result_resets: forall o, result_resets nil o = Sskip.
Proof. destruct o; reflexivity. Qed.

Lemma nil_valid_caches: forall st, valid_caches nil st = nil.
Proof. reflexivity. Qed.

Lemma nil_assign_temp: forall x st, nil_state st -> nil_state (assign_temp nil x st).
Proof.
  unfold nil_state, assign_temp, invalidate; intros x st [A B]. simpl. rewrite A, B. auto.
Qed.

Lemma nil_after_set: forall x e st, nil_state st -> nil_state (after_set ce nil x e st).
Proof.
  intros. unfold after_set.
  assert (copy_source ce nil st e = None).
  { unfold copy_source. simpl. destruct e; auto. }
  rewrite H0. apply nil_assign_temp; auto.
Qed.

Lemma nil_after_result: forall o st, nil_state st -> nil_state (after_result nil o st).
Proof.
  intros [x|] st H; simpl; auto. apply nil_assign_temp; auto.
Qed.

Lemma nil_invalidate: forall h st, nil_state st -> nil_state (invalidate nil h st).
Proof.
  unfold nil_state, invalidate; intros h st [A B]. simpl. rewrite A, B. auto.
Qed.

(** A successful [tr_loop] with cache-free parts: the parts it returns
    come from translations on cache-free states. *)
Lemma tr_loop_nil: forall (t1 t2: loop_part),
  (forall st ts n b c, nil_state st -> t1 st = Some (ts, (n, b, c)) -> nil_out n /\ nil_out b /\ nil_out c) ->
  (forall st ts n b c, nil_state st -> t2 st = Some (ts, (n, b, c)) -> nil_out n /\ nil_out b /\ nil_out c) ->
  forall fuel entry s1' s2' entry' o,
  nil_state entry ->
  tr_loop fuel t1 t2 entry = Some (s1', s2', entry', o) ->
  (exists e1 o1, nil_state e1 /\ t1 e1 = Some (s1', o1))
  /\ (exists e2 o2, nil_state e2 /\ t2 e2 = Some (s2', o2))
  /\ (let '(n, b, c) := o in nil_out n /\ nil_out b /\ nil_out c).
Proof.
  intros t1 t2 H1 H2. induction fuel; intros entry s1' s2' entry' o NE TL; simpl in TL;
  (destruct (t1 entry) as [[ts1 [[n1 b1] c1]] | ] eqn:T1; try discriminate;
   destruct (t2 (default_state (meet_opt n1 c1))) as [[ts2 [[n2 b2] c2]] | ] eqn:T2; try discriminate;
   destruct (H1 _ _ _ _ _ NE T1) as (N1 & B1 & C1);
   assert (NE2: nil_state (default_state (meet_opt n1 c1))) by (apply nil_default; apply nil_meet_opt; auto);
   destruct (H2 _ _ _ _ _ NE2 T2) as (N2 & B2 & C2)).
  - destruct (same_state _ _); inv TL. split; [eauto | split; [eauto | ]].
    split; [apply nil_meet_opt; auto | split; exact I].
  - destruct (same_state _ _).
    + inv TL. split; [eauto | split; [eauto | ]].
      split; [apply nil_meet_opt; auto | split; exact I].
    + assert (NE': nil_state (match meet_opt n2 c2 with Some back => meet entry back | None => entry end)).
      { destruct (meet_opt n2 c2) as [back | ] eqn:M; auto.
        apply nil_meet; auto. pose proof (nil_meet_opt _ _ N2 C2) as NB. rewrite M in NB. exact NB. }
      exact (IHfuel _ _ _ _ _ NE' TL).
Qed.


Lemma tr_stmt_switch_nil: forall st a ls,
  tr_stmt ce sps nil nw vars st (Sswitch a ls) =
  match tr_lstmt ce sps nil nw vars st None ls with
  | Some (ls', (n, b, c)) =>
      Some (Sswitch (tr_expr ce sps nil nil a) ls', (meet_opt (meet_opt n b) (Some st), None, c))
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma tr_lstmt_cons: forall st prev c s ls,
  tr_lstmt ce sps nil nw vars st prev (LScons c s ls) =
  match tr_stmt ce sps nil nw vars (default_state (meet_opt prev (Some st))) s with
  | Some (s', (n, b, k)) =>
      match tr_lstmt ce sps nil nw vars st n ls with
      | Some (ls'', (n', b', k')) => Some (LScons c s' ls'', (n', meet_opt b b', meet_opt k k'))
      | None => None
      end
  | None => None
  end.
Proof. reflexivity. Qed.

Ltac fin := refine (conj _ (conj _ (conj _ _))); try exact I; auto.

Lemma tr_stmt_nil:
  (forall s st ts n b c, nil_state st ->
     tr_stmt ce sps nil nw vars st s = Some (ts, (n, b, c)) ->
     tr2 s = Some ts /\ nil_out n /\ nil_out b /\ nil_out c)
  /\ (forall ls st prev tls n b c, nil_state st -> nil_out prev ->
     tr_lstmt ce sps nil nw vars st prev ls = Some (tls, (n, b, c)) ->
     tr2_l ls = Some tls /\ nil_out n /\ nil_out b /\ nil_out c).
Proof.
  apply statement_lstmt_ind; intros;
  try (rewrite tr_stmt_switch_nil in *); try (rewrite tr_lstmt_cons in *);
  cbn [tr_stmt tr_lstmt tr2 tr2_l reloads valid_caches filter fold_left fold_right resets nil_out] in *.
  - (* skip *) inv H0. fin.
  - (* assign *) inv H0. fin. apply nil_invalidate; auto.
  - (* set *)
    destruct (tr_set ce sps nil nil i e) as [s' | ] eqn:TS; inv H0.
    rewrite ?sseq_skip_l, ?sseq_skip_r. fin. apply nil_after_set; auto.
  - (* call *)
    inv H0. rewrite nil_result_resets, ?sseq_skip_l, ?sseq_skip_r. fin.
    apply nil_after_result. destruct (call_keeps_memory nw vars e); auto. apply nil_invalidate; auto.
  - (* builtin *)
    inv H0. rewrite nil_result_resets, ?sseq_skip_l, ?sseq_skip_r. fin.
    apply nil_after_result. destruct (ef_keeps_memory e); auto. apply nil_invalidate; auto.
  - (* sequence *)
    destruct (tr_stmt ce sps nil nw vars st s) as [[ts1 [[n1 b1] c1]] | ] eqn:T1; try discriminate.
    destruct (tr_stmt ce sps nil nw vars (default_state n1) s0) as [[ts2 [[n2 b2] c2]] | ] eqn:T2; try discriminate.
    inv H2. destruct (H _ _ _ _ _ H1 T1) as (E1 & N1 & B1 & C1).
    destruct (H0 _ _ _ _ _ (nil_default _ N1) T2) as (E2 & N2 & B2 & C2).
    rewrite E1, E2. fin; apply nil_meet_opt; auto.
  - (* if *)
    destruct (tr_stmt ce sps nil nw vars st s) as [[ts1 [[n1 b1] c1]] | ] eqn:T1; try discriminate.
    destruct (tr_stmt ce sps nil nw vars st s0) as [[ts2 [[n2 b2] c2]] | ] eqn:T2; try discriminate.
    inv H2. destruct (H _ _ _ _ _ H1 T1) as (E1 & N1 & B1 & C1).
    destruct (H0 _ _ _ _ _ H1 T2) as (E2 & N2 & B2 & C2).
    rewrite E1, E2. rewrite ?sseq_skip_l, ?sseq_skip_r. fin; apply nil_meet_opt; auto.
  - (* loop *)
    destruct (tr_loop _ _ _ _) as [[[[s1' s2'] entry] o] | ] eqn:TL; try discriminate.
    inv H2.
    exploit (tr_loop_nil (fun e => tr_stmt ce sps nil nw vars e s) (fun e => tr_stmt ce sps nil nw vars e s0)).
    { intros. destruct (H _ _ _ _ _ H2 H3) as (A & B & C & D). auto. }
    { intros. destruct (H0 _ _ _ _ _ H2 H3) as (A & B & C & D). auto. }
    exact H1. exact TL.
    intros ((e1 & [[n1 b1] c1] & NE1 & T1) & (e2 & [[n2 b2] c2] & NE2 & T2) & O).
    destruct (H _ _ _ _ _ NE1 T1) as (E1 & _). destruct (H0 _ _ _ _ _ NE2 T2) as (E2 & _).
    rewrite E1, E2. rewrite ?sseq_skip_l. simpl in O. destruct O as (C1 & C2 & C3). fin.
  - (* break *) inv H0. fin.
  - (* continue *) inv H0. fin.
  - (* return *) destruct o; inv H0; rewrite ?sseq_skip_l; fin.
  - (* switch *)
    destruct (tr_lstmt ce sps nil nw vars st None l) as [[tls [[n1 b1] c1]] | ] eqn:TL; try discriminate.
    inv H1. destruct (H st None _ _ _ _ H0 I TL) as (E & N1 & B1 & C1).
    rewrite E. rewrite ?sseq_skip_l, ?sseq_skip_r. fin.
    apply nil_meet_opt; auto. apply nil_meet_opt; auto.
  - (* label *)
    destruct (tr_stmt ce sps nil nw vars empty_state s) as [[ts1 [[n1 b1] c1]] | ] eqn:T1; try discriminate.
    inv H1. destruct (H empty_state _ _ _ _ (conj eq_refl eq_refl) T1) as (E & N1 & B1 & C1).
    rewrite E. fin.
  - (* goto *) inv H0. fin.
  - (* LSnil *) inv H1. fin.
  - (* LScons *)
    destruct (tr_stmt ce sps nil nw vars (default_state (meet_opt prev (Some st))) s) as [[ts1 [[n1 b1] c1]] | ] eqn:T1;
      try discriminate.
    destruct (tr_lstmt ce sps nil nw vars st n1 l) as [[tl [[n2 b2] c2]] | ] eqn:T2; try discriminate.
    inv H3.
    destruct (H _ _ _ _ _ (nil_default _ (nil_meet_opt prev (Some st) H2 H1)) T1) as (E1 & N1 & B1 & C1).
    destruct (H0 _ _ _ _ _ _ H1 N1 T2) as (E2 & N2 & B2 & C2).
    rewrite E1, E2. fin; apply nil_meet_opt; auto.
Qed.

End TR2.

(** ** What the checks of [plan_ok] give *)

Lemma norepet_map_inj: forall (A B: Type) (f: A -> B) l a b,
  list_norepet (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  induction l; simpl; intros. contradiction.
  inv H. destruct H0; destruct H1; subst; auto.
  - elim H5. rewrite H2. apply in_map; auto.
  - elim H5. rewrite <- H2. apply in_map; auto.
Qed.

Lemma norepet_b_true: forall l, norepet_b l = true -> list_norepet l.
Proof.
  unfold norepet_b; intros. destruct (list_norepet_dec ident_eq l); [auto | discriminate].
Qed.

Lemma disjoint_b_true: forall l1 l2 x, disjoint_b l1 l2 = true -> In x l1 -> ~ In x l2.
Proof.
  unfold disjoint_b; intros. rewrite forallb_forall in H. specialize (H x H0).
  apply negb_true_iff in H. intro IN. assert (existsb (Pos.eqb x) l2 = true).
  { apply existsb_exists. exists x; split; auto. apply Pos.eqb_refl. }
  congruence.
Qed.

Record splits_ok (ce: composite_env) (sps: splits) (top: positive) : Prop := {
  so_shape: forall x s, sps!x = Some s -> exists t ta, sp_type s = Tpointer t ta /\ sp_size s = sizeof ce t;
  so_src: forall x s, sps!x = Some s -> Ple x top;
  so_base: forall x s, sps!x = Some s -> Plt top (sp_base s);
  so_idx: forall x s, sps!x = Some s -> Plt top (sp_idx s);
  so_idx_inj: forall x y s1 s2, sps!x = Some s1 -> sps!y = Some s2 -> sp_idx s1 = sp_idx s2 -> x = y;
  so_idx_base: forall x y s1 s2, sps!x = Some s1 -> sps!y = Some s2 -> sp_idx s1 <> sp_base s2
}.

Lemma plan_ok_splits: forall ce sps share labs f tf,
  plan_ok ce sps share labs nil f tf = true -> splits_ok ce sps (max_function f).
Proof.
  unfold plan_ok; intros. rewrite ! andb_true_iff in H.
  destruct H as [[[[[[[[[W F] NO] DJ] NB] SH] DECL] OTH] NR] OK].
  rewrite app_nil_r in NO, DJ. simpl in F. rewrite app_nil_r in F.
  apply norepet_b_true in NO.
  rewrite forallb_forall in W, F.
  assert (IN: forall x s, sps!x = Some s -> In (x, s) (PTree.elements sps)) by (intros; apply PTree.elements_correct; auto).
  constructor; intros.
  - specialize (W _ (IN _ _ H)). simpl in W. apply andb_true_iff in W. destruct W as [W _].
    unfold split_wf in W. destruct (sp_type s) as [ | | | | t ta | | | | ]; try discriminate.
    exists t, ta; split; auto. apply Z.eqb_eq; auto.
  - specialize (W _ (IN _ _ H)). simpl in W. apply andb_true_iff in W. destruct W as [_ W].
    apply Pos.leb_le; auto.
  - apply Pos.ltb_lt. apply F. apply in_app_iff. left.
    change (sp_base s) with ((fun xs : ident * split => sp_base (snd xs)) (x, s)). apply in_map; auto.
  - apply Pos.ltb_lt. apply F. apply in_app_iff. right.
    change (sp_idx s) with ((fun xs : ident * split => sp_idx (snd xs)) (x, s)). apply in_map; auto.
  - exploit (norepet_map_inj _ _ (fun xs : ident * split => sp_idx (snd xs)) (PTree.elements sps) (x, s1) (y, s2));
      eauto. intros E; inv E; auto.
  - intro E. eapply (disjoint_b_true _ _ (sp_idx s1) DJ).
    change (sp_idx s1) with ((fun xs : ident * split => sp_idx (snd xs)) (x, s1)). apply in_map; auto.
    rewrite E. change (sp_base s2) with ((fun xs : ident * split => sp_base (snd xs)) (y, s2)). apply in_map; auto.
Qed.

(** ** With nothing split, the translation is the identity *)

Section NOSPLIT.

Variable ce: composite_env.
Variable sps: splits.
Hypothesis NONE: forall x, sps!x = None.

Lemma nosplit_elements: PTree.elements sps = nil.
Proof.
  destruct (PTree.elements sps) as [ | [x s] l] eqn:E; auto.
  assert (In (x, s) (PTree.elements sps)) by (rewrite E; left; auto).
  apply PTree.elements_complete in H. rewrite NONE in H. discriminate.
Qed.

Lemma nosplit_is_base: forall b, is_base sps nil b = false.
Proof.
  intros. unfold is_base. rewrite nosplit_elements. auto.
Qed.

Lemma nosplit_tr_expr: forall a, tr_expr ce sps nil nil a = a.
Proof.
  induction a; simpl; auto.
  - (* tempvar *) rewrite NONE; auto.
  - (* deref *) rewrite IHa; auto.
  - (* addrof *) f_equal. destruct a; simpl in *; auto; congruence.
  - (* unop *) rewrite IHa; auto.
  - (* binop *)
    rewrite IHa2.
    assert (IF: index_form ce sps nil b a1 a2 t = None).
    { unfold index_form. destruct (ptr_offset b a1 a2) as [[[tq sub] si] | ]; auto. simpl.
      destruct a1; auto. rewrite NONE; auto. }
    rewrite IF, IHa1.
    assert (IC: index_compare ce sps nil b a1 a2 a1 a2 t = None).
    { unfold index_compare, base_index.
      destruct a1; auto. destruct b0; auto. destruct a1_1; auto. rewrite nosplit_is_base. auto. }
    rewrite IC. auto.
  - (* cast *) rewrite IHa; auto.
  - (* field *) rewrite IHa; auto.
Qed.

Lemma nosplit_tr_lv: forall a, tr_lv ce sps nil nil a = a.
Proof.
  destruct a; simpl; auto; rewrite nosplit_tr_expr; auto.
Qed.

Lemma nosplit_map: forall al, map (tr_expr ce sps nil nil) al = al.
Proof.
  induction al; simpl; auto. rewrite nosplit_tr_expr, IHal; auto.
Qed.

Lemma nosplit_with_result: forall o mk, with_result sps o mk = mk o.
Proof.
  destruct o; simpl; auto. rewrite NONE; auto.
Qed.

Lemma nosplit_tr2:
  (forall s, tr2 ce sps s = Some s) /\ (forall ls, tr2_l ce sps ls = Some ls).
Proof.
  apply statement_lstmt_ind; intros; simpl;
  rewrite ?nosplit_tr_expr, ?nosplit_tr_lv, ?nosplit_map, ?nosplit_with_result; auto;
  try (rewrite H, H0; auto); try (rewrite H; auto).
  - unfold tr_set. rewrite NONE. destruct e; rewrite ?NONE, ?nosplit_tr_expr; auto.
  - destruct o; auto. rewrite nosplit_tr_expr; auto.
Qed.

Lemma nosplit_uses_ok: forall a, uses_ok sps a = true.
Proof.
  induction a; simpl; auto; try rewrite IHa; try rewrite IHa1, IHa2; auto.
  - rewrite NONE; auto.
  - unfold bare_split. destruct a; auto. rewrite NONE; auto.
Qed.

Lemma nosplit_received_ok: forall a ty, received_ok sps a ty = true.
Proof.
  intros. unfold received_ok, bare_split. rewrite nosplit_uses_ok. destruct a; auto. rewrite NONE; auto.
Qed.

Lemma nosplit_args_ok: forall al tys, args_ok sps al tys = true.
Proof.
  induction al; destruct tys; simpl; auto.
  - rewrite nosplit_uses_ok, IHal. auto.
  - rewrite nosplit_received_ok, IHal; auto.
Qed.

Lemma nosplit_body_ok: forall ret,
  (forall s, body_ok sps ret s = true) /\ (forall ls, body_ok_l sps ret ls = true).
Proof.
  intros. apply statement_lstmt_ind; intros; simpl;
  rewrite ?nosplit_uses_ok, ?nosplit_received_ok, ?nosplit_args_ok; auto;
  try (rewrite H, H0; auto); try (rewrite H; auto).
  - unfold copy_ok. destruct e; auto. rewrite NONE; auto.
  - unfold call_args_ok. destruct (classify_fun (typeof e)); simpl.
    + apply nosplit_args_ok.
    + apply forallb_forall. intros; apply nosplit_uses_ok.
  - destruct o; auto. apply nosplit_received_ok.
Qed.

Lemma nosplit_entry: forall params, entry_code sps params = Sskip.
Proof.
  induction params as [ | [x t] params IH]; simpl; auto. rewrite NONE; auto.
Qed.

End NOSPLIT.

(** ** One function and its translation *)

Definition lfuel (sps: splits) : nat := S (length (PTree.elements sps)).

Definition LC (ce: composite_env) (sps: splits) (labs: PTree.t lset) (s: statement) (after brk cont: lset) :=
  lcheck ce sps (shared_tree sps) labs (lfuel sps) s after brk cont.

Definition LCL (ce: composite_env) (sps: splits) (labs: PTree.t lset) (ls: labeled_statements) (after cont: lset) :=
  lcheck_l ce sps (shared_tree sps) labs (lfuel sps) ls after cont.

Lemma lcheck_switch_eq: forall ce sps sh labs fuel c ls after brk cont,
  lcheck ce sps sh labs fuel (Sswitch c ls) after brk cont =
  let '(_, all, ok) := lcheck_l ce sps sh labs fuel ls after cont in (lu sh c (lunion all after), ok).
Proof. reflexivity. Qed.

Lemma lcheck_lcons_eq: forall ce sps sh labs fuel c s ls after cont,
  lcheck_l ce sps sh labs fuel (LScons c s ls) after cont =
  let '(lr, all, ok') := lcheck_l ce sps sh labs fuel ls after cont in
  let '(l, ok) := lcheck ce sps sh labs fuel s lr after cont in
  (l, lunion l all, ok && ok').
Proof. reflexivity. Qed.

Section NOSPLIT_LIVE.

Variable ce: composite_env.
Variable sps: splits.
Hypothesis NONE: forall x, sps!x = None.

Lemma nosplit_tracked: forall x, tracked (shared_tree sps) x = false.
Proof.
  intros. unfold tracked, shared_tree. rewrite PTree.gmap, NONE. auto.
Qed.

Lemma nosplit_lu: forall e s, lu (shared_tree sps) e s = s.
Proof.
  induction e; intros; simpl; auto. rewrite nosplit_tracked; auto. rewrite IHe2, IHe1; auto.
Qed.

Lemma nosplit_lus: forall al s, fold_right (lu (shared_tree sps)) s al = s.
Proof.
  induction al; intros; simpl; auto. rewrite IHal, nosplit_lu; auto.
Qed.

(** With nothing split, every live set is empty and every check holds. *)
Lemma nosplit_lcheck: forall fuel,
  (forall s, lcheck ce sps (shared_tree sps) (PTree.empty lset) fuel s nil nil nil = (nil, true))
  /\ (forall ls, lcheck_l ce sps (shared_tree sps) (PTree.empty lset) fuel ls nil nil = (nil, nil, true)).
Proof.
  intros fuel. apply statement_lstmt_ind; intros;
  try rewrite lcheck_switch_eq; try rewrite lcheck_lcons_eq; cbn [lcheck lcheck_l];
  try (destruct fuel; cbn [lcheck]);
  repeat (first [ match goal with H: _ = (nil, true) |- _ => rewrite H; clear H
                                | H: _ = (nil, nil, true) |- _ => rewrite H; clear H end
                | progress cbn iota beta ]);
  unfold result_ok; repeat match goal with o: option _ |- _ => destruct o end;
  rewrite ?NONE, ?nosplit_lu, ?nosplit_lus; auto.
Qed.

End NOSPLIT_LIVE.

Lemma var_names_cons: forall x t (l: list (ident * type)), var_names ((x, t) :: l) = x :: var_names l.
Proof. reflexivity. Qed.

(** The bases of split parameters are distinct ([share_ok]). *)
Lemma pbases_inj: forall sps l p q sp sq,
  list_norepet (flat_map (fun (pt: ident * type) =>
                  match sps!(fst pt) with Some sp => sp_base sp :: nil | None => nil end) l) ->
  In p (var_names l) -> In q (var_names l) -> sps!p = Some sp -> sps!q = Some sq ->
  sp_base sp = sp_base sq -> p = q.
Proof.
  induction l as [ | [x t] l IH]; intros p q sp sq NR P Q SP SQ E. contradiction.
  assert (INB: forall y sy, In y (var_names l) -> sps!y = Some sy ->
            In (sp_base sy) (flat_map (fun (pt: ident * type) =>
                  match sps!(fst pt) with Some sp => sp_base sp :: nil | None => nil end) l)).
  { intros. apply in_flat_map. unfold var_names in H. rewrite in_map_iff in H.
    destruct H as ((y' & t') & E' & IN). simpl in E'. subst y'. exists (y, t'). simpl. rewrite H0. split; simpl; auto. }
  simpl in NR. rewrite var_names_cons in P, Q.
  destruct (peq p q); auto.
  destruct P as [P | P]; destruct Q as [Q | Q]; subst.
  - congruence.
  - rewrite SP in NR. simpl in NR. inv NR. elim H1. rewrite E. eapply INB; eauto.
  - rewrite SQ in NR. simpl in NR. inv NR. elim H1. rewrite <- E. eapply INB; eauto.
  - destruct (sps!x); [simpl in NR; inv NR | ]; eapply IH; eauto.
Qed.

Record tr_function (ce: composite_env) (sps: splits) (labs: PTree.t lset) (f tf: function) : Prop := {
  tf_splits: splits_ok ce sps (max_function f);
  tf_params: fn_params tf = fn_params f;
  tf_vars: fn_vars tf = fn_vars f;
  tf_return: fn_return tf = fn_return f;
  tf_callconv: fn_callconv tf = fn_callconv f;
  tf_body: exists body', tr2 ce sps (fn_body f) = Some body' /\ fn_body tf = sseq (entry_code sps (fn_params f)) body';
  tf_ok: body_ok sps (fn_return f) (fn_body f) = true;
  tf_temps_src: forall x, Ple x (max_function f) -> sps!x = None ->
                (In x (var_names (fn_temps tf)) <-> In x (var_names (fn_temps f)));
  tf_temps_new: forall x s, sps!x = Some s ->
                In (sp_base s) (var_names (fn_temps tf)) /\ In (sp_idx s) (var_names (fn_temps tf));
  tf_temps_other: forall y, In y (var_names (fn_temps tf)) ->
                  Plt (max_function f) y \/ In y (var_names (fn_temps f));
  tf_entry: list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)) ->
            list_disjoint (var_names (fn_params tf)) (var_names (fn_temps tf));
  tf_live: snd (LC ce sps labs (fn_body f) nil nil nil) = true;
  tf_pbases: forall p q sp sq, In p (var_names (fn_params f)) -> In q (var_names (fn_params f)) ->
             sps!p = Some sp -> sps!q = Some sq -> sp_base sp = sp_base sq -> p = q
}.

Lemma tr_function_same: forall ce sps f,
  (forall x, sps!x = None) -> tr_function ce sps (PTree.empty lset) f f.
Proof.
  intros. constructor; intros; auto;
  match goal with
  | |- splits_ok _ _ _ => constructor; intros; rewrite H in *; discriminate
  | |- exists body', _ =>
      exists (fn_body f); split; [apply (proj1 (nosplit_tr2 ce sps H)) | rewrite nosplit_entry; auto]
  | |- body_ok _ _ _ = true => apply (proj1 (nosplit_body_ok sps H (fn_return f)))
  | |- snd (LC _ _ _ _ _ _ _) = true => unfold LC; rewrite (proj1 (nosplit_lcheck ce sps H _)); auto
  | |- _ <-> _ => tauto
  | H0: sps ! _ = Some _ |- _ => rewrite H in H0; discriminate
  | |- _ \/ _ => right; auto
  end.
Qed.

Lemma var_names_filter: forall (p: ident * type -> bool) l x,
  In x (var_names (List.filter p l)) -> In x (var_names l).
Proof.
  unfold var_names; intros. rewrite in_map_iff in H. destruct H as ((y & t) & E & IN). simpl in E. subst.
  apply filter_In in IN. destruct IN. change x with (fst (x, t)). apply in_map; auto.
Qed.

Lemma transf_function_tr: forall ce nw share f next tf sps' cl fb n,
  transf_function ce nw share false f next = (tf, sps', cl, fb, n) ->
  exists sps labs, tr_function ce sps labs f tf.
Proof.
  unfold transf_function; intros.
  destruct (plan_function ce share f next) as [[sps labs] next1] eqn:PF. simpl in H.
  destruct (PTree.elements sps) as [ | e0 l0] eqn:EL.
  - (* nothing to split *)
    injection H as E1 _ _ _ _. subst tf. exists sps, (PTree.empty lset). apply tr_function_same. intros x.
    destruct (sps!x) as [s|] eqn:S; auto.
    apply PTree.elements_correct in S. rewrite EL in S. contradiction.
  - destruct (tr_stmt ce sps nil nw (fn_vars f) empty_state (fn_body f)) as [[body' [[on ob] oc]] | ] eqn:TS.
    + match type of H with context[plan_ok ?a ?b ?c ?d ?e ?g ?h] => destruct (plan_ok a b c d e g h) eqn:OK end;
      cbv beta iota in H; injection H as E1 _ _ _ _; subst tf.
      * (* rewritten *)
        exists sps, labs. pose proof OK as OK'. unfold plan_ok in OK'. rewrite ! andb_true_iff in OK'.
        destruct OK' as [[[[[[[[[W F] NO] DJ] NB] SH] DECL] OTH] NR] BODY].
        unfold share_ok in SH. apply andb_true_iff in SH. destruct SH as [PB LV].
        constructor; auto.
        { eapply plan_ok_splits; eauto. }
        { destruct (proj1 (tr_stmt_nil ce sps nw (fn_vars f)) (fn_body f) empty_state _ _ _ _ (conj eq_refl eq_refl) TS) as (E & _).
          exists body'. split; auto. }
        { (* temporaries of f kept *)
          intros x LE S. split.
          - intros IN. rewrite forallb_forall in OTH. specialize (OTH x IN).
            apply orb_true_iff in OTH. destruct OTH as [LT | EX].
            + apply Pos.ltb_lt in LT. exfalso. eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto.
            + apply existsb_exists in EX. destruct EX as (y & IN' & EQ). apply Pos.eqb_eq in EQ. subst; auto.
          - intros IN. simpl. unfold var_names in *. rewrite map_app, in_app_iff. left.
            rewrite in_map_iff in IN. destruct IN as ((y & t) & E & IN). simpl in E. subst y.
            change x with (fst (x, t)). apply in_map. apply filter_In. split; auto. simpl. rewrite S; auto. }
        { (* new temporaries declared *)
          intros x s S. rewrite forallb_forall in DECL.
          assert (IN: In (x, s) (PTree.elements sps)) by (apply PTree.elements_correct; auto).
          split.
          - specialize (DECL (sp_base s)). exploit DECL.
            apply in_app_iff. left. change (sp_base s) with ((fun xs : ident * split => sp_base (snd xs)) (x, s)).
            apply in_map; auto.
            intros EX. apply existsb_exists in EX. destruct EX as (y & IN' & EQ). apply Pos.eqb_eq in EQ. subst; auto.
          - specialize (DECL (sp_idx s)). exploit DECL.
            apply in_app_iff. right. rewrite app_nil_r.
            change (sp_idx s) with ((fun xs : ident * split => sp_idx (snd xs)) (x, s)). apply in_map; auto.
            intros EX. apply existsb_exists in EX. destruct EX as (y & IN' & EQ). apply Pos.eqb_eq in EQ. subst; auto. }
        { (* every temporary is new or one of f's *)
          intros y IN. rewrite forallb_forall in OTH. specialize (OTH y IN).
          apply orb_true_iff in OTH. destruct OTH as [LT | EX].
          - left. apply Pos.ltb_lt; auto.
          - right. apply existsb_exists in EX. destruct EX as (z & IN' & EQ). apply Pos.eqb_eq in EQ. subst; auto. }
        { (* entry *)
          intros _. apply norepet_b_true in NR. unfold var_names in NR. rewrite map_app in NR.
          apply list_norepet_app in NR. destruct NR as (_ & _ & D). exact D. }
        { intros. eapply pbases_inj; eauto. apply norepet_b_true; auto. }
      * (* a check failed *)
        exists (PTree.empty split), (PTree.empty lset). apply tr_function_same. intros; apply PTree.gempty.
    + injection H as E1 _ _ _ _; subst tf. exists (PTree.empty split), (PTree.empty lset). apply tr_function_same.
      intros; apply PTree.gempty.
Qed.

(** ** Identifiers of a statement are at most [top] *)

Lemma max_expr_ge: forall a m, Ple m (max_expr a m).
Proof.
  induction a; intros; simpl; try apply Ple_refl; try apply Pos.le_max_r; auto.
  - eapply Ple_trans; [apply IHa2 | apply IHa1].
  - eapply Ple_trans; [ | apply IHa]. apply Pos.le_max_r.
Qed.

Lemma max_expr_mono: forall a m1 m2, Ple m1 m2 -> Ple (max_expr a m1) (max_expr a m2).
Proof.
  induction a; intros; simpl; auto; try (apply Pos.max_le_compat_l; auto).
  - apply IHa. apply Pos.max_le_compat_l; auto.
Qed.

Lemma max_exprs_ge: forall al m, Ple m (fold_right max_expr m al).
Proof.
  induction al; simpl; intros. apply Ple_refl. eapply Ple_trans; [apply IHal | apply max_expr_ge].
Qed.

Lemma max_exprs_mono: forall al m1 m2, Ple m1 m2 -> Ple (fold_right max_expr m1 al) (fold_right max_expr m2 al).
Proof.
  induction al; simpl; intros; auto. apply max_expr_mono; auto.
Qed.

Lemma max_stmt_ge:
  (forall s m, Ple m (max_stmt s m)) /\ (forall ls m, Ple m (max_lstmt ls m)).
Proof.
  apply statement_lstmt_ind; intros; simpl; try apply Ple_refl.
  - eapply Ple_trans; [apply max_expr_ge | apply max_expr_ge].
  - eapply Ple_trans; [ | apply max_expr_ge]. apply Pos.le_max_r.
  - destruct o; simpl.
    + eapply Ple_trans; [ | apply Pos.le_max_r]. eapply Ple_trans; [apply max_exprs_ge | apply max_expr_ge].
    + eapply Ple_trans; [apply max_exprs_ge | apply max_expr_ge].
  - destruct o; simpl.
    + eapply Ple_trans; [ | apply Pos.le_max_r]. apply max_exprs_ge.
    + apply max_exprs_ge.
  - eapply Ple_trans; [apply H0 | apply H].
  - eapply Ple_trans; [ | apply max_expr_ge]. eapply Ple_trans; [apply H0 | apply H].
  - eapply Ple_trans; [apply H0 | apply H].
  - destruct o; simpl; [apply max_expr_ge | apply Ple_refl].
  - eapply Ple_trans; [ | apply max_expr_ge]. apply H.
  - eapply Ple_trans; [ | apply H]. apply Pos.le_max_r.
  - apply Pos.le_max_r.
  - eapply Ple_trans; [apply H0 | apply H].
Qed.

Lemma max_stmt_mono:
  (forall s m1 m2, Ple m1 m2 -> Ple (max_stmt s m1) (max_stmt s m2))
  /\ (forall ls m1 m2, Ple m1 m2 -> Ple (max_lstmt ls m1) (max_lstmt ls m2)).
Proof.
  apply statement_lstmt_ind; intros; cbn [max_stmt max_lstmt fold_right];
  try (match goal with o: option _ |- _ => destruct o; cbn [max_opt] end);
  repeat (first [assumption | apply max_expr_mono | apply max_exprs_mono | apply Pos.max_le_compat_l
                | match goal with H: forall m1 m2, Ple m1 m2 -> _ |- _ => apply H end]).
Qed.

(** Every identifier of an expression or statement is at most [p]. *)
Fixpoint expr_le (p: positive) (a: expr) : Prop :=
  match a with
  | Evar x _ | Etempvar x _ => Ple x p
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ => expr_le p a
  | Efield a f _ => Ple f p /\ expr_le p a
  | Ebinop _ a1 a2 _ => expr_le p a1 /\ expr_le p a2
  | _ => True
  end.

Definition opt_le (p: positive) (o: option ident) : Prop :=
  match o with Some x => Ple x p | None => True end.

Fixpoint stmt_le (p: positive) (s: statement) : Prop :=
  match s with
  | Sassign a1 a2 => expr_le p a1 /\ expr_le p a2
  | Sset x a => Ple x p /\ expr_le p a
  | Scall o a al => opt_le p o /\ expr_le p a /\ Forall (expr_le p) al
  | Sbuiltin o _ _ al => opt_le p o /\ Forall (expr_le p) al
  | Ssequence s1 s2 | Sloop s1 s2 => stmt_le p s1 /\ stmt_le p s2
  | Sifthenelse a s1 s2 => expr_le p a /\ stmt_le p s1 /\ stmt_le p s2
  | Sreturn (Some a) => expr_le p a
  | Sswitch a ls => expr_le p a /\ lstmt_le p ls
  | Slabel l s1 => Ple l p /\ stmt_le p s1
  | Sgoto l => Ple l p
  | _ => True
  end
with lstmt_le (p: positive) (ls: labeled_statements) : Prop :=
  match ls with
  | LSnil => True
  | LScons _ s ls' => stmt_le p s /\ lstmt_le p ls'
  end.

Lemma Ple_max_iff: forall a b c, Ple (Pos.max a b) c <-> Ple a c /\ Ple b c.
Proof.
  intros. unfold Ple. apply Pos.max_lub_iff.
Qed.

Lemma max_expr_le: forall a m p, Ple (max_expr a m) p <-> expr_le p a /\ Ple m p.
Proof.
  induction a; intros; cbn [max_expr expr_le];
  repeat (first [rewrite IHa | rewrite IHa1 | rewrite IHa2 | rewrite Ple_max_iff]); tauto.
Qed.

Lemma max_exprs_le: forall al m p, Ple (fold_right max_expr m al) p <-> Forall (expr_le p) al /\ Ple m p.
Proof.
  induction al; intros; simpl.
  - split; [intros; split; auto | tauto].
  - rewrite max_expr_le, IHal. split.
    + intros [A [B C]]. split; auto.
    + intros [A C]. inv A. auto.
Qed.

Lemma max_stmt_le:
  (forall s m p, Ple (max_stmt s m) p <-> stmt_le p s /\ Ple m p)
  /\ (forall ls m p, Ple (max_lstmt ls m) p <-> lstmt_le p ls /\ Ple m p).
Proof.
  apply statement_lstmt_ind; intros; cbn [max_stmt max_lstmt stmt_le lstmt_le];
  try (match goal with o: option _ |- _ => destruct o; cbn [max_opt opt_le] end);
  repeat (first [rewrite max_expr_le | rewrite max_exprs_le | rewrite Ple_max_iff
                | match goal with H: forall m p, Ple _ p <-> _ |- _ => rewrite H end]); tauto.
Qed.

Definition bounded (top: positive) (s: statement) : Prop := stmt_le top s.

Lemma bounded_body: forall f, bounded (max_function f) (fn_body f).
Proof.
  intros. unfold bounded, max_function. exact (proj1 (proj1 (proj1 max_stmt_le _ _ _) (Ple_refl _))).
Qed.

Lemma bounded_seq_of_ls: forall top ls, lstmt_le top ls -> bounded top (seq_of_labeled_statement ls).
Proof.
  unfold bounded. induction ls; simpl; intros; auto. destruct H; split; auto.
Qed.

Lemma bounded_select_switch: forall top n ls, lstmt_le top ls -> lstmt_le top (select_switch n ls).
Proof.
  intros. unfold select_switch.
  assert (D: forall ls, lstmt_le top ls -> forall r, select_switch_default ls = r -> lstmt_le top r).
  { induction ls0; simpl; intros; subst; auto. destruct o; auto. apply IHls0; auto. apply H0. }
  assert (C: forall ls, lstmt_le top ls -> forall r, select_switch_case n ls = Some r -> lstmt_le top r).
  { induction ls0; simpl; intros; try discriminate. destruct o.
    - destruct (zeq z n); [inv H1; auto | apply IHls0; auto; apply H0].
    - apply IHls0; auto. apply H0. }
  destruct (select_switch_case n ls) eqn:SC; eauto.
Qed.

(** ** [switch] cases *)

Section SWITCH.

Variable ce: composite_env.
Variable sps: splits.

Lemma tr2_select_switch: forall n ls tls,
  tr2_l ce sps ls = Some tls -> tr2_l ce sps (select_switch n ls) = Some (select_switch n tls).
Proof.
  intros. unfold select_switch.
  assert (D: forall ls tls, tr2_l ce sps ls = Some tls ->
             tr2_l ce sps (select_switch_default ls) = Some (select_switch_default tls)).
  { induction ls0; simpl; intros. inv H0; auto.
    destruct (tr2 ce sps s) as [t|] eqn:T; try discriminate.
    destruct (tr2_l ce sps ls0) as [tl|] eqn:TL; try discriminate. inv H0. simpl.
    destruct o; auto. simpl. rewrite ?T, ?TL; auto. }
  assert (C: forall ls tls, tr2_l ce sps ls = Some tls ->
             match select_switch_case n ls with
             | Some r => exists tr, select_switch_case n tls = Some tr /\ tr2_l ce sps r = Some tr
             | None => select_switch_case n tls = None
             end).
  { induction ls0; simpl; intros. inv H0; auto.
    destruct (tr2 ce sps s) as [t|] eqn:T; try discriminate.
    destruct (tr2_l ce sps ls0) as [tl|] eqn:TL; try discriminate. inv H0. simpl.
    destruct o.
    - destruct (zeq z n). exists (LScons (Some z) t tl); split; auto. simpl. rewrite ?T, ?TL; auto.
      apply IHls0; auto.
    - apply IHls0; auto. }
  specialize (C ls tls H). destruct (select_switch_case n ls) as [r|].
  - destruct C as (tr & E1 & E2). rewrite E1. auto.
  - rewrite C. auto.
Qed.

Lemma tr2_seq_of_ls: forall ls tls,
  tr2_l ce sps ls = Some tls -> tr2 ce sps (seq_of_labeled_statement ls) = Some (seq_of_labeled_statement tls).
Proof.
  induction ls; simpl; intros. inv H; auto.
  destruct (tr2 ce sps s) as [t|] eqn:T; try discriminate.
  destruct (tr2_l ce sps ls) as [tl|] eqn:TL; try discriminate. inv H. simpl.
  rewrite ?T, (IHls tl); auto.
Qed.

Lemma body_ok_seq_of_ls: forall ret ls,
  body_ok_l sps ret ls = true -> body_ok sps ret (seq_of_labeled_statement ls) = true.
Proof.
  induction ls; simpl; intros; auto. apply andb_true_iff in H. destruct H. rewrite H, IHls; auto.
Qed.

Lemma body_ok_select_switch: forall ret n ls,
  body_ok_l sps ret ls = true -> body_ok_l sps ret (select_switch n ls) = true.
Proof.
  intros. unfold select_switch.
  assert (D: forall ls, body_ok_l sps ret ls = true -> body_ok_l sps ret (select_switch_default ls) = true).
  { induction ls0; simpl; intros; auto. apply andb_true_iff in H0. destruct H0. destruct o; auto.
    simpl. rewrite H0, H1; auto. }
  assert (C: forall ls r, body_ok_l sps ret ls = true -> select_switch_case n ls = Some r -> body_ok_l sps ret r = true).
  { induction ls0; simpl; intros; try discriminate. apply andb_true_iff in H0. destruct H0. destruct o.
    - destruct (zeq z n). inv H1. simpl. rewrite H0, H2; auto. eauto.
    - eauto. }
  destruct (select_switch_case n ls) eqn:SC; eauto.
Qed.

End SWITCH.

(** ** Live sets (stage 3) *)

Lemma lmem_cons: forall y x s, lmem y (x :: s) = Pos.eqb y x || lmem y s.
Proof. reflexivity. Qed.

Lemma lmem_ladd: forall y x s, lmem y (ladd x s) = Pos.eqb y x || lmem y s.
Proof.
  intros. unfold ladd. destruct (lmem x s) eqn:M; rewrite ?lmem_cons; auto.
  destruct (Pos.eqb y x) eqn:E; auto. apply Pos.eqb_eq in E. subst. auto.
Qed.

Lemma lmem_lunion: forall y a b, lmem y (lunion a b) = lmem y a || lmem y b.
Proof.
  unfold lunion. induction a as [ | x a IH]; intros; simpl. auto.
  rewrite IH, lmem_ladd.
  destruct (Pos.eqb y x), (lmem y a), (lmem y b); auto.
Qed.

Lemma lmem_lkill: forall y x s, lmem y (lkill x s) = negb (Pos.eqb x y) && lmem y s.
Proof.
  unfold lkill, lmem. induction s as [ | z s IH]; simpl. rewrite andb_false_r; auto.
  destruct (Pos.eqb x z) eqn:XZ; simpl; rewrite IH.
  - apply Pos.eqb_eq in XZ; subst z.
    destruct (Pos.eqb x y) eqn:XY; simpl; auto. rewrite (Pos.eqb_sym y x), XY. auto.
  - destruct (Pos.eqb y z) eqn:YZ; simpl; auto.
    apply Pos.eqb_eq in YZ; subst z. rewrite XZ. auto.
Qed.

Lemma lmem_kill_opt: forall y o s,
  lmem y (kill_opt o s) = match o with Some x => negb (Pos.eqb x y) && lmem y s | None => lmem y s end.
Proof.
  intros. destruct o; simpl; auto. apply lmem_lkill.
Qed.

(** The temporaries an expression reads. *)
Fixpoint occ (y: ident) (e: expr) : bool :=
  match e with
  | Etempvar x _ => Pos.eqb x y
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ | Efield a _ _ => occ y a
  | Ebinop _ a1 a2 _ => occ y a1 || occ y a2
  | _ => false
  end.

Lemma lmem_lu: forall sh y e s, lmem y (lu sh e s) = (tracked sh y && occ y e) || lmem y s.
Proof.
  induction e; intros; simpl; auto; try (rewrite andb_false_r; auto).
  - destruct (tracked sh i) eqn:T.
    + rewrite lmem_ladd. destruct (Pos.eqb i y) eqn:E.
      * apply Pos.eqb_eq in E; subst. rewrite T, Pos.eqb_refl. auto.
      * rewrite andb_false_r. simpl. destruct (Pos.eqb y i) eqn:E'; auto.
        apply Pos.eqb_eq in E'; subst. rewrite Pos.eqb_refl in E. discriminate.
    + destruct (Pos.eqb i y) eqn:E; [ | rewrite andb_false_r; auto].
      apply Pos.eqb_eq in E; subst. rewrite T. auto.
  - rewrite IHe1, IHe2. destruct (tracked sh y), (occ y e1), (occ y e2), (lmem y s); auto.
Qed.

Lemma lmem_lus: forall sh y al s,
  lmem y (fold_right (lu sh) s al) = (tracked sh y && existsb (occ y) al) || lmem y s.
Proof.
  induction al; intros; simpl. rewrite andb_false_r; auto.
  rewrite lmem_lu, IHal. destruct (tracked sh y), (occ y a), (existsb (occ y) al), (lmem y s); auto.
Qed.

Lemma subset_lmem: forall a b y, subset a b = true -> lmem y a = true -> lmem y b = true.
Proof.
  unfold subset. intros. rewrite forallb_forall in H. unfold lmem in H0.
  apply existsb_exists in H0. destruct H0 as (z & IN & E). apply Pos.eqb_eq in E. subst. auto.
Qed.

(** ** Evaluation reads only the temporaries an expression mentions *)

Lemma eval_expr_agree: forall ge e le m,
  (forall a v, eval_expr ge e le m a v ->
     forall le', (forall y, occ y a = true -> le'!y = le!y) -> eval_expr ge e le' m a v)
  /\ (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
     forall le', (forall y, occ y a = true -> le'!y = le!y) -> eval_lvalue ge e le' m a b ofs bf).
Proof.
  intros. apply eval_expr_lvalue_ind; intros; simpl in *;
  try (econstructor; eauto; fail).
  - constructor. rewrite H0; auto. apply Pos.eqb_refl.
  - match goal with A: forall y, occ y a1 || occ y a2 = true -> _ |- _ =>
      econstructor; [apply H0; intros y Y; apply A; rewrite Y; auto
                    | apply H2; intros y Y; apply A; rewrite Y; apply orb_true_r | eauto] end.
Qed.

(** ** Members dead at a point hold [Vundef] *)

Definition kill (sh: PTree.t bool) (L: lset) (le: temp_env) : temp_env :=
  PTree.map (fun y v => if tracked sh y && negb (lmem y L) then Vundef else v) le.

Lemma kill_get: forall sh L le y,
  (kill sh L le)!y = match le!y with
                     | Some v => Some (if tracked sh y && negb (lmem y L) then Vundef else v)
                     | None => None
                     end.
Proof.
  intros. unfold kill. rewrite PTree.gmap. destruct (le!y); auto.
Qed.

Lemma kill_live: forall sh L le y, (tracked sh y = false \/ lmem y L = true) -> (kill sh L le)!y = le!y.
Proof.
  intros. rewrite kill_get. destruct (le!y); auto. destruct H as [T | M]; [rewrite T | rewrite M, andb_false_r]; auto.
Qed.

Lemma eval_kill: forall ge e le m sh L a v,
  eval_expr ge e le m a v -> (forall y, tracked sh y = true -> occ y a = true -> lmem y L = true) ->
  eval_expr ge e (kill sh L le) m a v.
Proof.
  intros. eapply (proj1 (eval_expr_agree ge e le m)); eauto.
  intros. apply kill_live. destruct (tracked sh y) eqn:T; auto.
Qed.

Lemma eval_lvalue_kill: forall ge e le m sh L a b ofs bf,
  eval_lvalue ge e le m a b ofs bf -> (forall y, tracked sh y = true -> occ y a = true -> lmem y L = true) ->
  eval_lvalue ge e (kill sh L le) m a b ofs bf.
Proof.
  intros. eapply (proj2 (eval_expr_agree ge e le m)); eauto.
  intros. apply kill_live. destruct (tracked sh y) eqn:T; auto.
Qed.

Lemma eval_exprlist_kill: forall ge e le m sh L al tys vl,
  eval_exprlist ge e le m al tys vl ->
  (forall y, tracked sh y = true -> existsb (occ y) al = true -> lmem y L = true) ->
  eval_exprlist ge e (kill sh L le) m al tys vl.
Proof.
  induction 1; intros; econstructor; eauto.
  - apply eval_kill; auto. intros. apply H2; auto. simpl. rewrite H4; auto.
  - apply IHeval_exprlist. intros. apply H2; auto. simpl. rewrite H4, orb_true_r; auto.
Qed.

(** ** Keeping [match_temps] *)

Section TEMPS.

Variable ce: composite_env.
Variable sps: splits.
Variable top: positive.
Hypothesis SO: splits_ok ce sps top.

Let sh := shared_tree sps.

Lemma match_temps_ext: forall le1 le2 tle,
  (forall y, le2!y = le1!y) -> match_temps sps top le1 tle -> match_temps sps top le2 tle.
Proof.
  intros. destruct H0. constructor; intros; rewrite ?H in *; eauto.
Qed.

Lemma match_temps_set_unsplit: forall le tle x v,
  match_temps sps top le tle -> sps!x = None -> Ple x top ->
  match_temps sps top (PTree.set x v le) (PTree.set x v tle).
Proof.
  intros. destruct H. constructor; intros.
  - rewrite ! PTree.gsspec. destruct (peq x0 x); auto.
  - rewrite PTree.gsspec in H2. destruct (peq x0 x). subst; congruence.
    intros P. destruct (mt_split0 _ _ _ H H2 P) as (b & i & B & I & AT).
    exists b, i. rewrite ! PTree.gso; auto.
    + intro E. subst. pose proof (so_idx _ _ _ SO _ _ H). eapply Plt_strict. eapply Plt_Ple_trans; eauto.
    + intro E. subst. pose proof (so_base _ _ _ SO _ _ H). eapply Plt_strict. eapply Plt_Ple_trans; eauto.
  - rewrite ! PTree.gso. eauto.
    intro E; subst; pose proof (so_idx _ _ _ SO _ _ H); eapply Plt_strict; eapply Plt_Ple_trans; eauto.
    intro E; subst; pose proof (so_base _ _ _ SO _ _ H); eapply Plt_strict; eapply Plt_Ple_trans; eauto.
  - rewrite PTree.gso; auto. intro E; subst. eapply Plt_strict. eapply Plt_Ple_trans; eauto.
Qed.

Lemma tracked_split: forall y, tracked sh y = true -> exists sy, sps!y = Some sy.
Proof.
  unfold tracked, sh, shared_tree; intros. rewrite PTree.gmap in H.
  destruct (sps!y) as [sy | ]; simpl in H; [eauto | discriminate].
Qed.

Lemma untracked: forall y, sps!y = None -> tracked sh y = false.
Proof.
  unfold tracked, sh, shared_tree; intros. rewrite PTree.gmap, H. auto.
Qed.

(** A split temporary that shares its base with another one is tracked. *)
Lemma tracked_same_base: forall x y sx sy,
  x <> y -> sps!x = Some sx -> sps!y = Some sy -> sp_base sx = sp_base sy -> tracked sh y = true.
Proof.
  unfold tracked, sh, shared_tree; intros. rewrite PTree.gmap, H1. simpl.
  apply existsb_exists. exists (x, sx). split. apply PTree.elements_correct; auto.
  simpl. apply andb_true_iff. split.
  - apply negb_true_iff. apply Pos.eqb_neq. auto.
  - apply Pos.eqb_eq. auto.
Qed.

(** Forgetting the value of split temporaries (making them [Vundef]). *)
Lemma match_temps_weaken: forall le1 le2 tle,
  match_temps sps top le1 tle ->
  (forall y, le2!y = le1!y \/ (exists sy v, sps!y = Some sy /\ le1!y = Some v /\ le2!y = Some Vundef)) ->
  match_temps sps top le2 tle.
Proof.
  intros le1 le2 tle MT W. destruct MT. constructor; intros.
  - destruct (W x) as [E | (sy & v & S & _ & _)]; [rewrite E; auto | congruence].
  - destruct (W x) as [E | (sy & v' & S & _ & E)].
    + rewrite E in H0. eauto.
    + rewrite E in H0. inv H0. intros P; contradiction.
  - eauto.
  - destruct (W x) as [E | (sy & v & S & E1 & _)]; [rewrite E; auto | ].
    rewrite (mt_above0 x H) in E1. discriminate.
Qed.

Lemma match_temps_kill_full: forall L le tle,
  match_temps sps top le tle -> match_temps sps top (kill sh L le) tle.
Proof.
  intros. eapply match_temps_weaken; eauto. intros y. rewrite kill_get.
  destruct (le!y) as [v | ] eqn:V; auto.
  destruct (tracked sh y && negb (lmem y L)) eqn:K; auto.
  right. apply andb_true_iff in K. destruct K as [T _]. destruct (tracked_split _ T) as (sy & S). eauto.
Qed.

(** Fewer live members. *)
Lemma match_temps_kill: forall L L' le tle,
  match_temps sps top (kill sh L le) tle ->
  (forall y, tracked sh y = true -> lmem y L' = true -> lmem y L = true) ->
  match_temps sps top (kill sh L' le) tle.
Proof.
  intros. eapply match_temps_weaken; eauto. intros y. rewrite !kill_get.
  destruct (le!y) as [v | ] eqn:V; auto.
  destruct (tracked sh y) eqn:T; simpl; auto.
  destruct (lmem y L') eqn:M'; simpl.
  - rewrite (H0 y T M'). auto.
  - right. destruct (tracked_split _ T) as (sy & S). exists sy.
    destruct (lmem y L); simpl; eauto.
Qed.

(** An assignment to a temporary that is not split. *)
Lemma match_temps_kill_unsplit: forall L A le tle x v,
  match_temps sps top (kill sh L le) tle -> sps!x = None -> Ple x top ->
  (forall y, tracked sh y = true -> lmem y A = true -> y <> x -> lmem y L = true) ->
  match_temps sps top (kill sh A (PTree.set x v le)) (PTree.set x v tle).
Proof.
  intros L A le tle x v MT S X LIVE.
  assert (TX: tracked sh x = false).
  { destruct (tracked sh x) eqn:T; auto. destruct (tracked_split _ T) as (sx & S'). congruence. }
  apply match_temps_ext with (PTree.set x v (kill sh A le)).
  { intros y. rewrite kill_get, !PTree.gsspec. destruct (peq y x).
    - subst. rewrite TX. auto.
    - rewrite kill_get. auto. }
  apply match_temps_set_unsplit; auto.
  apply match_temps_kill with L; auto.
  intros y T M. apply LIVE; auto. intro; subst; congruence.
Qed.

(** An assignment to split temporary [x]: the target changes [x]'s index
    and maybe its base. If it changes the base, the other members with that
    base are dead afterwards. *)
Lemma match_temps_kill_split: forall L A le tle tle' x s v,
  match_temps sps top (kill sh L le) tle -> sps!x = Some s ->
  (forall y, tracked sh y = true -> lmem y A = true -> y <> x -> lmem y L = true) ->
  (forall y, y <> sp_base s -> y <> sp_idx s -> tle'!y = tle!y) ->
  tle'!(sp_base s) <> None -> tle'!(sp_idx s) <> None ->
  rel s v tle' ->
  (tle'!(sp_base s) = tle!(sp_base s)
   \/ (forall y sy, y <> x -> sps!y = Some sy -> sp_base sy = sp_base s -> lmem y A = false)) ->
  match_temps sps top (kill sh A (PTree.set x v le)) tle'.
Proof.
  intros L A le tle tle' x s v MT S LIVE OTHER DB DI REL BASE.
  assert (XT: Ple x top) by (eapply so_src; eauto).
  assert (NB: forall y, Ple y top -> y <> sp_base s) by
    (intros y LE E; subst; pose proof (so_base _ _ _ SO _ _ S); eapply Plt_strict; eapply Plt_Ple_trans; eauto).
  assert (NI: forall y, Ple y top -> y <> sp_idx s) by
    (intros y LE E; subst; pose proof (so_idx _ _ _ SO _ _ S); eapply Plt_strict; eapply Plt_Ple_trans; eauto).
  destruct MT. constructor; intros.
  - (* temporaries that are not split *)
    rewrite kill_get, PTree.gso by congruence. rewrite OTHER by auto.
    rewrite mt_same0 by auto. rewrite !kill_get, untracked by auto. auto.
  - (* split temporaries *)
    rename x0 into y, s0 into sy, v0 into w.
    rewrite kill_get, PTree.gsspec in H0. destruct (peq y x).
    + subst y. rewrite S in H. inv H. inv H0.
      destruct (tracked sh x && negb (lmem x A)); [intros P; contradiction | auto].
    + destruct (le!y) as [w0 | ] eqn:LY; [ | discriminate].
      destruct (tracked sh y && negb (lmem y A)) eqn:K; inv H0; [intros P; contradiction | ].
      assert (LY': (kill sh L le)!y = Some w).
      { rewrite kill_get, LY. destruct (tracked sh y) eqn:T; simpl in K |- *; auto.
        apply negb_false_iff in K. rewrite (LIVE y T K n). auto. }
      intros P. destruct (mt_split0 _ _ _ H LY' P) as (b & i & B & I & AT).
      assert (II: sp_idx sy <> sp_idx s) by (intro E; elim n; eapply (so_idx_inj _ _ _ SO); eauto).
      assert (IB: sp_idx sy <> sp_base s) by (eapply (so_idx_base _ _ _ SO); eauto).
      assert (BI: sp_base sy <> sp_idx s) by (intro E; eapply (so_idx_base _ _ _ SO); [exact S | exact H | congruence]).
      exists b, i. rewrite (OTHER (sp_idx sy)) by auto. split; [ | split; auto].
      destruct (peq (sp_base sy) (sp_base s)) as [EB | NEB].
      * destruct BASE as [E | DEAD].
        -- rewrite EB, E, <- EB. auto.
        -- rewrite (DEAD y sy n H EB) in K.
           rewrite (tracked_same_base x y s sy) in K; auto. discriminate.
      * rewrite OTHER; auto.
  - (* new temporaries defined *)
    destruct (mt_defined0 _ _ H) as [D1 D2].
    destruct (peq x0 x) as [E | NX]; [subst; rewrite S in H; inv H; split; auto | ].
    assert (II: sp_idx s0 <> sp_idx s) by (intro E; elim NX; eapply (so_idx_inj _ _ _ SO); eauto).
    assert (IB: sp_idx s0 <> sp_base s) by (eapply (so_idx_base _ _ _ SO); eauto).
    assert (BI: sp_base s0 <> sp_idx s) by (intro E; eapply (so_idx_base _ _ _ SO); [exact S | exact H | congruence]).
    split; [ | rewrite OTHER; auto].
    destruct (peq (sp_base s0) (sp_base s)) as [EB | NEB]; [rewrite EB; auto | rewrite OTHER; auto].
  - (* nothing above top *)
    rewrite kill_get, PTree.gso. 
    + specialize (mt_above0 x0 H). rewrite kill_get in mt_above0. destruct (le!x0); [discriminate | auto].
    + intro E; subst. eapply Plt_strict. eapply Plt_Ple_trans; eauto.
Qed.

End TEMPS.

(** ** Helpers for the simulation *)

Lemma tr_expr_typeof_ce: forall ce sps a, typeof (tr_expr ce sps nil nil a) = typeof a.
Proof.
  intros. destruct a; simpl; auto.
  - destruct (sps!i); auto.
  - destruct (index_form ce sps nil b a1 (tr_expr ce sps nil nil a2) t) eqn:IF.
    + unfold index_form in IF. destruct (ptr_offset b a1 _) as [[[tq sub] si] | ]; try discriminate.
      simpl in IF. destruct a1; try discriminate. destruct (sps!i); try discriminate.
      destruct (Z.eqb _ _); inv IF; auto.
    + destruct (index_compare _ _ _ _ _ _ _ _ _) eqn:IC; auto.
      unfold index_compare in IC.
      destruct (base_index sps nil _) as [[[b1 t1] i1] | ]; try discriminate.
      destruct (base_index sps nil _) as [[[b2 t2] i2] | ]; try discriminate.
      destruct (_ && _); try discriminate.
      destruct b; try discriminate;
      repeat match goal with
      | [ H: context[match ?x with _ => _ end] |- _ ] => destruct x; try discriminate
      end; inv IC; auto.
Qed.

(** ** Function entry *)

Lemma create_undef_temps_in: forall l x,
  In x (var_names l) -> (create_undef_temps l)!x = Some Vundef.
Proof.
  induction l as [ | [y t] l IH]; intros x IN. contradiction.
  rewrite var_names_cons in IN. simpl. rewrite PTree.gsspec.
  destruct (peq x y); auto. apply IH. destruct IN; [congruence | auto].
Qed.

Lemma create_undef_temps_notin: forall l x,
  ~ In x (var_names l) -> (create_undef_temps l)!x = None.
Proof.
  induction l as [ | [y t] l IH]; intros x N; simpl. apply PTree.gempty.
  rewrite var_names_cons in N. rewrite PTree.gso. apply IH. intro; apply N; right; auto.
  intro; subst; apply N; left; auto.
Qed.

(** Binding the same parameters to the same arguments in two environments. *)
Lemma bind_parameter_temps_match: forall params args le1 le1' le2,
  bind_parameter_temps params args le1 = Some le1' ->
  exists le2', bind_parameter_temps params args le2 = Some le2'
    /\ (forall x, In x (var_names params) -> le2'!x = le1'!x /\ le1'!x <> None)
    /\ (forall x, ~ In x (var_names params) -> le1'!x = le1!x /\ le2'!x = le2!x).
Proof.
  induction params as [ | [y t] params IH]; destruct args as [ | v args]; intros le1 le1' le2 B;
  cbn [bind_parameter_temps] in B; try discriminate.
  - inv B. exists le2; split; auto. split; intros; [contradiction | auto].
  - destruct (IH _ _ _ (PTree.set y v le2) B) as (le2' & B' & IN & OUT).
    exists le2'; split; auto. rewrite var_names_cons. split; intros x X.
    + destruct (in_dec peq x (var_names params)) as [I | N]; [apply IN; auto | ].
      destruct X as [E | I]; [subst | contradiction].
      destruct (OUT _ N) as [A C]. rewrite A, C, !PTree.gss. split; auto; discriminate.
    + assert (x <> y) by (intro; subst; apply X; left; auto).
      assert (N: ~ In x (var_names params)) by (intro; apply X; right; auto).
      destruct (OUT _ N) as [A C]. rewrite A, C, !PTree.gso; auto.
Qed.

Lemma max_vars_ge: forall l m, Ple m (max_vars l m).
Proof.
  induction l as [ | [y t] l IH]; intros; simpl. apply Ple_refl.
  eapply Ple_trans; [ | apply IH]. apply Pos.le_max_r.
Qed.

Lemma max_vars_in: forall l m x, In x (var_names l) -> Ple x (max_vars l m).
Proof.
  induction l as [ | [y t] l IH]; intros m x IN. contradiction.
  rewrite var_names_cons in IN. simpl. destruct IN as [E | IN].
  - subst. eapply Ple_trans; [ | apply max_vars_ge]. apply Pos.le_max_l.
  - apply IH; auto.
Qed.

Lemma params_le: forall f x, In x (var_names (fn_params f)) -> Ple x (max_function f).
Proof.
  intros. unfold max_function. eapply Ple_trans; [ | apply (proj1 max_stmt_ge)]. apply max_vars_in; auto.
Qed.

Lemma temps_le: forall f x, In x (var_names (fn_temps f)) -> Ple x (max_function f).
Proof.
  intros. unfold max_function. eapply Ple_trans; [ | apply (proj1 max_stmt_ge)].
  eapply Ple_trans; [ | apply max_vars_ge]. eapply Ple_trans; [ | apply max_vars_ge].
  apply max_vars_in; auto.
Qed.

Lemma entry_code_cons: forall sps p t params,
  entry_code sps ((p, t) :: params) =
  match sps!p with
  | Some sp => Ssequence (Sset (sp_base sp) (Etempvar p t)) (Ssequence (zero_index sp) (entry_code sps params))
  | None => entry_code sps params
  end.
Proof. reflexivity. Qed.

Lemma find_label_entry: forall sps lbl params k, find_label lbl (entry_code sps params) k = None.
Proof.
  induction params as [ | [p t] params IH]; intros; auto.
  rewrite entry_code_cons. destruct (sps!p); simpl; auto.
Qed.

Lemma sseq_cases: forall s1 s2,
  (s1 = Sskip /\ sseq s1 s2 = s2) \/ (s1 <> Sskip /\ s2 = Sskip /\ sseq s1 s2 = s1)
  \/ (s1 <> Sskip /\ sseq s1 s2 = Ssequence s1 s2).
Proof.
  intros. destruct s1; try (left; auto; fail);
  destruct s2; try (right; left; split; [discriminate | auto]; fail); right; right; split; auto; discriminate.
Qed.

Lemma find_label_sseq: forall lbl s1 s2 k,
  (forall k', find_label lbl s1 k' = None) -> find_label lbl (sseq s1 s2) k = find_label lbl s2 k.
Proof.
  intros. destruct (sseq_cases s1 s2) as [[A B] | [[A [B C]] | [A B]]].
  - rewrite B; auto.
  - rewrite C, H. subst s2. auto.
  - rewrite B. simpl. rewrite H. auto.
Qed.


Lemma tr2_switch_eq: forall ce sps a ls,
  tr2 ce sps (Sswitch a ls) =
  match tr2_l ce sps ls with Some tls => Some (Sswitch (tr_expr ce sps nil nil a) tls) | None => None end.
Proof. reflexivity. Qed.

Lemma tr2_lcons_eq: forall ce sps c s ls,
  tr2_l ce sps (LScons c s ls) =
  match tr2 ce sps s, tr2_l ce sps ls with Some t, Some tl => Some (LScons c t tl) | _, _ => None end.
Proof. reflexivity. Qed.

(** ** Assignments to a split temporary *)

Lemma set_split_cases: forall ce sps x sx a,
  sps!x = Some sx ->
  (exists ty, a = Etempvar x ty /\ set_split ce sps nil nil x sx a = Sskip)
  \/ (exists q ty sq, a = Etempvar q ty /\ q <> x /\ sps!q = Some sq /\ sp_size sq = sp_size sx
        /\ set_split ce sps nil nil x sx a = copy_base sx sq (Sset (sp_idx sx) (idx_of sq))
        /\ writes_base ce sps x sx a = negb (Pos.eqb (sp_base sx) (sp_base sq)))
  \/ (exists q tq n sub si sq, offset_of a = Some (q, tq, n, sub, si) /\ sps!q = Some sq
        /\ elem_size ce tq = sp_size sq /\ sp_size sq = sp_size sx
        /\ set_split ce sps nil nil x sx a =
             (if peq x q then Sset (sp_idx sx) (index_expr sq sub si (tr_expr ce sps nil nil n))
              else copy_base sx sq (Sset (sp_idx sx) (index_expr sq sub si (tr_expr ce sps nil nil n))))
        /\ writes_base ce sps x sx a = (if peq x q then false else negb (Pos.eqb (sp_base sx) (sp_base sq))))
  \/ (set_split ce sps nil nil x sx a = Ssequence (Sset (sp_base sx) (tr_expr ce sps nil nil a)) (zero_index sx)
       /\ writes_base ce sps x sx a = true
       /\ (forall q ty sq, a = Etempvar q ty -> sps!q = Some sq -> sp_size sq <> sp_size sx)).
Proof.
  intros ce sps x sx a SX. unfold set_split, writes_base.
  destruct a; try (right; right; right; split; [reflexivity | split; [reflexivity | intros; discriminate]]).
  - (* temporary *)
    destruct (sps!i) as [sq | ] eqn:SQ.
    + destruct (peq x i).
      * subst. left. exists t; auto.
      * destruct (Z.eqb (sp_size sq) (sp_size sx)) eqn:Z.
        -- right; left. exists i, t, sq. apply Z.eqb_eq in Z. repeat split; auto.
        -- right; right; right. split; auto. split; auto. intros q ty sq' E S'. inv E. rewrite SQ in S'. inv S'.
           apply Z.eqb_neq; auto.
    + right; right; right. split; auto. split; auto. intros q ty sq' E S'. inv E. congruence.
  - (* binary operation *)
    destruct (offset_of (Ebinop b a1 a2 t)) as [[[[[q tq] n] sub] si] | ] eqn:OF.
    + destruct (sps!q) as [sq | ] eqn:SQ.
      * destruct (Z.eqb (elem_size ce tq) (sp_size sq) && Z.eqb (sp_size sq) (sp_size sx)) eqn:Z.
        -- right; right; left. apply andb_true_iff in Z. destruct Z as [Z1 Z2].
           apply Z.eqb_eq in Z1. apply Z.eqb_eq in Z2. exists q, tq, n, sub, si, sq. repeat split; auto.
        -- right; right; right. split; auto. split; auto. intros; discriminate.
      * right; right; right. split; auto. split; auto. intros; discriminate.
    + right; right; right. split; auto. split; auto. intros; discriminate.
Qed.

Lemma offset_of_tr: forall ce sps a q tq n sub si sq,
  offset_of a = Some (q, tq, n, sub, si) -> sps!q = Some sq -> elem_size ce tq = sp_size sq ->
  tr_expr ce sps nil nil a = Ebinop Oadd (base_of sq) (index_expr sq sub si (tr_expr ce sps nil nil n)) (typeof a).
Proof.
  intros. unfold offset_of in H. destruct a; try discriminate. destruct b; try discriminate;
  destruct a1; try discriminate.
  - destruct (classify_add t0 (typeof a2)) eqn:C; try discriminate;
    injection H as E1 E2 E3 E4 E5; subst q tq n sub si;
    (cbn [tr_expr find_cache]; unfold index_form, ptr_offset; cbn [typeof find_cache];
     rewrite (tr_expr_typeof_ce ce sps a2), C, H0, H1, Z.eqb_refl; auto).
  - destruct (classify_sub t0 (typeof a2)) eqn:C; try discriminate;
    injection H as E1 E2 E3 E4 E5; subst q tq n sub si;
    (cbn [tr_expr find_cache]; unfold index_form, ptr_offset; cbn [typeof find_cache];
     rewrite (tr_expr_typeof_ce ce sps a2), C, H0, H1, Z.eqb_refl; auto).
Qed.

Lemma find_label_tr_set: forall ce sps x a ts lbl k,
  tr_set ce sps nil nil x a = Some ts -> find_label lbl ts k = None.
Proof.
  unfold tr_set; intros. destruct (sps!x) as [sx | ] eqn:SX.
  - inv H. destruct (set_split_cases ce sps x sx a SX) as
      [(ty & _ & E) | [(q & ty & sq & _ & _ & _ & _ & E & _) | [(q & tq & n & sub & si & sq & _ & _ & _ & _ & E & _) | (E & _)]]];
    rewrite E; auto; unfold copy_base; try destruct (peq _ _); try destruct (peq _ _); auto.
  - destruct a; try (inv H; auto; fail). destruct (is_some sps!i); inv H; auto.
Qed.

Lemma find_label_with_result: forall sps o (mk: option ident -> statement) lbl k,
  (forall o' k', find_label lbl (mk o') k' = None) -> find_label lbl (with_result sps o mk) k = None.
Proof.
  intros. unfold with_result. destruct o as [x | ]; auto. destruct (sps!x); auto. simpl. rewrite H; auto.
Qed.


(** ** What [lcheck] gives *)

Lemma lmem_In: forall y s, lmem y s = true <-> In y s.
Proof.
  unfold lmem; intros. rewrite existsb_exists. split.
  - intros (z & IN & E). apply Pos.eqb_eq in E. subst; auto.
  - intros. exists y; split; auto. apply Pos.eqb_refl.
Qed.

Lemma clash_false: forall sps x sx A y sy,
  clash sps x A = false -> sps!x = Some sx -> y <> x -> sps!y = Some sy -> sp_base sy = sp_base sx ->
  lmem y A = false.
Proof.
  unfold clash; intros. destruct (lmem y A) eqn:M; auto.
  apply lmem_In in M. assert (existsb (fun y => negb (Pos.eqb y x) && same_base sps x y) A = true).
  { apply existsb_exists. exists y; split; auto. unfold same_base. rewrite H0, H2.
    apply andb_true_iff; split. apply negb_true_iff, Pos.eqb_neq; auto. apply Pos.eqb_eq; auto. }
  congruence.
Qed.

Section LIVEFACTS.

Variable ce: composite_env.
Variable sps: splits.
Variable labs: PTree.t lset.

Lemma LC_seq: forall s1 s2 A B C L,
  LC ce sps labs (Ssequence s1 s2) A B C = (L, true) ->
  exists l2, LC ce sps labs s2 A B C = (l2, true) /\ LC ce sps labs s1 l2 B C = (L, true).
Proof.
  unfold LC; intros. cbn [lcheck] in H.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s2 A B C) as [l2 ok2] eqn:E2.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s1 l2 B C) as [l1 ok1] eqn:E1.
  injection H as E3 E4. apply andb_true_iff in E4. destruct E4; subst. eauto.
Qed.

Lemma LC_if: forall c s1 s2 A B C L,
  LC ce sps labs (Sifthenelse c s1 s2) A B C = (L, true) ->
  exists l1 l2, LC ce sps labs s1 A B C = (l1, true) /\ LC ce sps labs s2 A B C = (l2, true)
                /\ L = lu (shared_tree sps) c (lunion l1 l2).
Proof.
  unfold LC; intros. cbn [lcheck] in H.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s1 A B C) as [l1 ok1] eqn:E1.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s2 A B C) as [l2 ok2] eqn:E2.
  injection H as E3 E4. apply andb_true_iff in E4. destruct E4; subst. eauto.
Qed.

Lemma LC_loop: forall s1 s2 A B C H,
  LC ce sps labs (Sloop s1 s2) A B C = (H, true) ->
  exists l2 l1, LC ce sps labs s2 H A H = (l2, true) /\ LC ce sps labs s1 l2 A l2 = (l1, true)
                /\ subset l1 H = true.
Proof.
  unfold LC; intros s1 s2 A B C H EQ. cbn [lcheck] in EQ.
  match type of EQ with ?F ?fu ?h = _ =>
    assert (G: forall k0 head, F k0 head = (H, true) ->
               exists l2 l1, lcheck ce sps (shared_tree sps) labs (lfuel sps) s2 H A H = (l2, true)
                             /\ lcheck ce sps (shared_tree sps) labs (lfuel sps) s1 l2 A l2 = (l1, true)
                             /\ subset l1 H = true); [ | eapply G; eauto] end.
  induction k0 as [ | k0 IH]; intros head E; simpl in E;
  (destruct (lcheck ce sps (shared_tree sps) labs _ s2 head A head) as [l2 ok2] eqn:E2;
   destruct (lcheck ce sps (shared_tree sps) labs _ s1 l2 A l2) as [l1 ok1] eqn:E1;
   cbn beta iota in E; destruct (subset l1 head) eqn:SUB).
  - injection E as E3 E4. apply andb_true_iff in E4. destruct E4; subst. eauto.
  - discriminate.
  - injection E as E3 E4. apply andb_true_iff in E4. destruct E4; subst. eauto.
  - eapply IH; eauto.
Qed.

Lemma LC_switch: forall c ls A B C L,
  LC ce sps labs (Sswitch c ls) A B C = (L, true) ->
  exists l all, LCL ce sps labs ls A C = (l, all, true) /\ L = lu (shared_tree sps) c (lunion all A).
Proof.
  unfold LC, LCL; intros. rewrite lcheck_switch_eq in H.
  destruct (lcheck_l ce sps (shared_tree sps) labs (lfuel sps) ls A C) as [[l all] ok] eqn:E.
  injection H as E1 E2. subst. eauto.
Qed.

Lemma LC_label: forall l s A B C L,
  LC ce sps labs (Slabel l s) A B C = (L, true) ->
  LC ce sps labs s A B C = (L, true) /\ subset L (lab labs l) = true.
Proof.
  unfold LC; intros. cbn [lcheck] in H.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s A B C) as [l1 ok] eqn:E.
  injection H as E1 E2. apply andb_true_iff in E2. destruct E2; subst. auto.
Qed.

Lemma LCL_cons: forall c s ls A C l all,
  LCL ce sps labs (LScons c s ls) A C = (l, all, true) ->
  exists lr all', LCL ce sps labs ls A C = (lr, all', true) /\ LC ce sps labs s lr A C = (l, true)
                  /\ all = lunion l all'.
Proof.
  unfold LC, LCL; intros. rewrite lcheck_lcons_eq in H.
  destruct (lcheck_l ce sps (shared_tree sps) labs (lfuel sps) ls A C) as [[lr all'] ok'] eqn:E1.
  destruct (lcheck ce sps (shared_tree sps) labs (lfuel sps) s lr A C) as [l1 ok1] eqn:E2.
  injection H as E3 E4 E5. apply andb_true_iff in E5. destruct E5; subst. eauto.
Qed.

(** The cases of a [switch], run in sequence from the first one. *)
Lemma LCL_seq: forall ls A C l all,
  LCL ce sps labs ls A C = (l, all, true) -> LC ce sps labs (seq_of_labeled_statement ls) A A C = (l, true).
Proof.
  induction ls; intros.
  - unfold LCL in H. cbn [lcheck_l] in H. inv H. reflexivity.
  - destruct (LCL_cons _ _ _ _ _ _ _ H) as (lr & all' & E1 & E2 & E3).
    simpl. unfold LC in *. cbn [lcheck]. rewrite (IHls _ _ _ _ E1), E2. auto.
Qed.

Lemma LCL_head: forall ls A C l all,
  LCL ce sps labs ls A C = (l, all, true) -> forall y, lmem y l = true -> lmem y all = true.
Proof.
  destruct ls; intros.
  - unfold LCL in H. cbn [lcheck_l] in H. inv H. auto.
  - destruct (LCL_cons _ _ _ _ _ _ _ H) as (lr & all' & E1 & E2 & E3). subst. rewrite lmem_lunion, H0. auto.
Qed.

(** The cases from the selected one on. *)
Lemma LCL_select: forall n ls A C l all,
  LCL ce sps labs ls A C = (l, all, true) ->
  exists l' all', LCL ce sps labs (select_switch n ls) A C = (l', all', true)
                  /\ (forall y, lmem y l' = true -> lmem y all = true).
Proof.
  intros. unfold select_switch.
  assert (D: forall ls l all, LCL ce sps labs ls A C = (l, all, true) ->
             exists l' all', LCL ce sps labs (select_switch_default ls) A C = (l', all', true)
                             /\ (forall y, lmem y l' = true -> lmem y all = true)).
  { induction ls0; intros; simpl.
    - exists l0, all0. split; auto. eapply LCL_head; eauto.
    - destruct o.
      + destruct (LCL_cons _ _ _ _ _ _ _ H0) as (lr & all' & E1 & E2 & E3).
        destruct (IHls0 _ _ E1) as (l' & all'' & F & G). exists l', all''. split; auto.
        intros. subst. rewrite lmem_lunion, G; auto. apply orb_true_r.
      + exists l0, all0. split; auto. eapply LCL_head; eauto. }
  assert (K: forall ls l all r, LCL ce sps labs ls A C = (l, all, true) -> select_switch_case n ls = Some r ->
             exists l' all', LCL ce sps labs r A C = (l', all', true)
                             /\ (forall y, lmem y l' = true -> lmem y all = true)).
  { induction ls0; intros; simpl in H1; try discriminate.
    destruct (LCL_cons _ _ _ _ _ _ _ H0) as (lr & all' & E1 & E2 & E3).
    assert (TAIL: forall r, select_switch_case n ls0 = Some r ->
                  exists l' all'', LCL ce sps labs r A C = (l', all'', true)
                                   /\ (forall y, lmem y l' = true -> lmem y all0 = true)).
    { intros. destruct (IHls0 _ _ _ E1 H2) as (l' & all'' & F & G). exists l', all''. split; auto.
      intros. subst. rewrite lmem_lunion, G; auto. apply orb_true_r. }
    destruct o; auto.
    destruct (zeq z n); auto. injection H1 as R; subst r. exists l0, all0. split; auto. eapply LCL_head; eauto. }
  destruct (select_switch_case n ls) as [r | ] eqn:SC; eauto.
Qed.

End LIVEFACTS.

(** ** The simulation *)

Section SIMULATION.

Variable share: bool.
Variable prog: program.

Let ce := prog_comp_env prog.
Let nw := nonwriting (prog_defs prog).
Let tp := tprog share prog.
Let ge := Clight.globalenv prog.
Let tge := Clight.globalenv tp.

Lemma CENV: genv_cenv tge = genv_cenv ge.
Proof. exact (comp_env_preserved share prog). Qed.

Lemma SYMB: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (symbols_preserved share prog). Qed.

Definition stmt_ok (f: function) (sps: splits) (s: statement) : Prop :=
  body_ok sps (fn_return f) s = true /\ bounded (max_function f) s.

(** Where a call's result goes in the target, and what the target does
    after the call: a split result is its base, then its index is zeroed. *)
Definition dst (sps: splits) (o: option ident) : option ident :=
  match o with
  | Some x => match sps!x with Some s => Some (sp_base s) | None => Some x end
  | None => None
  end.

Definition fixup (sps: splits) (o: option ident) (tk: cont) : cont :=
  match o with
  | Some x => match sps!x with Some s => Kseq (zero_index s) tk | None => tk end
  | None => tk
  end.

(** Continuations, with the members live when control reaches them normally,
    by [break] and by [continue] ([A], [B], [C]). *)
Inductive match_cont (f: function) (sps: splits) (labs: PTree.t lset): cont -> cont -> lset -> lset -> lset -> Prop :=
  | mc_stop: forall A B C, match_cont f sps labs Kstop Kstop A B C
  | mc_seq: forall s k ts tk A' B C A,
      tr2 ce sps s = Some ts -> stmt_ok f sps s -> LC ce sps labs s A' B C = (A, true) ->
      match_cont f sps labs k tk A' B C ->
      match_cont f sps labs (Kseq s k) (Kseq ts tk) A B C
  | mc_loop1: forall s1 s2 k ts1 ts2 tk A' B' C' H l2,
      tr2 ce sps s1 = Some ts1 -> tr2 ce sps s2 = Some ts2 ->
      stmt_ok f sps s1 -> stmt_ok f sps s2 ->
      LC ce sps labs (Sloop s1 s2) A' B' C' = (H, true) -> LC ce sps labs s2 H A' H = (l2, true) ->
      match_cont f sps labs k tk A' B' C' ->
      match_cont f sps labs (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk) l2 A' l2
  | mc_loop2: forall s1 s2 k ts1 ts2 tk A' B' C' H,
      tr2 ce sps s1 = Some ts1 -> tr2 ce sps s2 = Some ts2 ->
      stmt_ok f sps s1 -> stmt_ok f sps s2 ->
      LC ce sps labs (Sloop s1 s2) A' B' C' = (H, true) ->
      match_cont f sps labs k tk A' B' C' ->
      match_cont f sps labs (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk) H A' H
  | mc_switch: forall k tk A B C,
      match_cont f sps labs k tk A B C -> match_cont f sps labs (Kswitch k) (Kswitch tk) A A C
  | mc_call: forall optid f' e le k tf' tle tk sps' labs' A' B' C' A B C,
      tr_function ce sps' labs' f' tf' ->
      match_temps sps' (max_function f') (kill (shared_tree sps') (kill_opt optid A') le) tle ->
      opt_le (max_function f') optid ->
      result_ok sps' optid A' = true ->
      match_cont f' sps' labs' k tk A' B' C' ->
      match_cont f sps labs (Kcall optid f' e le k) (Kcall (dst sps' optid) tf' e tle (fixup sps' optid tk)) A B C.

Inductive match_states: Clight.state -> Clight.state -> Prop :=
  | ms_regular: forall f s k e le m tf ts tk tle sps labs A B C L
      (TRF: tr_function ce sps labs f tf)
      (TS: tr2 ce sps s = Some ts)
      (OK: stmt_ok f sps s)
      (LV: LC ce sps labs s A B C = (L, true))
      (MT: match_temps sps (max_function f) (kill (shared_tree sps) L le) tle)
      (MC: match_cont f sps labs k tk A B C),
      match_states (State f s k e le m) (State tf ts tk e tle m)
  | ms_call: forall fd args k m tfd tk f sps labs A B C
      (MF: match_fundef share prog prog fd tfd)
      (MC: match_cont f sps labs k tk A B C)
      (CC: is_call_cont k),
      match_states (Callstate fd args k m) (Callstate tfd args tk m)
  | ms_return: forall v k m tk f sps labs A B C
      (MC: match_cont f sps labs k tk A B C)
      (CC: is_call_cont k),
      match_states (Returnstate v k m) (Returnstate v tk m).

(** Only a copy of a split temporary to itself takes no target step. *)
Definition measure (S: Clight.state) : nat :=
  match S with
  | State _ (Sset _ _) _ _ _ _ => 1%nat
  | _ => O
  end.

Lemma match_cont_call_cont: forall f sps labs k tk A B C,
  match_cont f sps labs k tk A B C ->
  exists f' sps' labs', match_cont f' sps' labs' (call_cont k) (call_cont tk) nil nil nil.
Proof.
  induction 1; simpl; eauto.
  - exists f, sps, labs. constructor.
  - exists f, sps, labs. econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont: forall f sps labs k tk A B C,
  match_cont f sps labs k tk A B C -> is_call_cont k -> is_call_cont tk.
Proof.
  intros. inv H; simpl in *; auto.
Qed.

Lemma match_cont_call_cont_is: forall f sps labs k tk A B C,
  match_cont f sps labs k tk A B C -> is_call_cont (call_cont k).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_cont_change: forall f sps labs k tk A B C f' sps' labs' A' B' C',
  match_cont f sps labs k tk A B C -> is_call_cont k -> match_cont f' sps' labs' k tk A' B' C'.
Proof.
  intros. inv H; simpl in H0; try contradiction; econstructor; eauto.
Qed.

Lemma mc_call': forall f sps labs A B C optid f' e le k tf' tle tk sps' labs' A' B' C' o tk',
  tr_function ce sps' labs' f' tf' ->
  match_temps sps' (max_function f') (kill (shared_tree sps') (kill_opt optid A') le) tle ->
  opt_le (max_function f') optid -> result_ok sps' optid A' = true ->
  match_cont f' sps' labs' k tk A' B' C' ->
  o = dst sps' optid -> tk' = fixup sps' optid tk ->
  match_cont f sps labs (Kcall optid f' e le k) (Kcall o tf' e tle tk') A B C.
Proof.
  intros. subst. econstructor; eauto.
Qed.

(** *** Expressions in a function *)

Section EXPR.

Variables (f: function) (sps: splits) (labs: PTree.t lset) (tf: function) (le tle: temp_env) (e: env) (m: mem).
Hypothesis TRF: tr_function ce sps labs f tf.
Hypothesis MT: match_temps sps (max_function f) le tle.

Let TR := tr_expr ce sps nil nil.

Lemma tr_eval: forall a v,
  eval_expr ge e le m a v -> uses_ok sps a = true -> (bare_split sps a = true -> ptrish v) ->
  eval_expr tge e tle m (TR a) v.
Proof.
  exact (proj1 (tr_expr_correct ge tge CENV SYMB sps (max_function f)
                  (so_shape _ _ _ (tf_splits _ _ _ _ _ TRF)) le tle MT e m)).
Qed.

Lemma tr_eval_lvalue: forall a b ofs bf,
  eval_lvalue ge e le m a b ofs bf -> uses_ok sps a = true ->
  eval_lvalue tge e tle m (tr_lv ce sps nil nil a) b ofs bf.
Proof.
  exact (proj2 (tr_expr_correct ge tge CENV SYMB sps (max_function f)
                  (so_shape _ _ _ (tf_splits _ _ _ _ _ TRF)) le tle MT e m)).
Qed.

Lemma tr_eval_list: forall al tys vl,
  eval_exprlist ge e le m al tys vl -> args_ok sps al tys = true ->
  eval_exprlist tge e tle m (map TR al) tys vl.
Proof.
  induction 1; simpl; intros OK.
  - constructor.
  - apply andb_true_iff in OK. destruct OK as [R OK]. unfold received_ok in R.
    apply andb_true_iff in R. destruct R as [U NV].
    apply eval_Econs with v1.
    + apply tr_eval; auto. intros B. destruct (bare_pointer _ _ U B) as (t & ta & T). rewrite T in H0.
      eapply cast_ptr; eauto. intro V; subst ty. rewrite B in NV. discriminate.
    + unfold TR. rewrite tr_expr_typeof_ce. auto.
    + auto.
Qed.

End EXPR.

Lemma alloc_variables_preserved: forall e m vars e' m',
  alloc_variables ge e m vars e' m' -> alloc_variables tge e m vars e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite CENV; auto.
Qed.

Lemma blocks_of_env_preserved: forall e, blocks_of_env tge e = blocks_of_env ge e.
Proof.
  intros. unfold blocks_of_env, block_of_binding. rewrite CENV. auto.
Qed.

Lemma assign_loc_preserved: forall ty m b ofs bf v m',
  assign_loc ge ty m b ofs bf v m' -> assign_loc tge ty m b ofs bf v m'.
Proof.
  intros. rewrite CENV. auto.
Qed.

Lemma find_funct_ptrish: forall v fd, Genv.find_funct ge v = Some fd -> ptrish v.
Proof.
  intros. destruct v; simpl in H; try discriminate; exact I.
Qed.

(** *** Function entry *)

Section ENTRY.

Variables (tf: function) (sps: splits) (top: positive) (e: env) (m: mem).
Hypothesis SO: splits_ok ce sps top.

Lemma above_base: forall x s y, sps!x = Some s -> Ple y top -> y <> sp_base s.
Proof.
  intros; intro E; subst. pose proof (so_base _ _ _ SO _ _ H). eapply Plt_strict. eapply Plt_Ple_trans; eauto.
Qed.

Lemma above_idx: forall x s y, sps!x = Some s -> Ple y top -> y <> sp_idx s.
Proof.
  intros; intro E; subst. pose proof (so_idx _ _ _ SO _ _ H). eapply Plt_strict. eapply Plt_Ple_trans; eauto.
Qed.

(** The entry code sets the base of every split parameter to the parameter
    and its index to 0. Split parameters have distinct bases. *)
Lemma entry_exec: forall params tle,
  list_norepet (var_names params) ->
  (forall p, In p (var_names params) -> Ple p top /\ tle!p <> None) ->
  (forall p q sp sq, In p (var_names params) -> In q (var_names params) ->
     sps!p = Some sp -> sps!q = Some sq -> sp_base sp = sp_base sq -> p = q) ->
  exists tle',
    (forall k, star step2 tge (State tf (entry_code sps params) k e tle m) E0 (State tf Sskip k e tle' m))
    /\ (entry_code sps params = Sskip -> tle' = tle)
    /\ (forall p s, In p (var_names params) -> sps!p = Some s ->
          tle'!(sp_base s) = tle!p /\ tle'!(sp_idx s) = Some (Vlong Int64.zero))
    /\ (forall y, (forall p s, In p (var_names params) -> sps!p = Some s -> y <> sp_base s /\ y <> sp_idx s) ->
          tle'!y = tle!y)
    /\ (forall y, tle!y <> None -> tle'!y <> None).
Proof.
  induction params as [ | [p t] params IH]; intros tle NR P PB.
  - exists tle. split; [intros; apply star_refl | split; [auto | split; [intros; contradiction | auto]]].
  - rewrite var_names_cons in NR, P, PB. inv NR. rewrite entry_code_cons. rewrite var_names_cons.
    assert (PB': forall p q sp sq, In p (var_names params) -> In q (var_names params) ->
                 sps!p = Some sp -> sps!q = Some sq -> sp_base sp = sp_base sq -> p = q)
      by (intros; eapply PB; eauto; right; auto).
    destruct (sps!p) as [sp | ] eqn:S.
    + (* a split parameter *)
      destruct (P p (or_introl eq_refl)) as [PT D]. destruct (tle!p) as [v | ] eqn:V; [ | congruence].
      set (tle2 := PTree.set (sp_idx sp) (Vlong Int64.zero) (PTree.set (sp_base sp) v tle)).
      assert (G: forall y, Ple y top -> tle2!y = tle!y).
      { intros. unfold tle2. rewrite !PTree.gso; auto. eapply above_base; eauto. eapply above_idx; eauto. }
      assert (BI2: sp_idx sp <> sp_base sp) by (eapply (so_idx_base _ _ _ SO); eauto).
      destruct (IH tle2 H2) as (tle' & STAR & SK & BI & OTHER & DEF); auto.
      { intros. destruct (P p0 (or_intror H)). split; auto. rewrite G; auto. }
      assert (NOTP: forall y, y = sp_base sp \/ y = sp_idx sp ->
                    forall p0 s0, In p0 (var_names params) -> sps!p0 = Some s0 -> y <> sp_base s0 /\ y <> sp_idx s0).
      { intros y Y p0 s0 IN S0. assert (NE: p0 <> p) by (intro; subst; contradiction).
        destruct Y; subst y; split; intro E.
        - elim NE. symmetry. eapply PB; eauto. left; auto. right; auto.
        - exact (so_idx_base _ _ _ SO _ _ _ _ S0 S (eq_sym E)).
        - exact (so_idx_base _ _ _ SO _ _ _ _ S S0 E).
        - elim NE. eapply (so_idx_inj _ _ _ SO); eauto. }
      exists tle'. split; [ | split; [discriminate | split; [ | split]]].
      * intros k. eapply star_left. apply step_seq.
        eapply star_left. apply step_set. constructor. eauto.
        eapply star_left. apply step_skip_seq.
        eapply star_left. apply step_seq.
        eapply star_left. apply step_set. constructor.
        eapply star_left. apply step_skip_seq.
        apply STAR. all: reflexivity.
      * intros p0 s0 IN S0. destruct IN as [E | IN].
        -- subst p0. rewrite S in S0. inv S0.
           rewrite (OTHER (sp_base s0) (NOTP _ (or_introl eq_refl))).
           rewrite (OTHER (sp_idx s0) (NOTP _ (or_intror eq_refl))).
           unfold tle2. rewrite PTree.gss, PTree.gso, PTree.gss; auto.
        -- destruct (BI _ _ IN S0) as [A B]. rewrite A, B. split; auto. apply G. apply (P p0 (or_intror IN)).
      * intros y Y. destruct (Y p sp (or_introl eq_refl) S) as [Y1 Y2].
        rewrite OTHER; [unfold tle2; rewrite !PTree.gso; auto | ].
        intros p0 s0 IN S0. apply (Y p0 s0); auto. right; auto.
      * intros y Y. apply DEF. unfold tle2. rewrite !PTree.gsspec.
        destruct (peq y (sp_idx sp)); [discriminate | ]. destruct (peq y (sp_base sp)); [discriminate | auto].
    + (* a parameter that is not split *)
      destruct (IH tle H2) as (tle' & STAR & SK & BI & OTHER & DEF); auto.
      { intros. apply P. right; auto. }
      exists tle'. split; auto. split; auto. split; [ | split; auto].
      * intros p0 s0 IN S0. destruct IN as [E | IN]. subst; congruence. auto.
      * intros y Y. apply OTHER. intros p0 s0 IN S0. apply (Y p0 s0); auto. right; auto.
Qed.

Lemma star_sseq: forall s1 s2 k tle tle',
  (forall k', star step2 tge (State tf s1 k' e tle m) E0 (State tf Sskip k' e tle' m)) ->
  (s1 = Sskip -> tle' = tle) ->
  star step2 tge (State tf (sseq s1 s2) k e tle m) E0 (State tf s2 k e tle' m).
Proof.
  intros. destruct (sseq_cases s1 s2) as [[A B] | [[A [B C]] | [A B]]].
  - rewrite B, (H0 A). apply star_refl.
  - rewrite C. subst s2. auto.
  - rewrite B. eapply star_left. apply step_seq. eapply star_right. apply H. apply step_skip_seq.
    reflexivity. reflexivity.
Qed.

End ENTRY.

Lemma entry_sim: forall f sps labs tf vargs m e le m1 tk,
  tr_function ce sps labs f tf ->
  function_entry2 ge f vargs m e le m1 ->
  exists body' tle, tr2 ce sps (fn_body f) = Some body'
    /\ plus step2 tge (Callstate (Internal tf) vargs tk m) E0 (State tf body' tk e tle m1)
    /\ match_temps sps (max_function f) le tle.
Proof.
  intros until tk; intros TRF FE. inv FE.
  set (top := max_function f).
  pose proof (tf_splits _ _ _ _ _ TRF) as SO.
  destruct (tf_body _ _ _ _ _ TRF) as (body' & TB & FB).
  destruct (bind_parameter_temps_match _ _ _ _ (create_undef_temps (fn_temps tf)) H3) as (tle0 & B0 & IN & OUT).
  destruct (entry_exec tf sps top e m1 SO (fn_params f) tle0 H0) as (tle' & STAR & SK & BI & OTHER & DEF).
  { intros p IP. split. apply params_le; auto. destruct (IN _ IP) as [A C]. rewrite A; auto. }
  { exact (tf_pbases _ _ _ _ _ TRF). }
  assert (NB: forall y, Ple y top -> forall p s, In p (var_names (fn_params f)) -> sps!p = Some s ->
                y <> sp_base s /\ y <> sp_idx s).
  { intros. split. eapply above_base; eauto. eapply above_idx; eauto. }
  assert (NP: forall y, Plt top y -> ~ In y (var_names (fn_params f))).
  { intros y LT IP. apply params_le in IP. eapply Plt_strict. eapply Plt_Ple_trans; eauto. }
  exists body', tle'. split; auto. split.
  - eapply plus_left.
    { apply step_internal_function. constructor.
      - rewrite (tf_vars _ _ _ _ _ TRF); auto.
      - rewrite (tf_params _ _ _ _ _ TRF); auto.
      - apply (tf_entry _ _ _ _ _ TRF); auto.
      - rewrite (tf_vars _ _ _ _ _ TRF). apply alloc_variables_preserved. eexact H2.
      - rewrite (tf_params _ _ _ _ _ TRF). eexact B0. }
    rewrite FB. apply star_sseq; auto. reflexivity.
  - constructor.
    + (* same temporaries *)
      intros x X S. rewrite (OTHER x (NB x X)).
      destruct (in_dec peq x (var_names (fn_params f))) as [I | N].
      * apply IN; auto.
      * destruct (OUT x N) as [A C]. rewrite A, C.
        pose proof (tf_temps_src _ _ _ _ _ TRF x X S) as T.
        destruct (in_dec peq x (var_names (fn_temps f))) as [I' | N'].
        -- rewrite !create_undef_temps_in; tauto.
        -- rewrite !create_undef_temps_notin; tauto.
    + (* split temporaries *)
      intros x s v S L P.
      destruct (in_dec peq x (var_names (fn_params f))) as [I | N].
      * destruct (BI _ _ I S) as [A C]. destruct (IN _ I) as [A' _].
        exists v, Int64.zero. rewrite A, A'. split; auto. split; auto. apply at_index_zero; auto.
      * destruct (OUT x N) as [A _]. rewrite A in L.
        destruct (in_dec peq x (var_names (fn_temps f))) as [I' | N'].
        -- rewrite create_undef_temps_in in L; auto. inv L. contradiction.
        -- rewrite create_undef_temps_notin in L; auto. discriminate.
    + (* new temporaries defined *)
      intros x s S. destruct (tf_temps_new _ _ _ _ _ TRF x s S) as [TB' TI].
      destruct (OUT (sp_base s)) as [_ C1]. apply NP. eapply (so_base _ _ _ SO); eauto.
      destruct (OUT (sp_idx s)) as [_ C2]. apply NP. eapply (so_idx _ _ _ SO); eauto.
      split; apply DEF; [rewrite C1 | rewrite C2]; rewrite create_undef_temps_in; auto; discriminate.
    + (* nothing above top *)
      intros x LT. destruct (OUT x (NP x LT)) as [A _]. rewrite A. apply create_undef_temps_notin.
      intro IT. apply temps_le in IT. eapply Plt_strict. eapply Plt_Ple_trans; eauto.
Qed.

(** *** Assignments to temporaries *)

Lemma tr_set_unsplit: forall sps x a ts,
  tr_set ce sps nil nil x a = Some ts -> sps!x = None ->
  ts = Sset x (tr_expr ce sps nil nil a) /\ bare_split sps a = false.
Proof.
  unfold tr_set; intros. rewrite H0 in H. destruct a; try (inv H; auto; fail).
  destruct (sps!i) as [s | ] eqn:S; simpl in H; inv H. cbn [tr_expr find_cache]. rewrite S.
  unfold bare_split. rewrite S. auto.
Qed.

Lemma kill_set_same: forall sh L le x v,
  le!x = Some v -> forall y, (kill sh L (PTree.set x v le))!y = (kill sh L le)!y.
Proof.
  intros. rewrite !kill_get, PTree.gsspec. destruct (peq y x); subst; auto. rewrite H. auto.
Qed.

Lemma sset_sim: forall f sps labs tf tk e le tle m x a v ts A,
  tr_function ce sps labs f tf ->
  match_temps sps (max_function f) (kill (shared_tree sps) (lu (shared_tree sps) a (lkill x A)) le) tle ->
  (match sps!x with Some sx => negb (writes_base ce sps x sx a && clash sps x A) = true | None => True end) ->
  tr_set ce sps nil nil x a = Some ts -> uses_ok sps a = true -> copy_ok sps x a = true ->
  Ple x (max_function f) ->
  eval_expr ge e le m a v ->
  (exists tle', plus step2 tge (State tf ts tk e tle m) E0 (State tf Sskip tk e tle' m)
               /\ match_temps sps (max_function f) (kill (shared_tree sps) A (PTree.set x v le)) tle')
  \/ (ts = Sskip /\ match_temps sps (max_function f) (kill (shared_tree sps) A (PTree.set x v le)) tle).
Proof.
  intros until A; intros TRF MT CHK TS U CP XT EV.
  set (L := lu (shared_tree sps) a (lkill x A)) in *.
  pose proof (tf_splits _ _ _ _ _ TRF) as SO.
  assert (LIVE: forall y, tracked (shared_tree sps) y = true -> lmem y A = true -> y <> x -> lmem y L = true).
  { intros. unfold L. rewrite lmem_lu, lmem_lkill, H0.
    destruct (Pos.eqb x y) eqn:E; [apply Pos.eqb_eq in E; congruence | ]. simpl. apply orb_true_r. }
  assert (EVK: eval_expr ge e (kill (shared_tree sps) L le) m a v).
  { apply eval_kill; auto. intros. unfold L. rewrite lmem_lu, H, H0. auto. }
  destruct (sps!x) as [sx | ] eqn:SX.
  2: { (* x is not split *)
    destruct (tr_set_unsplit _ _ _ _ TS SX) as [E B]. subst ts. left.
    exists (PTree.set x v tle). split.
    - apply plus_one. apply step_set. eapply tr_eval; eauto. congruence.
    - eapply match_temps_kill_unsplit; eauto. }
  unfold tr_set in TS. rewrite SX in TS. inv TS.
  assert (BX: sp_idx sx <> sp_base sx) by (eapply (so_idx_base _ _ _ SO); eauto).
  destruct (mt_defined _ _ _ _ MT x sx SX) as [DB DI].
  (* the value of a split temporary read by [a] *)
  assert (READ: forall q ty sq, a = Etempvar q ty -> sps!q = Some sq -> le!q = Some v -> rel sq v tle).
  { intros. eapply (mt_split _ _ _ _ MT); eauto. rewrite kill_live; auto.
    destruct (tracked (shared_tree sps) q) eqn:T; auto. right. unfold L. subst a.
    rewrite lmem_lu, T. simpl. rewrite Pos.eqb_refl. auto. }
  destruct (set_split_cases ce sps x sx a SX) as
    [(ty & Ea & E) | [(q & ty & sq & Ea & NE & SQ & SZ & E & WB) |
     [(q & tq & n & sub & si & sq & OF & SQ & ES & SZ & E & WB) | (E & WB & NB)]]];
  rewrite E.
  - (* x = x: nothing to do *)
    right. split; auto. subst a.
    assert (LX: le!x = Some v) by (inv EV; [auto | match goal with H: eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end]).
    apply match_temps_kill with L.
    + apply match_temps_ext with (kill (shared_tree sps) L le); auto. apply kill_set_same; auto.
    + intros y T M. destruct (peq y x).
      * subst. unfold L. rewrite lmem_lu, T. simpl. rewrite Pos.eqb_refl. auto.
      * apply LIVE; auto.
  - (* x = q, another split temporary of the same unit: copy the index, and the base unless shared *)
    subst a. left.
    assert (LQ: le!q = Some v) by (inv EV; [auto | match goal with H: eval_lvalue _ _ _ _ _ _ _ _ |- _ => inv H end]).
    destruct (mt_defined _ _ _ _ MT q sq SQ) as [DBq DIq].
    destruct (tle!(sp_idx sq)) as [wi | ] eqn:WI; [ | congruence].
    destruct (tle!(sp_base sq)) as [wb | ] eqn:WBq; [ | congruence].
    assert (I1: sp_base sq <> sp_idx sx) by (intro Q; exact (so_idx_base _ _ _ SO _ _ _ _ SX SQ (eq_sym Q))).
    assert (REL: forall tle', tle'!(sp_base sx) = Some wb -> tle'!(sp_idx sx) = Some wi -> rel sx v tle').
    { intros tle' B I P. destruct (READ q ty sq eq_refl SQ LQ P) as (b & i & B' & I' & AT).
      exists b, i. split; [congruence | split; [congruence | ]]. rewrite <- SZ. auto. }
    unfold copy_base. destruct (peq (sp_base sx) (sp_base sq)) as [EB | NEB].
    + (* shared base: only the index *)
      exists (PTree.set (sp_idx sx) wi tle). split.
      * apply plus_one. apply step_set. constructor. auto.
      * eapply match_temps_kill_split with (L := L); eauto.
        -- intros y Y1 Y2. rewrite PTree.gso; auto.
        -- rewrite PTree.gso; auto.
        -- rewrite PTree.gss; discriminate.
        -- apply REL. rewrite PTree.gso, EB; auto. apply PTree.gss.
        -- left. rewrite PTree.gso; auto.
    + rewrite WB in CHK. apply Pos.eqb_neq in NEB. rewrite NEB in CHK. simpl in CHK.
      apply negb_true_iff in CHK.
      set (tle1 := PTree.set (sp_idx sx) wi tle).
      exists (PTree.set (sp_base sx) wb tle1). split.
      * eapply plus_left. apply step_seq.
        eapply star_left. apply step_set. constructor. eauto.
        eapply star_left. apply step_skip_seq.
        eapply star_one. apply step_set. constructor. unfold tle1. rewrite PTree.gso; auto.
        all: reflexivity.
      * eapply match_temps_kill_split with (L := L); eauto.
        -- intros y Y1 Y2. unfold tle1. rewrite !PTree.gso; auto.
        -- rewrite PTree.gss. discriminate.
        -- unfold tle1. rewrite PTree.gso, PTree.gss; auto; discriminate.
        -- apply REL. apply PTree.gss. unfold tle1. rewrite PTree.gso, PTree.gss; auto.
        -- right. intros. eapply clash_false; eauto.
  - (* x = q +/- n: update the index from q's, and the base unless shared *)
    left.
    assert (TA: tr_expr ce sps nil nil a = Ebinop Oadd (base_of sq) (index_expr sq sub si (tr_expr ce sps nil nil n)) (typeof a))
      by (eapply offset_of_tr; eauto).
    assert (BS: bare_split sps a = false).
    { unfold offset_of in OF. destruct a; try discriminate. auto. }
    assert (EV': eval_expr tge e tle m (tr_expr ce sps nil nil a) v) by (eapply tr_eval; eauto; congruence).
    rewrite TA in EV'. destruct (so_shape _ _ _ SO _ _ SQ) as (t & ta & T & SZq).
    unfold base_of in EV'. rewrite T in EV'.
    destruct (eval_base_index_inv _ _ _ _ _ _ _ _ _ _ EV' eq_refl) as (bv & iv & B & I & AT).
    rewrite CENV in AT. change (genv_cenv ge) with ce in AT. rewrite <- SZq, SZ in AT.
    destruct (peq x q).
    + subst q. rewrite SX in SQ. inv SQ.
      exists (PTree.set (sp_idx sq) (Vlong iv) tle). split.
      * apply plus_one. apply step_set. auto.
      * eapply match_temps_kill_split with (L := L); eauto.
        -- intros y Y1 Y2. rewrite PTree.gso; auto.
        -- rewrite PTree.gso; auto.
        -- rewrite PTree.gss. discriminate.
        -- intros _. exists bv, iv. rewrite PTree.gso, PTree.gss; auto.
        -- left. rewrite PTree.gso; auto.
    + assert (I1: sp_base sq <> sp_idx sx) by (intro Q; exact (so_idx_base _ _ _ SO _ _ _ _ SX SQ (eq_sym Q))).
      unfold copy_base. destruct (peq (sp_base sx) (sp_base sq)) as [EB | NEB].
      * exists (PTree.set (sp_idx sx) (Vlong iv) tle). split.
        -- apply plus_one. apply step_set. auto.
        -- eapply match_temps_kill_split with (L := L); eauto.
           ++ intros y Y1 Y2. rewrite PTree.gso; auto.
           ++ rewrite PTree.gso; auto.
           ++ rewrite PTree.gss. discriminate.
           ++ intros _. exists bv, iv. rewrite PTree.gso, PTree.gss, EB; auto.
           ++ left. rewrite PTree.gso; auto.
      * rewrite WB in CHK. apply Pos.eqb_neq in NEB. rewrite NEB in CHK. simpl in CHK.
        apply negb_true_iff in CHK.
        set (tle1 := PTree.set (sp_idx sx) (Vlong iv) tle).
        exists (PTree.set (sp_base sx) bv tle1). split.
        -- eapply plus_left. apply step_seq.
           eapply star_left. apply step_set. eauto.
           eapply star_left. apply step_skip_seq.
           eapply star_one. apply step_set. unfold base_of. constructor. unfold tle1. rewrite PTree.gso; auto.
           all: reflexivity.
        -- eapply match_temps_kill_split with (L := L); eauto.
           ++ intros y Y1 Y2. unfold tle1. rewrite !PTree.gso; auto.
           ++ rewrite PTree.gss. discriminate.
           ++ unfold tle1. rewrite PTree.gso, PTree.gss; auto; discriminate.
           ++ intros _. exists bv, iv. unfold tle1. rewrite PTree.gss, PTree.gso, PTree.gss; auto.
           ++ right. intros. eapply clash_false; eauto.
  - (* anything else: a new base, at index 0 *)
    left. rewrite WB in CHK. simpl in CHK. apply negb_true_iff in CHK.
    assert (BS: bare_split sps a = false).
    { unfold copy_ok in CP. unfold bare_split. destruct a; auto. rewrite SX in CP.
      destruct (sps!i) as [sq | ] eqn:SQ; auto. exfalso. apply (NB i t sq eq_refl SQ).
      symmetry. apply Z.eqb_eq; auto. }
    exists (PTree.set (sp_idx sx) (Vlong Int64.zero) (PTree.set (sp_base sx) v tle)). split.
    + eapply plus_left. apply step_seq.
      eapply star_left. apply step_set. eapply tr_eval; eauto. congruence.
      eapply star_left. apply step_skip_seq.
      eapply star_one. apply step_set. constructor.
      all: reflexivity.
    + eapply match_temps_kill_split with (L := L); eauto.
      * intros y Y1 Y2. rewrite !PTree.gso; auto.
      * rewrite PTree.gso, PTree.gss; auto. discriminate.
      * rewrite PTree.gss. discriminate.
      * intros P. exists v, Int64.zero. rewrite PTree.gss, PTree.gso, PTree.gss; auto.
        split; auto. split; auto. apply at_index_zero; auto.
      * right. intros. eapply clash_false; eauto.
Qed.

(** *** Labels *)

Lemma find_label_live: forall f sps labs lbl,
  (forall s k ts tk A B C L, tr2 ce sps s = Some ts -> stmt_ok f sps s -> LC ce sps labs s A B C = (L, true) ->
     match_cont f sps labs k tk A B C ->
     match find_label lbl s k with
     | Some (s', k') => exists ts' tk' A' B' C' L', find_label lbl ts tk = Some (ts', tk')
           /\ tr2 ce sps s' = Some ts' /\ stmt_ok f sps s' /\ LC ce sps labs s' A' B' C' = (L', true)
           /\ subset L' (lab labs lbl) = true /\ match_cont f sps labs k' tk' A' B' C'
     | None => find_label lbl ts tk = None
     end)
  /\ (forall ls k tls tk A C l all, tr2_l ce sps ls = Some tls ->
     body_ok_l sps (fn_return f) ls = true -> lstmt_le (max_function f) ls ->
     LCL ce sps labs ls A C = (l, all, true) -> match_cont f sps labs k tk A A C ->
     match find_label_ls lbl ls k with
     | Some (s', k') => exists ts' tk' A' B' C' L', find_label_ls lbl tls tk = Some (ts', tk')
           /\ tr2 ce sps s' = Some ts' /\ stmt_ok f sps s' /\ LC ce sps labs s' A' B' C' = (L', true)
           /\ subset L' (lab labs lbl) = true /\ match_cont f sps labs k' tk' A' B' C'
     | None => find_label_ls lbl tls tk = None
     end).
Proof.
  intros f sps labs lbl. apply statement_lstmt_ind; intros; try rewrite tr2_switch_eq in *; try rewrite tr2_lcons_eq in *;
  cbn [tr2 tr2_l] in *;
  try (inv H; reflexivity); try (inv H0; reflexivity).
  - (* set *) simpl. eapply find_label_tr_set; eauto.
  - (* call *) inv H. simpl. apply find_label_with_result. auto.
  - (* builtin *) inv H. simpl. apply find_label_with_result. auto.
  - (* sequence *)
    destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s0) as [t2|] eqn:T2; try discriminate. inv H1.
    destruct H2 as [BO [L1 L2]]. simpl in BO. apply andb_true_iff in BO. destruct BO as [B1 B2].
    destruct (LC_seq _ _ _ _ _ _ _ _ _ H3) as (l2 & E2 & E1).
    assert (MC2: match_cont f sps labs (Kseq s0 k) (Kseq t2 tk) l2 B C) by (econstructor; eauto; split; auto).
    specialize (H _ _ _ _ _ _ _ eq_refl (conj B1 L1) E1 MC2). simpl.
    destruct (find_label lbl s (Kseq s0 k)) as [[s' k'] | ].
    + destruct H as (ts' & tk' & A' & B' & C' & L' & F & R). rewrite F. exists ts', tk', A', B', C', L'. auto.
    + rewrite H. eapply H0; eauto. split; auto.
  - (* if *)
    destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s0) as [t2|] eqn:T2; try discriminate. inv H1.
    destruct H2 as [BO [_ [L1 L2]]]. simpl in BO. rewrite !andb_true_iff in BO. destruct BO as [[_ B1] B2].
    destruct (LC_if _ _ _ _ _ _ _ _ _ _ H3) as (l1 & l2 & E1 & E2 & EL).
    specialize (H _ _ _ _ _ _ _ eq_refl (conj B1 L1) E1 H4). simpl.
    destruct (find_label lbl s k) as [[s' k'] | ].
    + destruct H as (ts' & tk' & A' & B' & C' & L' & F & R). rewrite F. exists ts', tk', A', B', C', L'. auto.
    + rewrite H. eapply H0; eauto. split; auto.
  - (* loop *)
    destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s0) as [t2|] eqn:T2; try discriminate. inv H1.
    destruct H2 as [BO [L1 L2]]. simpl in BO. apply andb_true_iff in BO. destruct BO as [B1 B2].
    destruct (LC_loop _ _ _ _ _ _ _ _ _ H3) as (l2 & l1 & E2 & E1 & SUB).
    assert (MC1: match_cont f sps labs (Kloop1 s s0 k) (Kloop1 t1 t2 tk) l2 A l2)
      by (econstructor; eauto; split; auto).
    assert (MC2: match_cont f sps labs (Kloop2 s s0 k) (Kloop2 t1 t2 tk) L A L)
      by (econstructor; eauto; split; auto).
    specialize (H _ _ _ _ _ _ _ eq_refl (conj B1 L1) E1 MC1). simpl.
    destruct (find_label lbl s (Kloop1 s s0 k)) as [[s' k'] | ].
    + destruct H as (ts' & tk' & A' & B' & C' & L' & F & R). rewrite F. exists ts', tk', A', B', C', L'. auto.
    + rewrite H. eapply H0; eauto. split; auto.
  - (* return *) destruct o; inv H; reflexivity.
  - (* switch *)
    destruct (tr2_l ce sps l) as [tl|] eqn:TL; try discriminate. inv H0.
    destruct H1 as [BO [_ LL]]. simpl in BO. apply andb_true_iff in BO. destruct BO as [_ BO].
    destruct (LC_switch _ _ _ _ _ _ _ _ _ H2) as (l1 & all & E & EL).
    simpl. eapply (H _ _ _ A C l1 all eq_refl); eauto. econstructor; eauto.
  - (* label *)
    destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate. inv H0.
    destruct H1 as [BO [_ LL]]. simpl in BO. simpl.
    destruct (LC_label _ _ _ _ _ _ _ _ _ H2) as [E SUB].
    destruct (ident_eq lbl l).
    + subst l. exists t1, tk, A, B, C, L. repeat split; auto.
    + eapply H; eauto. split; auto.
  - (* LScons *)
    destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate.
    destruct (tr2_l ce sps l) as [tl|] eqn:TL; try discriminate. inv H1.
    simpl in H2. apply andb_true_iff in H2. destruct H2 as [B1 B2]. destruct H3 as [L1 L2].
    destruct (LCL_cons _ _ _ _ _ _ _ _ _ _ H4) as (lr & all' & E1 & E2 & E3).
    assert (MC2: match_cont f sps labs (Kseq (seq_of_labeled_statement l) k) (Kseq (seq_of_labeled_statement tl) tk) lr A C).
    { econstructor; eauto. apply tr2_seq_of_ls; auto. split. apply body_ok_seq_of_ls; auto.
      apply bounded_seq_of_ls; auto. eapply LCL_seq; eauto. }
    specialize (H _ _ _ _ _ _ _ eq_refl (conj B1 L1) E2 MC2). simpl.
    destruct (find_label lbl s (Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
    + destruct H as (ts' & tk' & A' & B' & C' & L' & F & R). rewrite F. exists ts', tk', A', B', C', L'. auto.
    + rewrite H. eapply H0; eauto.
Qed.

(** *** Statements *)

Lemma tr_lv_typeof_ce: forall sps a, typeof (tr_lv ce sps nil nil a) = typeof a.
Proof. intros. destruct a; reflexivity. Qed.

Ltac sok := split; simpl; auto.

(** Live sets: what a statement reads is live before it. *)
Ltac kill_ok :=
  let yy := fresh "y" in let TT := fresh "T" in let OO := fresh "O" in
  intros yy TT OO;
  rewrite ?lmem_lu, ?lmem_lus; rewrite ?TT, ?OO; simpl; rewrite ?orb_true_r; auto;
  rewrite ?lmem_lunion, ?lmem_lkill, ?lmem_kill_opt; rewrite ?TT, ?OO; simpl; rewrite ?orb_true_r; auto.

Lemma stmt_ok_seq: forall f sps s1 s2, stmt_ok f sps (Ssequence s1 s2) <-> stmt_ok f sps s1 /\ stmt_ok f sps s2.
Proof.
  unfold stmt_ok, bounded; intros; simpl. rewrite andb_true_iff. tauto.
Qed.

Lemma stmt_ok_loop: forall f sps s1 s2, stmt_ok f sps (Sloop s1 s2) <-> stmt_ok f sps s1 /\ stmt_ok f sps s2.
Proof.
  unfold stmt_ok, bounded; intros; simpl. rewrite andb_true_iff. tauto.
Qed.

Lemma stmt_ok_if: forall f sps a s1 s2, stmt_ok f sps (Sifthenelse a s1 s2) ->
  uses_ok sps a = true /\ stmt_ok f sps s1 /\ stmt_ok f sps s2.
Proof.
  unfold stmt_ok, bounded; intros; simpl in *. rewrite !andb_true_iff in H. tauto.
Qed.

Lemma tr2_loop: forall sps s1 s2 ts1 ts2,
  tr2 ce sps s1 = Some ts1 -> tr2 ce sps s2 = Some ts2 -> tr2 ce sps (Sloop s1 s2) = Some (Sloop ts1 ts2).
Proof.
  intros. simpl. rewrite H, H0. auto.
Qed.

Lemma assign_loc_void: forall ce m b ofs bf v m', ~ assign_loc ce Tvoid m b ofs bf v m'.
Proof.
  intros; intro A. inv A; try discriminate.
  match goal with H: store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ => inv H end.
Qed.

Lemma result_clash: forall sps x sx A, result_ok sps (Some x) A = true -> sps!x = Some sx -> clash sps x A = false.
Proof.
  unfold result_ok; intros. rewrite H0 in H. apply negb_true_iff; auto.
Qed.

Lemma lcheck_entry: forall sps labs body,
  snd (LC ce sps labs body nil nil nil) = true -> exists L, LC ce sps labs body nil nil nil = (L, true).
Proof.
  intros. destruct (LC ce sps labs body nil nil nil) as [L ok]. simpl in H. subst. eauto.
Qed.

Definition dummy_function := mkfunction Tvoid cc_default nil nil nil Sskip.

Theorem step_simulation:
  forall S1 t S2, step2 ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  (exists S2', plus step2 tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros S1' MS; inv MS.
  - (* assign *)
    simpl in TS. inv TS. destruct OK as [BO _]. simpl in BO. apply andb_true_iff in BO. destruct BO as [U1 U2].
    unfold LC in LV; cbn [lcheck] in LV. injection LV as EL. subst L.
    left. eexists; split.
    + apply plus_one. eapply step_assign.
      * eapply tr_eval_lvalue; eauto. apply eval_lvalue_kill; [eauto | kill_ok].
      * eapply tr_eval; eauto. apply eval_kill; [eauto | kill_ok].
        intros BS. destruct (bare_pointer _ _ U2 BS) as (t & ta & T). rewrite T in H1.
        eapply cast_ptr; eauto. intro V. rewrite V in H2. eapply assign_loc_void; eauto.
      * rewrite tr_expr_typeof_ce, tr_lv_typeof_ce. eauto.
      * rewrite tr_lv_typeof_ce. apply assign_loc_preserved; eauto.
    + assert (MT': match_temps sps (max_function f) (kill (shared_tree sps) A le) tle)
        by (eapply match_temps_kill; eauto; kill_ok).
      econstructor; eauto; try sok.
  - (* set *)
    simpl in TS. destruct OK as [BO BL]. simpl in BO, BL. apply andb_true_iff in BO. destruct BO as [U CP].
    destruct BL as [XT _].
    unfold LC in LV; cbn [lcheck] in LV. injection LV as EL CHK. subst L.
    destruct (sset_sim f sps labs tf tk e le tle m id a v ts A TRF MT) as [(tle' & P & MT') | (TS0 & MT')]; auto.
    { destruct (sps!id); auto. }
    + left. exists (State tf Sskip tk e tle' m). split; auto. econstructor; eauto; try sok.
    + right. subst ts. split. simpl; lia. split; auto. econstructor; eauto; try sok.
  - (* call *)
    simpl in TS. inv TS. destruct OK as [BO BL]. simpl in BO, BL. apply andb_true_iff in BO. destruct BO as [U CA].
    destruct BL as [OL _].
    unfold call_args_ok in CA. rewrite H in CA.
    unfold LC in LV; cbn [lcheck] in LV. injection LV as EL RO. subst L.
    destruct (functions_translated share prog _ _ H2) as (tfd & FT & MF).
    assert (EVA: eval_expr tge e tle m (tr_expr ce sps nil nil a) vf).
    { eapply tr_eval; eauto. apply eval_kill; [eauto | kill_ok]. intros _. eapply find_funct_ptrish; eauto. }
    assert (EVL: eval_exprlist tge e tle m (map (tr_expr ce sps nil nil) al) tyargs vargs).
    { eapply tr_eval_list; eauto. apply eval_exprlist_kill; [eauto | kill_ok]. }
    assert (CF: classify_fun (typeof (tr_expr ce sps nil nil a)) = fun_case_f tyargs tyres cconv)
      by (rewrite tr_expr_typeof_ce; auto).
    assert (TY: type_of_fundef tfd = Tfunction tyargs tyres cconv)
      by (rewrite (type_of_fundef_preserved share prog _ _ MF); auto).
    assert (MT': match_temps sps (max_function f) (kill (shared_tree sps) (kill_opt optid A) le) tle)
      by (eapply match_temps_kill; eauto; kill_ok).
    left. unfold with_result. destruct optid as [x | ]; [destruct (sps!x) as [sx | ] eqn:SX | ].
    + (* the result is split: the call returns into its base *)
      eexists; split.
      * eapply plus_left. apply step_seq. apply star_one. eapply step_call; eauto. reflexivity.
      * apply ms_call with (f := f) (sps := sps) (labs := labs) (A := A) (B := B) (C := C); [exact MF | | exact I].
        eapply mc_call'; eauto; simpl; rewrite SX; auto.
    + eexists; split.
      * apply plus_one. eapply step_call; eauto.
      * apply ms_call with (f := f) (sps := sps) (labs := labs) (A := A) (B := B) (C := C); [exact MF | | exact I].
        eapply mc_call'; eauto; simpl; rewrite SX; auto.
    + eexists; split.
      * apply plus_one. eapply step_call; eauto.
      * apply ms_call with (f := f) (sps := sps) (labs := labs) (A := A) (B := B) (C := C); [exact MF | | exact I].
        eapply mc_call'; eauto.
  - (* builtin *)
    simpl in TS. inv TS. destruct OK as [BO BL]. simpl in BO, BL. destruct BL as [OL _].
    unfold LC in LV; cbn [lcheck] in LV. injection LV as EL RO. subst L.
    pose proof (tf_splits _ _ _ _ _ TRF) as SO.
    assert (EVL: eval_exprlist tge e tle m (map (tr_expr ce sps nil nil) al) tyargs vargs).
    { eapply tr_eval_list; eauto. apply eval_exprlist_kill; [eauto | kill_ok]. }
    assert (EC: external_call ef tge vargs m t vres m')
      by (eapply external_call_symbols_preserved; eauto; apply senv_preserved).
    assert (MT1: match_temps sps (max_function f) (kill (shared_tree sps) (kill_opt optid A) le) tle)
      by (eapply match_temps_kill; eauto; kill_ok).
    left. unfold with_result. destruct optid as [x | ]; [destruct (sps!x) as [sx | ] eqn:SX | ].
    + (* the result is split: its base, at index 0 *)
      assert (BX: sp_idx sx <> sp_base sx) by (eapply (so_idx_base _ _ _ SO); eauto).
      eexists; split.
      * eapply plus_four.
        apply step_seq. eapply step_builtin; eauto. apply step_skip_seq. apply step_set. constructor.
        traceEq.
      * assert (MT': match_temps sps (max_function f) (kill (shared_tree sps) A (set_opttemp (Some x) vres le))
                       (PTree.set (sp_idx sx) (Vlong Int64.zero) (PTree.set (sp_base sx) vres tle))).
        { simpl. eapply match_temps_kill_split with (L := lkill x A); eauto.
          - intros y T M N. rewrite lmem_lkill, M. destruct (Pos.eqb x y) eqn:E; auto.
            apply Pos.eqb_eq in E. congruence.
          - intros y Y1 Y2. rewrite !PTree.gso; auto.
          - rewrite PTree.gso, PTree.gss; auto; discriminate.
          - rewrite PTree.gss; discriminate.
          - intros P. exists vres, Int64.zero. rewrite PTree.gss, PTree.gso, PTree.gss; auto.
            split; auto. split; auto. apply at_index_zero; auto.
          - right. intros y sy N S EB. apply (clash_false sps x sx A y sy); auto. eapply result_clash; eauto. }
        econstructor; eauto; try sok.
    + eexists; split.
      * apply plus_one. eapply step_builtin; eauto.
      * assert (MT': match_temps sps (max_function f) (kill (shared_tree sps) A (set_opttemp (Some x) vres le))
                       (PTree.set x vres tle)).
        { simpl. eapply match_temps_kill_unsplit with (L := lkill x A); eauto.
          intros y T M N. rewrite lmem_lkill, M. destruct (Pos.eqb x y) eqn:E; auto.
          apply Pos.eqb_eq in E. congruence. }
        econstructor; eauto; try sok.
    + eexists; split.
      * apply plus_one. eapply step_builtin; eauto.
      * econstructor; eauto; try sok.
  - (* sequence *)
    simpl in TS. destruct (tr2 ce sps s1) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s2) as [t2|] eqn:T2; try discriminate. inv TS.
    apply stmt_ok_seq in OK. destruct OK as [OK1 OK2].
    destruct (LC_seq _ _ _ _ _ _ _ _ _ LV) as (l2 & E2 & E1).
    left. eexists; split. apply plus_one. apply step_seq. econstructor; eauto. econstructor; eauto.
  - (* skip, Kseq *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_skip_seq. econstructor; eauto.
  - (* continue, Kseq *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_continue_seq.
    econstructor; eauto; try sok.
  - (* break, Kseq *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_break_seq.
    econstructor; eauto; try sok.
  - (* if *)
    simpl in TS. destruct (tr2 ce sps s1) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s2) as [t2|] eqn:T2; try discriminate. inv TS.
    destruct (stmt_ok_if _ _ _ _ _ OK) as (U & OK1 & OK2).
    destruct (LC_if _ _ _ _ _ _ _ _ _ _ LV) as (l1 & l2 & E1 & E2 & EL). subst L.
    left. eexists; split.
    + apply plus_one. eapply step_ifthenelse.
      * eapply tr_eval; eauto. apply eval_kill; [eauto | kill_ok].
        intros BS. destruct (bare_pointer _ _ U BS) as (t & ta & T). rewrite T in H0.
        eapply bool_val_ptr; eauto.
      * rewrite tr_expr_typeof_ce. eauto.
    + destruct b; econstructor; eauto; eapply match_temps_kill; eauto; kill_ok.
  - (* loop *)
    simpl in TS. destruct (tr2 ce sps s1) as [t1|] eqn:T1; try discriminate.
    destruct (tr2 ce sps s2) as [t2|] eqn:T2; try discriminate. inv TS.
    pose proof OK as OK'. apply stmt_ok_loop in OK'. destruct OK' as [OK1 OK2].
    destruct (LC_loop _ _ _ _ _ _ _ _ _ LV) as (l2 & l1 & E2 & E1 & SUB).
    left. eexists; split. apply plus_one. apply step_loop.
    econstructor; eauto.
    + eapply match_temps_kill; eauto. intros. eapply subset_lmem; eauto.
    + econstructor; eauto.
  - (* skip or continue, Kloop1 *)
    inv MC. destruct H as [X | X]; subst x; simpl in TS; inv TS; unfold LC in LV; cbn [lcheck] in LV; inv LV;
    (left; eexists; split; [apply plus_one; apply step_skip_or_continue_loop1; auto
                           | econstructor; eauto; econstructor; eauto]).
  - (* break, Kloop1 *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_break_loop1.
    econstructor; eauto; try sok.
  - (* skip, Kloop2 *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_skip_loop2.
    econstructor; eauto. apply tr2_loop; auto. apply stmt_ok_loop; auto.
  - (* break, Kloop2 *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_break_loop2.
    econstructor; eauto; try sok.
  - (* return *)
    simpl in TS. inv TS. destruct (match_cont_call_cont _ _ _ _ _ _ _ _ MC) as (f' & sps' & labs' & MC').
    left. eexists; split.
    + apply plus_one. apply step_return_0. rewrite blocks_of_env_preserved; eauto.
    + econstructor; eauto. eapply match_cont_call_cont_is; eauto.
  - (* return a *)
    simpl in TS. inv TS. destruct OK as [BO _]. simpl in BO. unfold received_ok in BO.
    apply andb_true_iff in BO. destruct BO as [U NV].
    unfold LC in LV; cbn [lcheck] in LV. injection LV as EL. subst L.
    destruct (match_cont_call_cont _ _ _ _ _ _ _ _ MC) as (f' & sps' & labs' & MC').
    left. eexists; split.
    + apply plus_one. eapply step_return_1.
      * eapply tr_eval; eauto. apply eval_kill; [eauto | kill_ok].
        intros BS. destruct (bare_pointer _ _ U BS) as (t & ta & T). rewrite T in H0.
        eapply cast_ptr; eauto. intro V. rewrite V, BS in NV. discriminate.
      * rewrite tr_expr_typeof_ce, (tf_return _ _ _ _ _ TRF). eauto.
      * rewrite blocks_of_env_preserved; eauto.
    + econstructor; eauto. eapply match_cont_call_cont_is; eauto.
  - (* skip at the end of a function *)
    simpl in TS. inv TS. left. eexists; split.
    + apply plus_one. apply step_skip_call. eapply match_cont_is_call_cont; eauto.
      rewrite blocks_of_env_preserved; eauto.
    + econstructor; eauto.
  - (* switch *)
    rewrite tr2_switch_eq in TS. destruct (tr2_l ce sps sl) as [tsl|] eqn:TL; try discriminate. inv TS.
    destruct OK as [BO BL]. simpl in BO, BL. apply andb_true_iff in BO. destruct BO as [U BOL]. destruct BL as [_ LL].
    destruct (LC_switch _ _ _ _ _ _ _ _ _ LV) as (l1 & all & E & EL). subst L.
    destruct (LCL_select _ _ _ n _ _ _ _ _ E) as (l' & all' & E' & SUBS).
    left. eexists; split.
    + apply plus_one. eapply step_switch.
      * eapply tr_eval; eauto. apply eval_kill; [eauto | kill_ok].
        intros BS. destruct (bare_pointer _ _ U BS) as (t & ta & T). rewrite T in H0.
        simpl in H0. discriminate.
      * rewrite tr_expr_typeof_ce; eauto.
    + apply ms_regular with (sps := sps) (labs := labs) (A := A) (B := A) (C := C) (L := l'); auto.
      * apply tr2_seq_of_ls. apply tr2_select_switch; auto.
      * split. apply body_ok_seq_of_ls. apply body_ok_select_switch; auto.
        apply bounded_seq_of_ls. apply bounded_select_switch; auto.
      * eapply LCL_seq; eauto.
      * eapply match_temps_kill; eauto. intros y T M. rewrite lmem_lu, lmem_lunion, (SUBS y M). simpl.
        rewrite orb_true_r. auto.
      * econstructor; eauto.
  - (* skip or break, Kswitch *)
    inv MC. destruct H as [X | X]; subst x; simpl in TS; inv TS; unfold LC in LV; cbn [lcheck] in LV; inv LV;
    (left; eexists; split; [apply plus_one; apply step_skip_break_switch; auto | econstructor; eauto; try sok]).
  - (* continue, Kswitch *)
    inv MC. simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    left. eexists; split. apply plus_one. apply step_continue_switch.
    econstructor; eauto; try sok.
  - (* label *)
    simpl in TS. destruct (tr2 ce sps s) as [t1|] eqn:T1; try discriminate. inv TS.
    destruct OK as [BO BL]. simpl in BO, BL. destruct BL as [_ BL].
    destruct (LC_label _ _ _ _ _ _ _ _ _ LV) as [E SUB].
    left. eexists; split. apply plus_one. apply step_label. econstructor; eauto. split; auto.
  - (* goto *)
    simpl in TS. inv TS. unfold LC in LV; cbn [lcheck] in LV. inv LV.
    destruct (tf_body _ _ _ _ _ TRF) as (body' & TB & FB).
    destruct (lcheck_entry _ _ _ (tf_live _ _ _ _ _ TRF)) as (L0 & LB).
    destruct (match_cont_call_cont _ _ _ _ _ _ _ _ MC) as (f' & sps' & labs' & MC').
    assert (MC'': match_cont f sps labs (call_cont k) (call_cont tk) nil nil nil).
    { eapply match_cont_change; eauto. eapply match_cont_call_cont_is; eauto. }
    pose proof (proj1 (find_label_live f sps labs lbl) (fn_body f) (call_cont k) body' (call_cont tk) _ _ _ _ TB
                  (conj (tf_ok _ _ _ _ _ TRF) (bounded_body f)) LB MC'') as FL.
    rewrite H in FL. destruct FL as (ts' & tk' & A' & B' & C' & L' & FL & TS' & OK' & LV' & SUB & MC2).
    left. eexists; split.
    + apply plus_one. apply step_goto. rewrite FB, find_label_sseq. eauto. intros; apply find_label_entry.
    + econstructor; eauto. eapply match_temps_kill; eauto. intros. eapply subset_lmem; eauto.
  - (* internal function *)
    inv MF. match goal with H: transf_function _ _ _ _ _ _ = _ |- _ =>
      destruct (transf_function_tr _ _ _ _ _ _ _ _ _ _ H) as (sps' & labs' & TRF) end.
    destruct (entry_sim _ _ _ _ _ _ _ _ _ tk TRF H) as (body' & tle & TB & P & MT).
    destruct (lcheck_entry _ _ _ (tf_live _ _ _ _ _ TRF)) as (L0 & LB).
    left. eexists; split.
    + eexact P.
    + econstructor; eauto.
      * split. apply (tf_ok _ _ _ _ _ TRF). apply bounded_body.
      * eapply match_temps_kill_full; eauto.
      * eapply match_cont_change; eauto.
  - (* external function *)
    inv MF. left. eexists; split.
    + apply plus_one. apply step_external_function.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + econstructor; eauto.
  - (* return to the caller *)
    inv MC. match goal with H: tr_function _ _ _ _ _ |- _ => rename H into TRF end.
    pose proof (tf_splits _ _ _ _ _ TRF) as SO.
    destruct optid as [x | ]; [destruct (sps'!x) as [sx | ] eqn:SX | ]; unfold dst, fixup; try rewrite SX.
    + (* a split result: its base, then its index is zeroed *)
      assert (BX: sp_idx sx <> sp_base sx) by (eapply (so_idx_base _ _ _ SO); eauto).
      left. eexists; split.
      * eapply plus_three. apply step_returnstate. apply step_skip_seq. apply step_set. constructor.
        reflexivity.
      * assert (MT': match_temps sps' (max_function f) (kill (shared_tree sps') A' (set_opttemp (Some x) v le))
                       (PTree.set (sp_idx sx) (Vlong Int64.zero) (PTree.set (sp_base sx) v tle))).
        { simpl. eapply match_temps_kill_split with (L := lkill x A'); eauto.
          - intros y T M N. rewrite lmem_lkill, M. destruct (Pos.eqb x y) eqn:E; auto.
            apply Pos.eqb_eq in E. congruence.
          - intros y Y1 Y2. rewrite !PTree.gso; auto.
          - rewrite PTree.gso, PTree.gss; auto; discriminate.
          - rewrite PTree.gss; discriminate.
          - intros P. exists v, Int64.zero. rewrite PTree.gss, PTree.gso, PTree.gss; auto.
            split; auto. split; auto. apply at_index_zero; auto.
          - right. intros y sy N S EB. apply (clash_false sps' x sx A' y sy); auto. eapply result_clash; eauto. }
        econstructor; eauto; try sok.
    + left. eexists; split.
      * apply plus_one. apply step_returnstate.
      * assert (MT': match_temps sps' (max_function f) (kill (shared_tree sps') A' (set_opttemp (Some x) v le))
                       (PTree.set x v tle)).
        { simpl. eapply match_temps_kill_unsplit with (L := lkill x A'); eauto.
          intros y T M N. rewrite lmem_lkill, M. destruct (Pos.eqb x y) eqn:E; auto.
          apply Pos.eqb_eq in E. congruence. }
        econstructor; eauto; try sok.
    + left. eexists; split.
      * apply plus_one. apply step_returnstate.
      * econstructor; eauto; try sok.
Qed.

Lemma transf_initial_states: forall S1, Clight.initial_state prog S1 ->
  exists S2, Clight.initial_state tp S2 /\ match_states S1 S2.
Proof.
  intros. inv H.
  destruct (function_ptr_translated share prog _ _ H2) as (tf & FT & MF).
  exists (Callstate tf nil Kstop m0); split.
  - econstructor.
    + apply (Genv.init_mem_match (tprog_match share prog)); auto.
    + replace (prog_main tp) with (prog_main prog).
      * transitivity (Genv.find_symbol (Genv.globalenv prog) (prog_main prog)); eauto.
        exact (symbols_preserved share prog _).
      * symmetry. exact (Linking.match_program_main (tprog_match share prog)).
    + eauto.
    + rewrite (type_of_fundef_preserved share prog _ _ MF). auto.
  - apply ms_call with (f := dummy_function) (sps := PTree.empty split) (labs := PTree.empty lset)
                       (A := nil) (B := nil) (C := nil); auto.
    constructor. exact I.
Qed.

Lemma transf_final_states: forall S1 S2 r,
  match_states S1 S2 -> Clight.final_state S1 r -> Clight.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv MC. constructor.
Qed.

(** The rewriting without caches preserves the semantics, with or without
    shared bases. *)
Theorem transf_program_correct_nocache:
  forward_simulation (semantics2 prog) (semantics2 tp).
Proof.
  eapply forward_simulation_star with (measure := measure).
  - apply senv_preserved.
  - apply transf_initial_states.
  - apply transf_final_states.
  - apply step_simulation.
Qed.

End SIMULATION.

(** * The theorem

    [transf_program] (shared bases, no caches) preserves the semantics of
    every Clight program, in the form CompCert states it for its own passes:
    a forward simulation, so every execution of the original program is
    matched by an execution of the rewritten one with the same trace and
    result. *)
Theorem transf_program_correct: forall p tp,
  transf_program p = OK tp -> forward_simulation (semantics2 p) (semantics2 tp).
Proof.
  unfold transf_program; intros. inv H. exact (transf_program_correct_nocache true p).
Qed.
