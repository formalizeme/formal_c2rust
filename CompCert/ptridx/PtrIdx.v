(** * Pointer arithmetic -> base + index, on Clight

    Two kinds of pointer are rewritten.

    Pointer temporaries. A pointer temporary whose value moves (some statement
    assigns it [q + n] or [q - n]) is split, together with every pointer
    temporary it is copied to or from, into a base temporary and a [long]
    index temporary:
<<
      p = q + n     becomes   p_idx = q_idx + (long) n;  p_base = q_base
      p = q         becomes   p_idx = q_idx;  p_base = q_base
      p = e         becomes   p_base = e;  p_idx = 0          (any other e)
      p + n         becomes   p_base + (p_idx + (long) n)
      any other p   becomes   p_base + p_idx
>>
    The value of [p] is therefore always [p_base + p_idx], computed exactly
    the way Clight computes pointer arithmetic.

    Pointers stored in memory, an extension that PtrIdxproof.v
    does not cover, used only when [mem] is set. A location [L] of pointer type (a
    struct field, a global, [*pp]) whose address depends only on temporaries,
    and that the function moves ([L = L + n]), gets a cache: temporaries
    [L_base] and [L_idx]. Memory is never changed: every store to [L] is
    still made (write-through), so the cache is only a second view of it.
<<
      L = L + n     becomes   L_idx = L_idx + (long) n;  L = L_base + L_idx
      L = e         becomes   L_base = (T) e;  L_idx = 0;  L = L_base
      a read of L   becomes   L_base + L_idx
>>
    The cache is valid while nothing can have changed [L]: a call to a
    function that may write memory, a store that may overlap [L], or a new
    value for a temporary in [L]'s address makes it stale. It is then reloaded
    before the next statement that uses [L]'s value, as [L_base = L - L_idx]:
    the index keeps counting, and if [L] did not change, the base is the same.
    [L_idx] starts at 0 when the function starts.

    Members of a group share one base temporary unless a member is rebased
    while another one is still live (a liveness analysis decides). The
    original pointer temporaries are no longer declared.

    [==], [!=] and pointer differences between two pointers with the same
    base temporary and 1-byte elements compare or subtract the indices;
    other comparisons use [base + idx]. Both are exact. Function signatures and memory
    layout are not changed. A function containing something these rules
    cannot express exactly is left unchanged. *)

Require Import Coqlib Maps Integers AST Errors Ctypes Cop Clight Builtins.

Definition tlong := Tlong Signed noattr.

(** How one pointer temporary is split. Its index counts in units of
    [sp_size], the size of what it points to. Members of a group whose base
    never changes share one base temporary. *)
Record split : Type := mksplit {
  sp_base: ident;
  sp_idx: ident;
  sp_type: type;
  sp_size: Z;
  sp_param: bool       (* the pointer is a function parameter *)
}.

Definition splits := PTree.t split.

(** ** Recognizing pointer arithmetic *)

Definition pointee (t: type) : option type :=
  match t with Tpointer t' _ => Some t' | _ => None end.

(** [q + n] or [q - n], where [q] is a temporary and [n] an integer. Returns
    [q], the type [q] has in the expression, [n], whether it subtracts, and
    how Clight widens [n] to 64 bits: [Some si] for an [int] (sign- or
    zero-extended), [None] for a [long]. *)
Definition offset_of (e: expr) : option (ident * type * expr * bool * option signedness) :=
  match e with
  | Ebinop Oadd (Etempvar q tq) n _ =>
      match classify_add tq (typeof n) with
      | add_case_pi _ si => Some (q, tq, n, false, Some si)
      | add_case_pl _ => Some (q, tq, n, false, None)
      | _ => None
      end
  | Ebinop Osub (Etempvar q tq) n _ =>
      match classify_sub tq (typeof n) with
      | sub_case_pi _ si => Some (q, tq, n, true, Some si)
      | sub_case_pl _ => Some (q, tq, n, true, None)
      | _ => None
      end
  | _ => None
  end.

(** ** Analysis: which pointer temporaries to split *)

(** Assignments between temporaries: [(p, q, true)] for [p = q +/- n],
    [(p, q, false)] for [p = q]. *)
Fixpoint edges_stmt (s: statement) (acc: list (ident * ident * bool)) : list (ident * ident * bool) :=
  match s with
  | Sset p (Etempvar q _) => (p, q, false) :: acc
  | Sset p e =>
      match offset_of e with
      | Some (q, _, _, _, _) => (p, q, true) :: acc
      | None => acc
      end
  | Ssequence s1 s2 | Sloop s1 s2 | Sifthenelse _ s1 s2 => edges_stmt s1 (edges_stmt s2 acc)
  | Slabel _ s1 => edges_stmt s1 acc
  | Sswitch _ ls => edges_lstmt ls acc
  | _ => acc
  end
with edges_lstmt (ls: labeled_statements) (acc: list (ident * ident * bool)) : list (ident * ident * bool) :=
  match ls with
  | LSnil => acc
  | LScons _ s ls' => edges_stmt s (edges_lstmt ls' acc)
  end.

(** Groups (connected components of the assignment edges), computed by
    label propagation: every temporary starts as its own label, and each
    pass lowers both ends of every edge to the smaller of their labels.
    The smallest label in a group spreads one edge per pass, so one pass per
    edge, plus one, is enough. *)
Definition label (r: PTree.t ident) (x: ident) : ident :=
  match r!x with Some y => y | None => x end.

Definition relax (r: PTree.t ident) (e: ident * ident * bool) : PTree.t ident :=
  let '(p, q, _) := e in
  let m := Pos.min (label r p) (label r q) in
  PTree.set p m (PTree.set q m r).

Fixpoint relax_n (n: nat) (es: list (ident * ident * bool)) (r: PTree.t ident) : PTree.t ident :=
  match n with
  | O => r
  | S n' => relax_n n' es (fold_left relax es r)
  end.

Definition is_some {A: Type} (o: option A) : bool :=
  match o with Some _ => true | None => false end.

Section ANALYSIS.

Variable ce: composite_env.

Definition elem_size (t: type) : Z :=
  match pointee t with Some t' => sizeof ce t' | None => 0 end.

(** Pointer temporaries that may be split, with their declared types.
    Parameters count: in Clight's [semantics2] they are temporaries. Only
    pointers to complete types qualify. Clight gives arithmetic on [void *] a
    meaning ([sizeof(void)] is 1), but CompCert's backend rejects it, and it
    is the wrong shape for a slice; a [void *] copied into a [char *] that then
    moves is a new base for the [char *]. *)
Definition splittable_temps (l: list (ident * type)) : PTree.t type :=
  fold_left (fun m (it: ident * type) =>
               match snd it with
               | Tpointer t' _ => if complete_type ce t' then PTree.set (fst it) (snd it) m else m
               | _ => m
               end)
            l (PTree.empty type).

(** Rebases: statements that give a member a value that is not a copy or
    offset of a member of the same group (exactly the assignments
    [set_split] turns into a new base), or a call result. [grp] maps each
    split temporary to its group, [gsize] each group to the size its members
    point to. *)
Section REBASED.

Variable grp: PTree.t ident.
Variable gsize: PTree.t Z.

Definition in_group (g q: ident) : bool :=
  match grp!q with Some g' => Pos.eqb g g' | None => false end.

Definition derived (g: ident) (e: expr) : bool :=
  match e with
  | Etempvar q _ => in_group g q
  | _ =>
      match offset_of e with
      | Some (q, tq, _, _, _) =>
          in_group g q && match gsize!g with Some z => Z.eqb (elem_size tq) z | None => false end
      | None => false
      end
  end.

(** Rebases per group: how many statements rebase a member, and the groups
    with a rebase inside a loop (it can run more than once). *)
Definition rebases := (PTree.t nat * PTree.t unit)%type.

Definition note (in_loop: bool) (g: ident) (acc: rebases) : rebases :=
  let '(counts, looped) := acc in
  (PTree.set g (S (match counts!g with Some k => k | None => O end)) counts,
   if in_loop then PTree.set g tt looped else looped).

Fixpoint rebases_stmt (in_loop: bool) (s: statement) (acc: rebases) : rebases :=
  match s with
  | Sset p e =>
      match grp!p with
      | Some g => if derived g e then acc else note in_loop g acc
      | None => acc
      end
  | Scall (Some p) _ _ | Sbuiltin (Some p) _ _ _ =>
      match grp!p with Some g => note in_loop g acc | None => acc end
  | Ssequence s1 s2 | Sifthenelse _ s1 s2 => rebases_stmt in_loop s1 (rebases_stmt in_loop s2 acc)
  | Sloop s1 s2 => rebases_stmt true s1 (rebases_stmt true s2 acc)
  | Slabel _ s1 => rebases_stmt in_loop s1 acc
  | Sswitch _ ls => rebases_lstmt in_loop ls acc
  | _ => acc
  end
with rebases_lstmt (in_loop: bool) (ls: labeled_statements) (acc: rebases) : rebases :=
  match ls with
  | LSnil => acc
  | LScons _ s ls' => rebases_stmt in_loop s (rebases_lstmt in_loop ls' acc)
  end.

(** *** Liveness of group members

    When a group shares one base, a rebase of member [p] ([G_base = e]) is
    exact only if no other member of the group still needs its value: its
    value is [G_base + q_idx], with the old base. So each rebase is checked
    against the members live after it. Only members are tracked. Loops and
    labels are fixpoints: the sets only grow, and are bounded by the members.
    A rebase found in conflict while the sets were still growing is also in
    conflict once they are complete, so conflicts are simply collected. *)

Definition lset := list ident.

Definition lmem (x: ident) (s: lset) : bool := existsb (Pos.eqb x) s.
Definition ladd (x: ident) (s: lset) : lset := if lmem x s then s else x :: s.
Definition lunion (a b: lset) : lset := fold_left (fun s x => ladd x s) a b.
Definition lkill (x: ident) (s: lset) : lset := filter (fun y => negb (Pos.eqb x y)) s.

Fixpoint luses (e: expr) (s: lset) : lset :=
  match e with
  | Etempvar x _ => if is_some grp!x then ladd x s else s
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ | Efield a _ _ => luses a s
  | Ebinop _ a1 a2 _ => luses a1 (luses a2 s)
  | _ => s
  end.

(** Member [p] gets a new base while [after] is live. *)
Definition conflict (p: ident) (after: lset) (conf: PTree.t unit) : PTree.t unit :=
  match grp!p with
  | Some g => if existsb (fun q => negb (Pos.eqb q p) && in_group g q) after then PTree.set g tt conf else conf
  | None => conf
  end.

Definition rebased_by_set (x: ident) (e: expr) : bool :=
  match grp!x with Some g => negb (derived g e) | None => false end.

Definition rebased_by_result (o: option ident) : option ident :=
  match o with Some x => if is_some grp!x then Some x else None | None => None end.

Definition kill_opt (o: option ident) (s: lset) : lset :=
  match o with Some x => lkill x s | None => s end.

(** What is collected: the members live at each label, and the groups with a
    conflicting rebase. *)
Definition lacc := (PTree.t lset * PTree.t unit)%type.

Definition note_conflict (p: option ident) (after: lset) (acc: lacc) : lacc :=
  match p with
  | Some x => let '(labs, conf) := acc in (labs, conflict x after conf)
  | None => acc
  end.

Variable members: lset.          (* every member: the fuel, and the answer when it runs out *)
Variable all_groups: PTree.t unit.

(** The members live before [s], given those live after it ends normally,
    by [break] and by [continue], and those live at each label ([labs], from
    the previous round). *)
Fixpoint live_stmt (labs: PTree.t lset) (s: statement) (after brk cont: lset) (acc: lacc) {struct s}
                   : lset * lacc :=
  match s with
  | Sskip => (after, acc)
  | Sassign a e => (luses a (luses e after), acc)
  | Sset x e =>
      let acc' := if rebased_by_set x e then note_conflict (Some x) after acc else acc in
      (luses e (lkill x after), acc')
  | Scall o f al =>
      (luses f (fold_right luses (kill_opt o after) al), note_conflict (rebased_by_result o) after acc)
  | Sbuiltin o _ _ al =>
      (fold_right luses (kill_opt o after) al, note_conflict (rebased_by_result o) after acc)
  | Ssequence s1 s2 =>
      let '(l2, acc) := live_stmt labs s2 after brk cont acc in
      live_stmt labs s1 l2 brk cont acc
  | Sifthenelse c s1 s2 =>
      let '(l1, acc) := live_stmt labs s1 after brk cont acc in
      let '(l2, acc) := live_stmt labs s2 after brk cont acc in
      (luses c (lunion l1 l2), acc)
  | Sloop s1 s2 =>
      (* [head]: live at the start of an iteration. [s1] ends into [s2], [s2]
         into the next iteration; [break] leaves the loop. *)
      let fix iter (n: nat) (head: lset) (acc: lacc) : lset * lacc :=
        let '(l2, acc) := live_stmt labs s2 head after head acc in
        let '(l1, acc) := live_stmt labs s1 l2 after l2 acc in
        let head' := lunion l1 head in
        if Nat.eqb (length head') (length head) then (head, acc)
        else match n with
             | O => (members, (fst acc, all_groups))
             | S n' => iter n' head' acc
             end in
      iter (S (length members)) nil acc
  | Sbreak => (brk, acc)
  | Scontinue => (cont, acc)
  | Sreturn None => (nil, acc)
  | Sreturn (Some e) => (luses e nil, acc)
  | Sswitch c ls =>
      (* Any case may be entered, or none: after the switch. [break] ends
         the switch. *)
      let '(_, all, acc) := live_lstmt labs ls after cont acc in
      (luses c (lunion all after), acc)
  | Slabel l s1 =>
      let '(l1, (found, conf)) := live_stmt labs s1 after brk cont acc in
      (l1, (PTree.set l l1 found, conf))
  | Sgoto l => (match labs!l with Some x => x | None => nil end, acc)
  end
(** Cases: the members live at the start of these cases (falling through
    from one case to the next), and at the start of any of them. *)
with live_lstmt (labs: PTree.t lset) (ls: labeled_statements) (after cont: lset) (acc: lacc) {struct ls}
                : lset * lset * lacc :=
  match ls with
  | LSnil => (after, after, acc)
  | LScons _ s ls' =>
      let '(lr, all, acc) := live_lstmt labs ls' after cont acc in
      let '(l, acc) := live_stmt labs s lr after cont acc in
      (l, lunion l all, acc)
  end.

Definition labels_size (labs: PTree.t lset) : nat :=
  PTree.fold (fun n _ s => (n + length s)%nat) labs O.

(** Rounds until the members live at every label stop growing; a [goto]
    reads them from the previous round. Without [goto], one round. Also
    returns the members live at each label, which [plan_ok] checks. *)
Fixpoint live_rounds (n: nat) (body: statement) (labs: PTree.t lset) (conf: PTree.t unit)
                     : lset * PTree.t lset * PTree.t unit :=
  let '(entry, (found, conf')) := live_stmt labs body nil nil nil (PTree.empty lset, conf) in
  if Nat.eqb (labels_size found) (labels_size labs) then (entry, found, conf')
  else match n with
       | O => (members, found, all_groups)
       | S n' => live_rounds n' body found conf'
       end.

End REBASED.

Fixpoint count_labels (s: statement) : nat :=
  match s with
  | Slabel _ s1 => S (count_labels s1)
  | Ssequence s1 s2 | Sloop s1 s2 | Sifthenelse _ s1 s2 => (count_labels s1 + count_labels s2)%nat
  | Sswitch _ ls => count_labels_l ls
  | _ => O
  end
with count_labels_l (ls: labeled_statements) : nat :=
  match ls with
  | LSnil => O
  | LScons _ s ls' => (count_labels s + count_labels_l ls')%nat
  end.

(** The pointer temporaries of [f] to split, with fresh identifiers for
    their bases and indices numbered from [next], and the next unused
    identifier. A group is split if one of its members moves and all of its
    members point to things of the same size. Its members share one base
    temporary when the base can be kept exact, and at most one member is a
    parameter:
    - its only source of an outside value is a parameter: the base is set at
      entry and never changes; or
    - it has outside values, and no rebase of a member (a parameter counts
      as a rebase at entry) happens while another member is live.
    Otherwise, or when [share] is false, each member has its own base, and
    copies copy it. Also returns the members live at each label, for the
    check of [plan_ok]. *)
Definition plan_function (share: bool) (f: function) (next: positive) : splits * PTree.t lset * positive :=
  let pts := splittable_temps (f.(fn_params) ++ f.(fn_temps)) in
  let es := List.filter (fun (e: ident * ident * bool) => let '(p, q, _) := e in is_some pts!p && is_some pts!q)
                        (edges_stmt f.(fn_body) nil) in
  let r := relax_n (S (length es)) es (PTree.empty ident) in
  let moving := fold_left (fun (m: PTree.t unit) (e: ident * ident * bool) => let '(p, _, off) := e in
                             if off then PTree.set (label r p) tt m else m)
                          es (PTree.empty unit) in
  let members := List.filter (fun (pt: ident * type) => is_some moving!(label r (fst pt))) (PTree.elements pts) in
  let mixed := fold_left (fun (m: PTree.t unit) (pt: ident * type) =>
                 let g := label r (fst pt) in
                 match pts!g with
                 | Some tg => if Z.eqb (elem_size (snd pt)) (elem_size tg) then m else PTree.set g tt m
                 | None => PTree.set g tt m
                 end) members (PTree.empty unit) in
  let chosen := List.filter (fun (pt: ident * type) => negb (is_some mixed!(label r (fst pt)))) members in
  let grp := fold_left (fun m (pt: ident * type) => PTree.set (fst pt) (label r (fst pt)) m)
                       chosen (PTree.empty ident) in
  let gsize := fold_left (fun m (pt: ident * type) => PTree.set (label r (fst pt)) (elem_size (snd pt)) m)
                         chosen (PTree.empty Z) in
  let params := fold_left (fun m (pt: ident * type) => PTree.set (fst pt) tt m)
                          f.(fn_params) (PTree.empty unit) in
  let nparams := fold_left (fun (m: PTree.t nat) (pt: ident * type) =>
                   if is_some params!(fst pt) then
                     let g := label r (fst pt) in
                     PTree.set g (S (match m!g with Some k => k | None => O end)) m
                   else m) chosen (PTree.empty nat) in
  let '(nrebases, _) := rebases_stmt grp gsize false f.(fn_body) (PTree.empty nat, PTree.empty unit) in
  let count := fun (m: PTree.t nat) g => match m!g with Some k => k | None => O end in
  (* The only source of an outside value is one parameter, at entry. *)
  let sources := fun g => (count nparams g + count nrebases g)%nat in
  let once := fun g =>
    match sources g with
    | S O => Nat.eqb (count nrebases g) O
    | _ => false
    end in
  let groups := fold_left (fun m (pt: ident * type) => PTree.set (label r (fst pt)) tt m)
                          chosen (PTree.empty unit) in
  (* Liveness, only when some group needs it: to decide, or for the members
     live at labels, which [plan_ok] checks at every label (used by a goto
     or not) when a function shares a base. *)
  let labelled := negb (Nat.eqb (count_labels f.(fn_body)) O) in
  let needs := share && existsb (fun (gu: ident * unit) =>
                         negb (Nat.eqb (sources (fst gu)) O) && (negb (once (fst gu)) || labelled))
                       (PTree.elements groups) in
  let '(labs, conf) :=
    if needs then
      let mems := map fst chosen in
      let '(entry, labs, conf) := live_rounds grp gsize mems groups (S (count_labels f.(fn_body) * length mems))
                                              f.(fn_body) (PTree.empty lset) (PTree.empty unit) in
      (labs, fold_left (fun conf (pt: ident * type) =>
                          if is_some params!(fst pt) then conflict grp (fst pt) entry conf else conf)
                       chosen conf)
    else (PTree.empty lset, groups) in
  let fixed := fun g => share && Nat.leb (count nparams g) 1
                        && (once g || (negb (Nat.eqb (sources g) O) && negb (is_some conf!g))) in
  let '(sps, _, n) :=
    fold_left (fun (acc: splits * PTree.t ident * positive) (pt: ident * type) =>
                 let '(sps, gb, n) := acc in
                 let p := fst pt in
                 let g := label r p in
                 let mk := fun b i => mksplit b i (snd pt) (elem_size (snd pt)) (is_some params!p) in
                 if fixed g then
                   match gb!g with
                   | Some b => (PTree.set p (mk b n) sps, gb, Pos.succ n)
                   | None => (PTree.set p (mk n (Pos.succ n)) sps, PTree.set g n gb, Pos.succ (Pos.succ n))
                   end
                 else (PTree.set p (mk n (Pos.succ n)) sps, gb, Pos.succ (Pos.succ n)))
              chosen (PTree.empty split, PTree.empty ident, next) in
  (sps, labs, n).

End ANALYSIS.

(** ** Analysis: pointers stored in memory *)

(** Syntactic equality of expressions. [false] for constructors a cached
    location never contains (floating-point constants, [sizeof]): the only
    cost is a missed match, never a wrong one. *)
Definition binop_eq: forall (x y: binary_operation), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition unop_eq: forall (x y: unary_operation), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition type_eqb (t u: type) : bool := if type_eq t u then true else false.

Fixpoint expr_eqb (a b: expr) : bool :=
  match a, b with
  | Econst_int i t, Econst_int j u => Int.eq i j && type_eqb t u
  | Econst_long i t, Econst_long j u => Int64.eq i j && type_eqb t u
  | Evar x t, Evar y u => Pos.eqb x y && type_eqb t u
  | Etempvar x t, Etempvar y u => Pos.eqb x y && type_eqb t u
  | Ederef a1 t, Ederef b1 u => expr_eqb a1 b1 && type_eqb t u
  | Eaddrof a1 t, Eaddrof b1 u => expr_eqb a1 b1 && type_eqb t u
  | Eunop o a1 t, Eunop o' b1 u => (if unop_eq o o' then true else false) && expr_eqb a1 b1 && type_eqb t u
  | Ebinop o a1 a2 t, Ebinop o' b1 b2 u =>
      (if binop_eq o o' then true else false) && expr_eqb a1 b1 && expr_eqb a2 b2 && type_eqb t u
  | Ecast a1 t, Ecast b1 u => expr_eqb a1 b1 && type_eqb t u
  | Efield a1 f t, Efield b1 g u => expr_eqb a1 b1 && Pos.eqb f g && type_eqb t u
  | _, _ => false
  end.

(** The temporaries the address of a location depends on, or [None] if
    computing it reads memory or a volatile location is involved. A cached
    location's address must not change while nothing assigns these. *)
Fixpoint addr_temps (b: expr) : option (list ident) :=
  match b with
  | Etempvar x _ => Some (x :: nil)
  | Econst_int _ _ | Econst_long _ _ => Some nil
  | Ebinop Oadd b1 b2 _ | Ebinop Osub b1 b2 _ =>
      match addr_temps b1, addr_temps b2 with
      | Some l1, Some l2 => Some (l1 ++ l2)
      | _, _ => None
      end
  | Ecast b1 _ => addr_temps b1
  | Eaddrof a _ => lv_temps a
  | _ => None
  end
with lv_temps (a: expr) : option (list ident) :=
  if type_is_volatile (typeof a) then None else
  match a with
  | Evar _ _ => Some nil
  | Efield b _ _ => lv_temps b
  | Ederef b _ => addr_temps b
  | _ => None
  end.

(** [l] is read as a value somewhere in [e] (not just its address taken). *)
Fixpoint occurs (l e: expr) {struct e} : bool :=
  expr_eqb e l ||
  match e with
  | Ederef a _ | Eunop _ a _ | Ecast a _ | Efield a _ _ => occurs l a
  | Eaddrof a _ => occurs_lv l a
  | Ebinop _ a1 a2 _ => occurs l a1 || occurs l a2
  | _ => false
  end
with occurs_lv (l a: expr) {struct a} : bool :=
  match a with
  | Ederef b _ | Efield b _ _ => occurs l b
  | _ => false
  end.

(** Statement [s] evaluates [l] and converts its value: it dereferences it,
    computes with it, compares it, casts it, passes it or stores it. A
    conversion gets stuck on [Vundef], so where [s] does this, reloading the
    cache ([L_base = L - L_idx], which also gets stuck on [Vundef]) cannot
    get stuck where [s] would not. The one place a value is not converted is
    a plain copy into a temporary, [x = L]. *)
Definition leaf_reads (l: expr) (s: statement) : bool :=
  match s with
  | Sset _ e => negb (expr_eqb e l) && occurs l e
  | Sassign a e => occurs_lv l a || occurs l e
  | Scall _ f al => occurs l f || existsb (occurs l) al
  | Sbuiltin _ _ _ al => existsb (occurs l) al
  | Sreturn (Some e) => occurs l e
  | Sifthenelse c _ _ | Sswitch c _ => occurs l c
  | _ => false
  end.

(** The first thing [s] does is such a read of [l]. Then a reload just before
    [s] reads the same memory as [s] would: this places a loop's reload
    before the loop, as for [while (r->pos < r->end) ...]. *)
Fixpoint first_reads (l: expr) (s: statement) : bool :=
  match s with
  | Ssequence Sskip s2 => first_reads l s2
  | Ssequence s1 _ | Sloop s1 _ => first_reads l s1
  | _ => leaf_reads l s
  end.

(** External functions that leave every existing location unchanged:
    [malloc] (a fresh block), [free] (contents of other blocks are kept; a
    freed location can no longer be read at all), annotations, volatile
    loads, and builtins CompCert gives a pure meaning. *)
Definition ef_keeps_memory (ef: external_function) : bool :=
  match ef with
  | EF_malloc | EF_free | EF_vload _ | EF_annot _ _ _ | EF_annot_val _ _ _ | EF_debug _ _ _ => true
  | EF_builtin name sg => is_some (lookup_builtin_function name sg)
  | _ => false
  end.

Definition is_local (vars: list (ident * type)) (x: ident) : bool :=
  existsb (fun v => Pos.eqb (fst v) x) vars.

(** A direct call to a function in [nw]. A local variable of the same name
    would shadow the global. *)
Definition call_keeps_memory (nw: PTree.t unit) (vars: list (ident * type)) (a: expr) : bool :=
  match a with
  | Evar g _ => is_some nw!g && negb (is_local vars g)
  | _ => false
  end.

Fixpoint keeps_memory (nw: PTree.t unit) (vars: list (ident * type)) (s: statement) : bool :=
  match s with
  | Sassign _ _ => false
  | Scall _ a _ => call_keeps_memory nw vars a
  | Sbuiltin _ ef _ _ => ef_keeps_memory ef
  | Ssequence s1 s2 | Sloop s1 s2 | Sifthenelse _ s1 s2 => keeps_memory nw vars s1 && keeps_memory nw vars s2
  | Slabel _ s1 => keeps_memory nw vars s1
  | Sswitch _ ls => keeps_memory_l nw vars ls
  | _ => true
  end
with keeps_memory_l (nw: PTree.t unit) (vars: list (ident * type)) (ls: labeled_statements) : bool :=
  match ls with
  | LSnil => true
  | LScons _ s ls' => keeps_memory nw vars s && keeps_memory_l nw vars ls'
  end.

(** Functions whose calls leave every existing location unchanged: internal
    functions with no store, no memory-writing builtin, and only direct calls
    to such functions (their own stack frame is fresh and freed on return),
    and the external functions of [ef_keeps_memory]. A greatest fixpoint:
    start from every function and remove the ones that call a function
    outside the set, until nothing changes. *)
Definition nw_step (defs: list (ident * globdef fundef type)) (nw: PTree.t unit) : PTree.t unit :=
  fold_left (fun m (d: ident * globdef fundef type) =>
               match snd d with
               | Gfun (Internal f) =>
                   if is_some nw!(fst d) && keeps_memory nw f.(fn_vars) f.(fn_body)
                   then PTree.set (fst d) tt m else m
               | Gfun (External ef _ _ _) => if ef_keeps_memory ef then PTree.set (fst d) tt m else m
               | _ => m
               end)
            defs (PTree.empty unit).

(** [nw_step] only removes functions, so a step that keeps the size changes
    nothing: the fixpoint is reached. *)
Fixpoint nw_iter (n: nat) (defs: list (ident * globdef fundef type)) (nw: PTree.t unit) : PTree.t unit :=
  match n with
  | O => nw
  | S n' =>
      let nw' := nw_step defs nw in
      if Nat.eqb (length (PTree.elements nw')) (length (PTree.elements nw)) then nw' else nw_iter n' defs nw'
  end.

Definition nonwriting (defs: list (ident * globdef fundef type)) : PTree.t unit :=
  let all := fold_left (fun m (d: ident * globdef fundef type) =>
                          match snd d with Gfun _ => PTree.set (fst d) tt m | _ => m end)
                       defs (PTree.empty unit) in
  nw_iter (S (length defs)) defs all.

(** A cache for one location. Its index counts in units of [ca_size]. *)
Record cache : Type := mkcache {
  ca_loc: expr;            (* the location, an lvalue of pointer type *)
  ca_base: ident;
  ca_idx: ident;
  ca_type: type;           (* the location's type *)
  ca_size: Z;
  ca_temps: list ident     (* the temporaries its address depends on *)
}.

Section MEMORY.

Variable ce: composite_env.

(** [a] (a store) and [l] (a cached location) cannot overlap: two different
    variables, or two members of one struct, reached by the same path, whose
    byte ranges are disjoint. Anything else may overlap. *)
Fixpoint lv_path (a: expr) : expr * list (ident * type) :=
  match a with
  | Efield b f _ => let '(r, fs) := lv_path b in (r, fs ++ (f, typeof b) :: nil)
  | _ => (a, nil)
  end.

Definition member_range (co: composite) (f: ident) : option (Z * Z) :=
  match field_offset ce f (co_members co), field_type f (co_members co) with
  | OK (ofs, Full), OK t => Some (ofs, ofs + sizeof ce t)
  | _, _ => None
  end.

Fixpoint diverge (fs1 fs2: list (ident * type)) : bool :=
  match fs1, fs2 with
  | (f1, t1) :: r1, (f2, _) :: r2 =>
      if Pos.eqb f1 f2 then diverge r1 r2
      else match t1 with
           | Tstruct id _ =>
               match ce!id with
               | Some co =>
                   match member_range co f1, member_range co f2 with
                   | Some (lo1, hi1), Some (lo2, hi2) => Z.leb hi1 lo2 || Z.leb hi2 lo1
                   | _, _ => false
                   end
               | None => false
               end
           | _ => false
           end
  | _, _ => false
  end.

Definition disjoint (a l: expr) : bool :=
  let '(ra, fa) := lv_path a in
  let '(rl, fl) := lv_path l in
  if expr_eqb ra rl then diverge fa fl
  else match ra, rl with
       | Evar x _, Evar y _ => negb (Pos.eqb x y)
       | _, _ => false
       end.

(** [p + n] or [p - n] with [p] any expression of pointer type and [n] an
    integer: the type [p] has, whether it subtracts, and how [n] is widened
    (as in [offset_of]). *)
Definition ptr_offset (op: binary_operation) (a n: expr) : option (type * bool * option signedness) :=
  match op with
  | Oadd =>
      match classify_add (typeof a) (typeof n) with
      | add_case_pi _ si => Some (typeof a, false, Some si)
      | add_case_pl _ => Some (typeof a, false, None)
      | _ => None
      end
  | Osub =>
      match classify_sub (typeof a) (typeof n) with
      | sub_case_pi _ si => Some (typeof a, true, Some si)
      | sub_case_pl _ => Some (typeof a, true, None)
      | _ => None
      end
  | _ => None
  end.

(** Locations that can have a cache: a variable, a member or a dereference,
    of pointer-to-complete type, not volatile, whose address depends only on
    temporaries. *)
Definition cacheable (a: expr) : bool :=
  match a with
  | Evar _ _ | Efield _ _ _ | Ederef _ _ =>
      match typeof a with
      | Tpointer t' _ => complete_type ce t' && is_some (lv_temps a)
      | _ => false
      end
  | _ => false
  end.

(** Assignments [x = e] to temporaries and stores [a = e], in order. *)
Fixpoint assigns_stmt (s: statement) (acc: list (ident * expr) * list (expr * expr))
                    : list (ident * expr) * list (expr * expr) :=
  match s with
  | Sset x e => let '(sets, stores) := acc in ((x, e) :: sets, stores)
  | Sassign a e => let '(sets, stores) := acc in (sets, (a, e) :: stores)
  | Ssequence s1 s2 | Sloop s1 s2 | Sifthenelse _ s1 s2 => assigns_stmt s2 (assigns_stmt s1 acc)
  | Slabel _ s1 => assigns_stmt s1 acc
  | Sswitch _ ls => assigns_lstmt ls acc
  | _ => acc
  end
with assigns_lstmt (ls: labeled_statements) (acc: list (ident * expr) * list (expr * expr))
                 : list (ident * expr) * list (expr * expr) :=
  match ls with
  | LSnil => acc
  | LScons _ s ls' => assigns_lstmt ls' (assigns_stmt s acc)
  end.

(** Temporary [t] is assigned [a], or [a] plus or minus something. *)
Definition copied_from (sets: list (ident * expr)) (t: ident) (a: expr) : bool :=
  existsb (fun (te: ident * expr) =>
             Pos.eqb (fst te) t &&
             (expr_eqb (snd te) a || match snd te with Ebinop _ a' _ _ => expr_eqb a' a | _ => false end))
          sets.

(** The store [a = e] moves [a]: [e] is [a + n], or [t + n] or [t] where
    temporary [t] holds a copy of [a] (as [*p->cur++ = c] compiles). *)
Definition moves (sets: list (ident * expr)) (a e: expr) : bool :=
  match e with
  | Ebinop op a' n _ =>
      is_some (ptr_offset op a' n) &&
      (expr_eqb a' a || match a' with Etempvar t _ => copied_from sets t a | _ => false end)
  | Etempvar t _ => copied_from sets t a
  | _ => false
  end.

(** The locations of [f] to cache, with fresh identifiers numbered from
    [next], in the order of their first move. *)
Definition plan_caches (f: function) (next: positive) : list cache * positive :=
  let '(sets, stores) := assigns_stmt f.(fn_body) (nil, nil) in
  let locs := fold_left (fun (acc: list expr) (ae: expr * expr) =>
                           let '(a, e) := ae in
                           if cacheable a && moves sets a e && negb (existsb (expr_eqb a) acc)
                           then acc ++ a :: nil else acc)
                        (rev' stores) nil in
  fold_left (fun (acc: list cache * positive) (a: expr) =>
               let '(l, n) := acc in
               let temps := match lv_temps a with Some t => t | None => nil end in
               (l ++ mkcache a n (Pos.succ n) (typeof a) (elem_size ce (typeof a)) temps :: nil,
                Pos.succ (Pos.succ n)))
            locs (nil, next).

End MEMORY.

(** ** Rewriting *)

Section REWRITE.

Variable ce: composite_env.
Variable sps: splits.
Variable cl: list cache.              (* every cache of the function *)
Variable nw: PTree.t unit.            (* functions whose calls keep memory *)
Variable vars: list (ident * type).   (* the function's local variables *)

Definition base_of (s: split) : expr := Etempvar s.(sp_base) s.(sp_type).
Definition idx_of (s: split) : expr := Etempvar s.(sp_idx) tlong.

(** The value of a split temporary, [p_base + p_idx], with the type [ty]
    the original occurrence had. The addition scales by [sp_size], because
    [p_base] has [p]'s declared type. *)
Definition value_of (s: split) (ty: type) : expr := Ebinop Oadd (base_of s) (idx_of s) ty.

Definition zero_index (s: split) : statement := Sset s.(sp_idx) (Econst_long Int64.zero tlong).

Definition cache_base (k: cache) : expr := Etempvar (ca_base k) (ca_type k).
Definition cache_idx (k: cache) : expr := Etempvar (ca_idx k) tlong.
Definition cache_value (k: cache) (ty: type) : expr := Ebinop Oadd (cache_base k) (cache_idx k) ty.

(** [n] widened to 64 bits exactly as pointer arithmetic widens it. *)
Definition widen (si: option signedness) (n: expr) : expr :=
  match si, n with
  | None, _ => n
  | Some Signed, Econst_int i _ => Econst_long (Int64.repr (Int.signed i)) tlong
  | Some Unsigned, Econst_int i _ => Econst_long (Int64.repr (Int.unsigned i)) tlong
  | Some si', _ =>
      match typeof n, si' with
      | Tint I32 Signed _, Signed | Tint I32 Unsigned _, Unsigned => Ecast n tlong
      | _, _ => Ecast (Ecast n (Tint I32 si' noattr)) tlong
      end
  end.

Definition index_expr (s: split) (sub: bool) (si: option signedness) (n: expr) : expr :=
  Ebinop (if sub then Osub else Oadd) (idx_of s) (widen si n) tlong.

Fixpoint find_cache (cs: list cache) (e: expr) : option cache :=
  match cs with
  | nil => None
  | k :: cs' => if expr_eqb (ca_loc k) e then Some k else find_cache cs' e
  end.

(** [p + n] or [p - n], kept in index form when [p] is a split temporary or
    a location with a valid cache in [cs], and [p]'s type in the expression
    scales by the same size as its index. [n'] is already rewritten. *)
Definition index_form (cs: list cache) (op: binary_operation) (a1 n': expr) (ty: type) : option expr :=
  match ptr_offset op a1 n' with
  | Some (tq, sub, si) =>
      match find_cache cs a1 with
      | Some k =>
          if Z.eqb (elem_size ce tq) (ca_size k)
          then Some (Ebinop Oadd (cache_base k)
                            (Ebinop (if sub then Osub else Oadd) (cache_idx k) (widen si n') tlong) ty)
          else None
      | None =>
          match a1 with
          | Etempvar q _ =>
              match sps!q with
              | Some s =>
                  if Z.eqb (elem_size ce tq) s.(sp_size)
                  then Some (Ebinop Oadd (base_of s) (index_expr s sub si n') ty)
                  else None
              | None => None
              end
          | _ => None
          end
      end
  | None => None
  end.

(** A rewritten pointer in base + index form, [B + i] with [B] the base
    temporary of a group or of a cache: the base, its type and the index. *)
Definition is_base (b: ident) : bool :=
  existsb (fun (ps: ident * split) => Pos.eqb (sp_base (snd ps)) b) (PTree.elements sps)
  || existsb (fun (k: cache) => Pos.eqb (ca_base k) b) cl.

Definition base_index (e: expr) : option (ident * type * expr) :=
  match e with
  | Ebinop Oadd (Etempvar b tb) i _ => if is_base b && type_eqb (typeof i) tlong then Some (b, tb, i) else None
  | _ => None
  end.

(** [e1 == e2], [e1 != e2] and [e1 - e2] on pointers with the same base
    variable and elements of size 1 are exactly the same operations on the
    indices: [B + k1 == B + k2] iff [k1 == k2], and [(B + k1) - (B + k2)] is
    [k1 - k2], both modulo 2^64, where Clight defines them (one block, or
    integers). [a1'] and [a2'] are [a1] and [a2] rewritten. Ordering
    comparisons keep [B + k]: an index that wrapped around would compare
    differently. *)
Definition index_compare (op: binary_operation) (a1 a2 a1' a2': expr) (ty: type) : option expr :=
  match base_index a1', base_index a2' with
  | Some (b1, t1, i1), Some (b2, t2, i2) =>
      if Pos.eqb b1 b2 && Z.eqb (elem_size ce t1) 1 && Z.eqb (elem_size ce t2) 1 then
        match op with
        | Oeq | One =>
            match classify_cmp (typeof a1) (typeof a2) with
            | cmp_case_pp => Some (Ebinop op i1 i2 ty)
            | _ => None
            end
        | Osub =>
            match classify_sub (typeof a1) (typeof a2) with
            | sub_case_pp t => if Z.eqb (sizeof ce t) 1 && type_eqb ty tlong then Some (Ebinop Osub i1 i2 ty) else None
            | _ => None
            end
        | _ => None
        end
      else None
  | _, _ => None
  end.

(** Expressions, given the caches [cs] that are valid. A read of a cached
    location becomes [L_base + L_idx]; an lvalue's own location is kept
    ([tr_lv]): only its address computation is rewritten. *)
Fixpoint tr_expr (cs: list cache) (e: expr) : expr :=
  match find_cache cs e with
  | Some k => cache_value k (typeof e)
  | None =>
      match e with
      | Etempvar x ty =>
          match sps!x with Some s => value_of s ty | None => e end
      | Ederef a ty => Ederef (tr_expr cs a) ty
      | Eaddrof a ty => Eaddrof (tr_lv cs a) ty
      | Eunop op a ty => Eunop op (tr_expr cs a) ty
      | Ebinop op a1 a2 ty =>
          let a2' := tr_expr cs a2 in
          match index_form cs op a1 a2' ty with
          | Some e' => e'
          | None =>
              let a1' := tr_expr cs a1 in
              match index_compare op a1 a2 a1' a2' ty with
              | Some e' => e'
              | None => Ebinop op a1' a2' ty
              end
          end
      | Ecast a ty => Ecast (tr_expr cs a) ty
      | Efield a f ty => Efield (tr_expr cs a) f ty
      | _ => e
      end
  end
with tr_lv (cs: list cache) (a: expr) : expr :=
  match a with
  | Ederef b ty => Ederef (tr_expr cs b) ty
  | Efield b f ty => Efield (tr_expr cs b) f ty
  | _ => a
  end.

(** After updating [x]'s index from [q]'s: copy [q]'s base, unless they
    share one. *)
Definition copy_base (sx sq: split) (update: statement) : statement :=
  if peq sx.(sp_base) sq.(sp_base) then update
  else Ssequence update (Sset sx.(sp_base) (base_of sq)).

(** An assignment [x = e] to a split temporary. Copies and offsets within
    the same unit update the index (first, so that [e] sees the old values)
    and copy the base; anything else starts a new base at index 0. *)
Definition set_split (cs: list cache) (x: ident) (sx: split) (e: expr) : statement :=
  let rebase := Ssequence (Sset sx.(sp_base) (tr_expr cs e)) (zero_index sx) in
  match e with
  | Etempvar q _ =>
      match sps!q with
      | Some sq =>
          if peq x q then Sskip
          else if Z.eqb sq.(sp_size) sx.(sp_size)
          then copy_base sx sq (Sset sx.(sp_idx) (idx_of sq))
          else rebase
      | None => rebase
      end
  | _ =>
      match offset_of e with
      | Some (q, tq, n, sub, si) =>
          match sps!q with
          | Some sq =>
              if Z.eqb (elem_size ce tq) sq.(sp_size) && Z.eqb sq.(sp_size) sx.(sp_size) then
                let update := Sset sx.(sp_idx) (index_expr sq sub si (tr_expr cs n)) in
                if peq x q then update else copy_base sx sq update
              else rebase
          | None => rebase
          end
      | None => rebase
      end
  end.

(** A call or builtin whose result goes to [optid]. *)
Definition with_result (optid: option ident) (mk: option ident -> statement) : statement :=
  match optid with
  | Some x =>
      match sps!x with
      | Some sx => Ssequence (mk (Some sx.(sp_base))) (zero_index sx)
      | None => mk optid
      end
  | None => mk None
  end.

Definition sseq (s1 s2: statement) : statement :=
  match s1, s2 with
  | Sskip, _ => s2
  | _, Sskip => s1
  | _, _ => Ssequence s1 s2
  end.

(** *** What is known about the caches at a program point *)

(** [cs_valid]: the caches (by base) whose [L_base + L_idx] equals [L]'s
    value in memory. [cs_copies]: temporaries [t] holding a copy of a cached
    location plus a constant [c] (in elements), [t = L + c], with a flag
    saying that the cache has stayed valid, base and index unchanged, since
    the copy, so that [t = L_base + (L_idx + c)]. A store [L = t + n] can then
    keep counting from [L_idx]. *)
Record cstate : Type := mkcstate {
  cs_valid: list ident;
  cs_copies: list (ident * (ident * Z * bool))
}.

Definition empty_state := mkcstate nil nil.

Definition default_state (o: option cstate) : cstate :=
  match o with Some st => st | None => empty_state end.

Definition mem_id (x: ident) (l: list ident) : bool := existsb (Pos.eqb x) l.

Definition is_valid (st: cstate) (k: cache) : bool := mem_id (ca_base k) (cs_valid st).

Definition valid_caches (st: cstate) : list cache := filter (is_valid st) cl.

Definition copy_eqb (a b: ident * (ident * Z * bool)) : bool :=
  let '(t, (k, c, v)) := a in
  let '(t', (k', c', v')) := b in
  Pos.eqb t t' && Pos.eqb k k' && Z.eqb c c' && Bool.eqb v v'.

(** Where paths join, only what holds on both is known. *)
Definition meet (a b: cstate) : cstate :=
  mkcstate (filter (fun k => mem_id k (cs_valid b)) (cs_valid a))
           (filter (fun c => existsb (copy_eqb c) (cs_copies b)) (cs_copies a)).

Definition meet_opt (a b: option cstate) : option cstate :=
  match a, b with
  | Some x, Some y => Some (meet x y)
  | Some x, None | None, Some x => Some x
  | None, None => None
  end.

(** [b] is [meet a _], so it is [a] when it has as many elements. *)
Definition same_state (a b: cstate) : bool :=
  Nat.eqb (length (cs_valid a)) (length (cs_valid b)) && Nat.eqb (length (cs_copies a)) (length (cs_copies b)).

Definition set_valid (k: cache) (st: cstate) : cstate :=
  if is_valid st k then st else mkcstate (ca_base k :: cs_valid st) (cs_copies st).

(** The caches satisfying [hit] may no longer match memory. *)
Definition invalidate (hit: cache -> bool) (st: cstate) : cstate :=
  let gone := fun b => existsb (fun k => Pos.eqb (ca_base k) b && hit k) cl in
  mkcstate (filter (fun b => negb (gone b)) (cs_valid st))
           (map (fun (c: ident * (ident * Z * bool)) =>
                   let '(t, (b, off, v)) := c in if gone b then (t, (b, off, false)) else c)
                (cs_copies st)).

(** [k]'s base or index changed: copies measured against them are stale. *)
Definition forget_copies (k: cache) (st: cstate) : cstate :=
  mkcstate (cs_valid st)
           (filter (fun (c: ident * (ident * Z * bool)) => let '(_, (b, _, _)) := c in negb (Pos.eqb b (ca_base k)))
                   (cs_copies st)).

(** Temporary [x] gets a new value: caches whose address reads [x] are
    stale, and [x] is no longer a copy. *)
Definition assign_temp (x: ident) (st: cstate) : cstate :=
  let st' := invalidate (fun k => mem_id x (ca_temps k)) st in
  mkcstate (cs_valid st') (filter (fun (c: ident * (ident * Z * bool)) => negb (Pos.eqb (fst c) x)) (cs_copies st')).

Definition lookup_copy (st: cstate) (t: ident) (k: cache) : option (Z * bool) :=
  match find (fun (c: ident * (ident * Z * bool)) =>
                let '(t', (b, _, _)) := c in Pos.eqb t t' && Pos.eqb b (ca_base k))
             (cs_copies st) with
  | Some (_, (_, c, v)) => Some (c, v)
  | None => None
  end.

(** A constant [n] added to a pointer, in elements, as Clight widens it. *)
Definition const_offset (si: option signedness) (n: expr) : option Z :=
  match si, n with
  | Some Signed, Econst_int i _ => Some (Int.signed i)
  | Some Unsigned, Econst_int i _ => Some (Int.unsigned i)
  | None, Econst_long i _ => Some (Int64.signed i)
  | _, _ => None
  end.

(** [x = e] makes [x] a copy of a cached location when [e] is the location
    ([x = L], the cache valid or not), or the location plus a constant, read
    through a valid cache. *)
Definition copy_source (st: cstate) (e: expr) : option (cache * Z * bool) :=
  match find_cache cl e with
  | Some k => Some (k, 0, is_valid st k)
  | None =>
      match e with
      | Ebinop op a n _ =>
          match find_cache (valid_caches st) a, ptr_offset op a n with
          | Some k, Some (tq, sub, si) =>
              match const_offset si n with
              | Some c => if Z.eqb (elem_size ce tq) (ca_size k) then Some (k, if sub then -c else c, true) else None
              | None => None
              end
          | _, _ => None
          end
      | _ => None
      end
  end.

(** Copies serve [t = L; L = t + 1] (how [*p->cur++] compiles), so only the
    most recent few are kept: in a huge function the list stays short. *)
Definition max_copies : nat := 8%nat.

Definition after_set (x: ident) (e: expr) (st: cstate) : cstate :=
  let st' := assign_temp x st in
  match copy_source st e with
  | Some (k, c, v) =>
      if mem_id x (ca_temps k) then st'
      else mkcstate (cs_valid st') (firstn max_copies ((x, (ca_base k, c, v && is_valid st' k)) :: cs_copies st'))
  | None => st'
  end.

Definition after_result (optid: option ident) (st: cstate) : cstate :=
  match optid with Some x => assign_temp x st | None => st end.

(** Temporary [x] got a new value, so a cached location whose address reads
    [x] is now a different location: its index restarts at 0 (its next
    reload sets the base). *)
Definition resets (x: ident) : statement :=
  fold_right (fun (k: cache) s => if mem_id x (ca_temps k) then sseq (Sset (ca_idx k) (Econst_long Int64.zero tlong)) s else s)
             Sskip cl.

Definition result_resets (optid: option ident) : statement :=
  match optid with Some x => resets x | None => Sskip end.

(** *** Statements *)

(** [L_base = L - L_idx]: the cache matches [L] again, and the index keeps
    counting. *)
Definition reload (k: cache) : statement :=
  Sset (ca_base k) (Ebinop Osub (tr_lv nil (ca_loc k)) (cache_idx k) (ca_type k)).

(** The reloads a statement needs first: stale caches whose location it reads
    and converts ([leaf_reads]). *)
Definition reloads (s: statement) (st: cstate) : statement * cstate :=
  fold_left (fun (acc: statement * cstate) (k: cache) =>
               let '(pre, st') := acc in
               if negb (is_valid st' k) && leaf_reads (ca_loc k) s
               then (sseq pre (reload k), set_valid k st')
               else acc)
            cl (Sskip, st).

Definition idx_plus (k: cache) (c: Z) : expr :=
  if Z.eqb c 0 then cache_idx k else Ebinop Oadd (cache_idx k) (Econst_long (Int64.repr c) tlong) tlong.

Definition is_pointer (t: type) : bool := match t with Tpointer _ _ => true | _ => false end.

(** A store [a = e] to cached location [a] (cache [k]), with the caches
    known in [st]. Memory gets the same value as in the source.
    - [a = a +/- n]: a move, [L_idx = L_idx +/- n].
    - [a = t +/- n] or [a = t], [t] a copy [L + c]: a move by [c +/- n]. If
      the cache did not stay valid since the copy, the base is first set so
      that [t = L_base + (L_idx + c)].
    - anything else: a new base, at index 0. *)
Definition store_cached (st: cstate) (k: cache) (a e: expr) : statement :=
  let cs := valid_caches st in
  let ty := ca_type k in
  let store := Sassign (tr_lv cs a) (cache_value k ty) in
  let set_idx := fun i => Sset (ca_idx k) i in
  let rebase := sseq (Sset (ca_base k) (if type_eqb (typeof e) ty then tr_expr cs e else Ecast (tr_expr cs e) ty))
                     (sseq (set_idx (Econst_long Int64.zero tlong)) (Sassign (tr_lv cs a) (cache_base k))) in
  let from_copy := fun (t: ident) (tyt: type) (c: Z) (v: bool) (step: expr -> expr) =>
      if Z.eqb (elem_size ce tyt) (ca_size k) then
        let d := idx_plus k c in
        if v && is_valid st k then sseq (set_idx (step d)) store
        else sseq (Sset (ca_base k) (Ebinop Osub (tr_expr cs (Etempvar t tyt)) d ty))
                  (sseq (set_idx (step d)) store)
      else rebase in
  match e with
  | Etempvar t tyt =>
      if is_pointer tyt then
        match lookup_copy st t k with
        | Some (c, v) => from_copy t tyt c v (fun d => d)
        | None => rebase
        end
      else rebase
  | Ebinop op a' n rty =>
      match ptr_offset op a' n with
      | Some (tq, sub, si) =>
          let step := fun d => Ebinop (if sub then Osub else Oadd) d (widen si (tr_expr cs n)) tlong in
          if negb (is_pointer rty) then rebase
          else if expr_eqb a' a then
            if is_valid st k && Z.eqb (elem_size ce tq) (ca_size k)
            then sseq (set_idx (step (cache_idx k))) store
            else rebase
          else
            match a' with
            | Etempvar t tyt =>
                match lookup_copy st t k with
                | Some (c, v) => from_copy t tyt c v step
                | None => rebase
                end
            | _ => rebase
            end
      | None => rebase
      end
  | _ => rebase
  end.

(** A store [a = e]. Afterwards a stored-to cache is valid, and caches whose
    location may overlap [a] are stale. *)
Definition tr_assign (st: cstate) (a e: expr) : statement * cstate :=
  match find_cache cl a with
  | Some k =>
      (store_cached st k a e,
       set_valid k (forget_copies k
         (invalidate (fun k' => negb (Pos.eqb (ca_base k') (ca_base k)) && negb (disjoint ce a (ca_loc k'))) st)))
  | None =>
      let cs := valid_caches st in
      (Sassign (tr_lv cs a) (tr_expr cs e), invalidate (fun k => negb (disjoint ce a (ca_loc k))) st)
  end.

(** [x = e] for a temporary [x]. [None] when [e] is a bare copy of a split
    temporary and [x] is not split: Clight allows copying an uninitialized
    pointer, but [p_base + p_idx] would get stuck. A bare copy of a cached
    location reads memory unless the cache is valid (then it is
    [L_base + L_idx], which is defined). *)
Definition tr_set (cs: list cache) (x: ident) (e: expr) : option statement :=
  match sps!x with
  | Some sx => Some (set_split cs x sx e)
  | None =>
      match e with
      | Etempvar q _ => if is_some sps!q then None else Some (Sset x e)
      | _ => Some (Sset x (tr_expr cs e))
      end
  end.

(** How a statement can end: normally, by [break], by [continue], each with
    what is known then ([None]: it cannot end that way). [return] and [goto]
    leave nothing to know. *)
Definition outcome := (option cstate * option cstate * option cstate)%type.

Definition loop_part := cstate -> option (statement * outcome).

(** A loop: the state at its head must hold on entry and after every
    iteration. Starting from the entry state, intersect with the state at the
    end of the body until it does not change; it only shrinks, so [fuel] (its
    size plus one) iterations suffice. *)
Fixpoint tr_loop (fuel: nat) (t1 t2: loop_part) (entry: cstate)
                 : option (statement * statement * cstate * outcome) :=
  match t1 entry with
  | None => None
  | Some (s1', (n1, b1, c1)) =>
      match t2 (default_state (meet_opt n1 c1)) with
      | None => None
      | Some (s2', (n2, b2, c2)) =>
          let entry' := match meet_opt n2 c2 with Some back => meet entry back | None => entry end in
          if same_state entry entry' then Some (s1', s2', entry, (meet_opt b1 b2, None, None))
          else match fuel with
               | O => None
               | S fuel' => tr_loop fuel' t1 t2 entry'
               end
      end
  end.

Fixpoint tr_stmt (st: cstate) (s: statement) {struct s} : option (statement * outcome) :=
  match s with
  | Sskip => Some (Sskip, (Some st, None, None))
  | Sbreak => Some (Sbreak, (None, Some st, None))
  | Scontinue => Some (Scontinue, (None, None, Some st))
  | Sgoto l => Some (Sgoto l, (None, None, None))
  | Sreturn None => Some (Sreturn None, (None, None, None))
  | Sreturn (Some a) =>
      let '(pre, st1) := reloads s st in
      Some (sseq pre (Sreturn (Some (tr_expr (valid_caches st1) a))), (None, None, None))
  | Sset x e =>
      let '(pre, st1) := reloads s st in
      match tr_set (valid_caches st1) x e with
      | Some s' => Some (sseq pre (sseq s' (resets x)), (Some (after_set x e st1), None, None))
      | None => None
      end
  | Sassign a e =>
      let '(pre, st1) := reloads s st in
      let '(s', st2) := tr_assign st1 a e in
      Some (sseq pre s', (Some st2, None, None))
  | Scall optid a al =>
      let '(pre, st1) := reloads s st in
      let cs := valid_caches st1 in
      let st2 := if call_keeps_memory nw vars a then st1 else invalidate (fun _ => true) st1 in
      Some (sseq pre (sseq (with_result optid (fun dst => Scall dst (tr_expr cs a) (map (tr_expr cs) al)))
                           (result_resets optid)),
            (Some (after_result optid st2), None, None))
  | Sbuiltin optid ef tys al =>
      let '(pre, st1) := reloads s st in
      let cs := valid_caches st1 in
      let st2 := if ef_keeps_memory ef then st1 else invalidate (fun _ => true) st1 in
      Some (sseq pre (sseq (with_result optid (fun dst => Sbuiltin dst ef tys (map (tr_expr cs) al)))
                           (result_resets optid)),
            (Some (after_result optid st2), None, None))
  | Ssequence s1 s2 =>
      match tr_stmt st s1 with
      | Some (s1', (n1, b1, c1)) =>
          match tr_stmt (default_state n1) s2 with
          | Some (s2', (n2, b2, c2)) => Some (Ssequence s1' s2', (n2, meet_opt b1 b2, meet_opt c1 c2))
          | None => None
          end
      | None => None
      end
  | Sifthenelse a s1 s2 =>
      let '(pre, st1) := reloads s st in
      match tr_stmt st1 s1, tr_stmt st1 s2 with
      | Some (s1', (n1, b1, c1)), Some (s2', (n2, b2, c2)) =>
          Some (sseq pre (Sifthenelse (tr_expr (valid_caches st1) a) s1' s2'),
                (meet_opt n1 n2, meet_opt b1 b2, meet_opt c1 c2))
      | _, _ => None
      end
  | Sloop s1 s2 =>
      (* Reload before the loop the stale caches the loop body reads first. *)
      let entry0 := fold_left (fun (st': cstate) (k: cache) =>
                                 if negb (is_valid st' k) && first_reads (ca_loc k) s1 then set_valid k st' else st')
                              cl st in
      match tr_loop (S (length (cs_valid entry0) + length (cs_copies entry0)))
                    (fun e => tr_stmt e s1) (fun e => tr_stmt e s2) entry0 with
      | Some (s1', s2', entry, o) =>
          let pre := fold_left (fun (pre: statement) (k: cache) =>
                                  if is_valid entry k && negb (is_valid st k) then sseq pre (reload k) else pre)
                               cl Sskip in
          Some (sseq pre (Sloop s1' s2'), o)
      | None => None
      end
  | Sswitch a ls =>
      let '(pre, st1) := reloads s st in
      match tr_lstmt st1 None ls with
      | Some (ls', (n, b, c)) =>
          (* Ends normally after the last case, by [break], or when no case
             matches. *)
          Some (sseq pre (Sswitch (tr_expr (valid_caches st1) a) ls'),
                (meet_opt (meet_opt n b) (Some st1), None, c))
      | None => None
      end
  | Slabel l s1 =>
      (* A [goto] may jump here from anywhere. *)
      match tr_stmt empty_state s1 with
      | Some (s1', o) => Some (Slabel l s1', o)
      | None => None
      end
  end
(** Cases: each is entered from the switch ([st]) or by falling through from
    the case before ([prev]). *)
with tr_lstmt (st: cstate) (prev: option cstate) (ls: labeled_statements)
              : option (labeled_statements * outcome) :=
  match ls with
  | LSnil => Some (LSnil, (prev, None, None))
  | LScons c s ls' =>
      match tr_stmt (default_state (meet_opt prev (Some st))) s with
      | Some (s', (n, b, k)) =>
          match tr_lstmt st n ls' with
          | Some (ls'', (n', b', k')) => Some (LScons c s' ls'', (n', meet_opt b b', meet_opt k k'))
          | None => None
          end
      | None => None
      end
  end.

(** A split parameter starts as its own base, at index 0. *)
Definition entry_code (params: list (ident * type)) : statement :=
  fold_right (fun (pt: ident * type) s =>
                match sps!(fst pt) with
                | Some sp => Ssequence (Sset sp.(sp_base) (Etempvar (fst pt) (snd pt)))
                                       (Ssequence (zero_index sp) s)
                | None => s
                end)
             Sskip params.

(** Every cache starts stale, at index 0. *)
Definition cache_entry : statement :=
  fold_right (fun (k: cache) s => sseq (Sset (ca_idx k) (Econst_long Int64.zero tlong)) s) Sskip cl.

(** Every index, and every base once (members of a group may share one). *)
Definition new_temps : list (ident * type) :=
  let '(_, l) :=
    fold_left (fun (acc: PTree.t unit * list (ident * type)) (e: ident * split) =>
                 let '(seen, l) := acc in
                 let s := snd e in
                 let l := (sp_idx s, tlong) :: l in
                 if is_some seen!(sp_base s) then (seen, l)
                 else (PTree.set (sp_base s) tt seen, (sp_base s, sp_type s) :: l))
              (PTree.elements sps) (PTree.empty unit, nil) in
  rev l ++ flat_map (fun (k: cache) => (ca_base k, ca_type k) :: (ca_idx k, tlong) :: nil) cl.

End REWRITE.

(** Fresh identifiers start above every identifier the program uses: global
    names, composite and member names, and every function's parameters,
    variables, temporaries, field names and labels. *)
Fixpoint max_expr (e: expr) (m: positive) : positive :=
  match e with
  | Evar x _ | Etempvar x _ => Pos.max x m
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ => max_expr a m
  | Efield a f _ => max_expr a (Pos.max f m)
  | Ebinop _ a1 a2 _ => max_expr a1 (max_expr a2 m)
  | _ => m
  end.

Definition max_opt (o: option ident) (m: positive) : positive :=
  match o with Some x => Pos.max x m | None => m end.

Fixpoint max_stmt (s: statement) (m: positive) : positive :=
  match s with
  | Sassign a1 a2 => max_expr a1 (max_expr a2 m)
  | Sset x a => max_expr a (Pos.max x m)
  | Scall o a al => max_opt o (max_expr a (fold_right max_expr m al))
  | Sbuiltin o _ _ al => max_opt o (fold_right max_expr m al)
  | Ssequence s1 s2 | Sloop s1 s2 => max_stmt s1 (max_stmt s2 m)
  | Sifthenelse a s1 s2 => max_expr a (max_stmt s1 (max_stmt s2 m))
  | Sreturn (Some a) => max_expr a m
  | Sswitch a ls => max_expr a (max_lstmt ls m)
  | Slabel l s1 => max_stmt s1 (Pos.max l m)
  | Sgoto l => Pos.max l m
  | _ => m
  end
with max_lstmt (ls: labeled_statements) (m: positive) : positive :=
  match ls with
  | LSnil => m
  | LScons _ s ls' => max_stmt s (max_lstmt ls' m)
  end.

Definition max_vars (l: list (ident * type)) (m: positive) : positive :=
  fold_left (fun m (it: ident * type) => Pos.max (fst it) m) l m.

Definition max_composite (m: positive) (c: composite_definition) : positive :=
  match c with
  | Composite id _ ms _ => fold_left (fun (m: positive) (mb: member) => Pos.max (name_member mb) m) ms (Pos.max id m)
  end.

Definition max_program (p: program) : positive :=
  fold_left (fun m (d: ident * globdef fundef type) =>
               let m := Pos.max (fst d) m in
               match snd d with
               | Gfun (Internal f) =>
                   max_stmt f.(fn_body) (max_vars f.(fn_params) (max_vars f.(fn_vars) (max_vars f.(fn_temps) m)))
               | _ => m
               end)
            (prog_defs p) (fold_left max_composite (prog_types p) 1%positive).

(** ** Checks the proof relies on (PtrIdxproof.v)

    The rewritten function is kept only if these hold; otherwise the function
    is left unchanged. They are cheap, and the proof needs nothing else from
    how the splits and caches were chosen. *)

Section CHECKS.

Variable ce: composite_env.
Variable sps: splits.

Definition is_void (t: type) : bool := match t with Tvoid => true | _ => false end.

Definition bare_split (e: expr) : bool :=
  match e with Etempvar x _ => is_some sps!x | _ => false end.

(** Every occurrence of a split temporary converts its value: it has a
    pointer type, and it is not the operand of a cast to [void]. Then the
    original program can only use the temporary's value if it is a pointer
    or an integer pointer, which [base + idx] computes; an uninitialized
    temporary is only ever copied. *)
Fixpoint uses_ok (e: expr) : bool :=
  match e with
  | Etempvar x ty => negb (is_some sps!x) || is_pointer ty
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Efield a _ _ => uses_ok a
  | Ecast a ty => uses_ok a && negb (bare_split a && is_void ty)
  | Ebinop _ a1 a2 _ => uses_ok a1 && uses_ok a2
  | _ => true
  end.

(** An expression converted to [ty] (a call argument, a returned value). *)
Definition received_ok (e: expr) (ty: type) : bool := uses_ok e && negb (bare_split e && is_void ty).

(** Arguments beyond the declared parameters (a variadic call) are not
    constrained: Clight evaluates a call only when every argument has a
    declared type ([eval_exprlist]). *)
Fixpoint args_ok (al: list expr) (tys: list type) : bool :=
  match al, tys with
  | nil, _ => true
  | a :: al', ty :: tys' => received_ok a ty && args_ok al' tys'
  | a :: al', nil => uses_ok a && args_ok al' nil
  end.

Definition call_args_ok (a: expr) (al: list expr) : bool :=
  match classify_fun (typeof a) with
  | fun_case_f tys _ _ => args_ok al tys
  | fun_default => forallb uses_ok al
  end.

(** A copy between split temporaries keeps the index (it does not start a
    new base): they count in the same unit. *)
Definition copy_ok (x: ident) (b: expr) : bool :=
  match b with
  | Etempvar q _ =>
      match sps!x, sps!q with
      | Some sx, Some sq => Z.eqb (sp_size sx) (sp_size sq)
      | _, _ => true
      end
  | _ => true
  end.

Fixpoint body_ok (ret: type) (s: statement) : bool :=
  match s with
  | Sassign a b => uses_ok a && uses_ok b
  | Sset x b => uses_ok b && copy_ok x b
  | Scall _ a al => uses_ok a && call_args_ok a al
  | Sbuiltin _ _ tys al => args_ok al tys
  | Sreturn (Some a) => received_ok a ret
  | Sifthenelse a s1 s2 => uses_ok a && body_ok ret s1 && body_ok ret s2
  | Ssequence s1 s2 | Sloop s1 s2 => body_ok ret s1 && body_ok ret s2
  | Sswitch a ls => uses_ok a && body_ok_l ret ls
  | Slabel _ s1 => body_ok ret s1
  | _ => true
  end
with body_ok_l (ret: type) (ls: labeled_statements) : bool :=
  match ls with
  | LSnil => true
  | LScons _ s ls' => body_ok ret s && body_ok_l ret ls'
  end.

(** A split's base has a pointer type, and its index counts in units of
    what that type points to. *)
Definition split_wf (s: split) : bool :=
  match sp_type s with
  | Tpointer t _ => Z.eqb (sp_size s) (sizeof ce t)
  | _ => false
  end.

Definition max_function (f: function) : positive :=
  max_stmt f.(fn_body) (max_vars f.(fn_params) (max_vars f.(fn_vars) (max_vars f.(fn_temps) 1%positive))).

Definition norepet_b (l: list ident) : bool := if list_norepet_dec ident_eq l then true else false.

Definition disjoint_b (l1 l2: list ident) : bool :=
  forallb (fun x => negb (existsb (Pos.eqb x) l2)) l1.

(** *** Shared bases

    When members of a group share one base, writing that base changes the
    value of every other member: only the written member is right afterwards.
    [lcheck] checks that no other member with the same base is live after
    any statement that writes a base, by a liveness computation over the
    members that share a base ([tracked]). Loops and labels are checked to be
    post-fixpoints: the loop head and the label sets ([labs], from the
    analysis) contain what is live at them, so nothing here needs the
    iteration to have converged. *)

Definition same_base (x y: ident) : bool :=
  match sps!x, sps!y with
  | Some sx, Some sy => Pos.eqb (sp_base sx) (sp_base sy)
  | _, _ => false
  end.

(** For each split temporary, whether another one has the same base. *)
Definition shared_tree : PTree.t bool :=
  PTree.map (fun x sx =>
               existsb (fun (ys: ident * split) => negb (Pos.eqb (fst ys) x) && Pos.eqb (sp_base (snd ys)) (sp_base sx))
                       (PTree.elements sps))
            sps.

(** [set_split] writes [x]'s base, unless [e] is [x] itself, or a copy or an
    offset of a split temporary that has the same base. *)
Definition writes_base (x: ident) (sx: split) (e: expr) : bool :=
  match e with
  | Etempvar q _ =>
      match sps!q with
      | Some sq =>
          if peq x q then false
          else if Z.eqb (sp_size sq) (sp_size sx) then negb (Pos.eqb (sp_base sx) (sp_base sq)) else true
      | None => true
      end
  | _ =>
      match offset_of e with
      | Some (q, tq, _, _, _) =>
          match sps!q with
          | Some sq =>
              if Z.eqb (elem_size ce tq) (sp_size sq) && Z.eqb (sp_size sq) (sp_size sx) then
                if peq x q then false else negb (Pos.eqb (sp_base sx) (sp_base sq))
              else true
          | None => true
          end
      | None => true
      end
  end.

Definition subset (a b: lset) : bool := forallb (fun x => lmem x b) a.

(** Another member with [x]'s base is live in [after]. *)
Definition clash (x: ident) (after: lset) : bool :=
  existsb (fun y => negb (Pos.eqb y x) && same_base x y) after.

Section LIVE.

Variable shared: PTree.t bool.
Variable labs: PTree.t lset.
Variable fuel: nat.

Definition tracked (x: ident) : bool := match shared!x with Some b => b | None => false end.

Fixpoint lu (e: expr) (s: lset) : lset :=
  match e with
  | Etempvar x _ => if tracked x then ladd x s else s
  | Ederef a _ | Eaddrof a _ | Eunop _ a _ | Ecast a _ | Efield a _ _ => lu a s
  | Ebinop _ a1 a2 _ => lu a1 (lu a2 s)
  | _ => s
  end.

Definition lab (l: ident) : lset := match labs!l with Some x => x | None => nil end.

(** A call or builtin storing its result in [o]: [with_result] writes the
    base of a split result. *)
Definition result_ok (o: option ident) (after: lset) : bool :=
  match o with
  | Some x => match sps!x with Some _ => negb (clash x after) | None => true end
  | None => true
  end.

(** The members live before [s], given those live after it ends normally,
    by [break] and by [continue], and whether the checks hold in [s]. *)
Fixpoint lcheck (s: statement) (after brk cont: lset) {struct s} : lset * bool :=
  match s with
  | Sskip => (after, true)
  | Sassign a e => (lu a (lu e after), true)
  | Sset x e =>
      (lu e (lkill x after),
       match sps!x with Some sx => negb (writes_base x sx e && clash x after) | None => true end)
  | Scall o a al => (lu a (fold_right lu (kill_opt o after) al), result_ok o after)
  | Sbuiltin o _ _ al => (fold_right lu (kill_opt o after) al, result_ok o after)
  | Ssequence s1 s2 =>
      let '(l2, ok2) := lcheck s2 after brk cont in
      let '(l1, ok1) := lcheck s1 l2 brk cont in
      (l1, ok1 && ok2)
  | Sifthenelse c s1 s2 =>
      let '(l1, ok1) := lcheck s1 after brk cont in
      let '(l2, ok2) := lcheck s2 after brk cont in
      (lu c (lunion l1 l2), ok1 && ok2)
  | Sloop s1 s2 =>
      let fix iter (n: nat) (head: lset) : lset * bool :=
        let '(l2, ok2) := lcheck s2 head after head in
        let '(l1, ok1) := lcheck s1 l2 after l2 in
        if subset l1 head then (head, ok1 && ok2)
        else match n with
             | O => (head, false)
             | S n' => iter n' (lunion l1 head)
             end in
      iter fuel nil
  | Sbreak => (brk, true)
  | Scontinue => (cont, true)
  | Sreturn None => (nil, true)
  | Sreturn (Some e) => (lu e nil, true)
  | Sswitch c ls =>
      let '(_, all, ok) := lcheck_l ls after cont in
      (lu c (lunion all after), ok)
  | Slabel l s1 =>
      let '(l1, ok) := lcheck s1 after brk cont in
      (l1, ok && subset l1 (lab l))
  | Sgoto l => (lab l, true)
  end
with lcheck_l (ls: labeled_statements) (after cont: lset) {struct ls} : lset * lset * bool :=
  match ls with
  | LSnil => (after, after, true)
  | LScons _ s ls' =>
      let '(lr, all, ok') := lcheck_l ls' after cont in
      let '(l, ok) := lcheck s lr after cont in
      (l, lunion l all, ok && ok')
  end.

End LIVE.

(** Bases are shared only by members that are not both parameters (the
    entry code sets a parameter's base), and [lcheck] holds for the body. *)
Definition share_ok (labs: PTree.t lset) (f: function) : bool :=
  let pbases := flat_map (fun (pt: ident * type) =>
                            match sps!(fst pt) with Some sp => sp_base sp :: nil | None => nil end)
                         f.(fn_params) in
  norepet_b pbases
  && snd (lcheck shared_tree labs (S (length (PTree.elements sps))) f.(fn_body) nil nil nil).

(** The splits and caches of [f], rewritten into [tf]: every split is well
    formed; the split temporaries are [f]'s own identifiers and every new one
    is above them all; indices and cache temporaries are all distinct, and
    distinct from the bases; without sharing, the bases are distinct too, and
    shared bases pass [share_ok]; every new temporary is declared in [tf],
    and every temporary of [tf] is new or one of [f]'s; [tf]'s parameters and
    temporaries do not repeat (function entry requires it). *)
Definition plan_ok (share: bool) (labs: PTree.t lset) (cl: list cache) (f tf: function) : bool :=
  let top := max_function f in
  let els := PTree.elements sps in
  let bases := map (fun xs => sp_base (snd xs)) els in
  let others := map (fun xs => sp_idx (snd xs)) els ++ flat_map (fun k => ca_base k :: ca_idx k :: nil) cl in
  let declared := var_names tf.(fn_temps) in
  forallb (fun xs => split_wf (snd xs) && Pos.leb (fst xs) top) els
  && forallb (Pos.ltb top) (bases ++ others)
  && norepet_b others && disjoint_b others bases && (share || norepet_b bases) && share_ok labs f
  && forallb (fun x => existsb (Pos.eqb x) declared) (bases ++ others)
  && forallb (fun y => Pos.ltb top y || existsb (Pos.eqb y) (var_names f.(fn_temps))) declared
  && norepet_b (var_names (tf.(fn_params) ++ tf.(fn_temps)))
  && body_ok f.(fn_return) f.(fn_body).

End CHECKS.

(** ** Functions and programs *)

(** The rewritten function, its splits and caches, or [f] itself and none.
    The boolean says whether [f] had pointers to rewrite but was left
    unchanged, because [tr_stmt] could not rewrite it exactly or a check of
    [plan_ok] failed. [share] lets a group share one base; [mem] turns the
    caches for pointers in memory on. *)
Definition transf_function (ce: composite_env) (nw: PTree.t unit) (share mem: bool) (f: function) (next: positive)
                         : function * splits * list cache * bool * positive :=
  let '(sps, labs, next1) := plan_function ce share f next in
  let '(cl, next2) := if mem then plan_caches ce f next1 else (nil, next1) in
  match PTree.elements sps, cl with
  | nil, nil => (f, sps, nil, false, next)
  | _, _ =>
      match tr_stmt ce sps cl nw f.(fn_vars) empty_state f.(fn_body) with
      | Some (body', _) =>
          let tf := {| fn_return := f.(fn_return);
                       fn_callconv := f.(fn_callconv);
                       fn_params := f.(fn_params);
                       fn_vars := f.(fn_vars);
                       (* A split temporary is no longer read or written. *)
                       fn_temps := List.filter (fun (xt: ident * type) => negb (is_some sps!(fst xt))) f.(fn_temps)
                                   ++ new_temps sps cl;
                       fn_body := sseq (entry_code sps f.(fn_params)) (sseq (cache_entry cl) body') |} in
          if plan_ok ce sps share labs cl f tf then (tf, sps, cl, false, next2)
          else (f, PTree.empty split, nil, true, next)
      | None => (f, PTree.empty split, nil, true, next)
      end
  end.

(** Per function: whether it fell back, the pointer temporaries split, and
    the locations cached. *)
Definition plan := list (ident * (bool * list (ident * split) * list cache)).

Fixpoint transf_defs (ce: composite_env) (nw: PTree.t unit) (share mem: bool)
         (defs: list (ident * globdef fundef type)) (next: positive)
         : list (ident * globdef fundef type) * plan :=
  match defs with
  | nil => (nil, nil)
  | (id, Gfun (Internal f)) :: defs' =>
      let '(f', sps, cl, fell_back, next') := transf_function ce nw share mem f next in
      let '(defs'', pl) := transf_defs ce nw share mem defs' next' in
      ((id, Gfun (Internal f')) :: defs'', (id, (fell_back, PTree.elements sps, cl)) :: pl)
  | d :: defs' =>
      let '(defs'', pl) := transf_defs ce nw share mem defs' next in
      (d :: defs'', pl)
  end.

(** The rewritten program, and for each function the pointers that were
    split and the locations cached (for the driver: naming the new
    temporaries, and the facts file). *)
Definition transf_program_plan (share mem: bool) (p: program) : program * plan :=
  let nw := nonwriting (prog_defs p) in
  let '(defs', pl) := transf_defs (prog_comp_env p) nw share mem (prog_defs p) (Pos.succ (max_program p)) in
  ({| prog_defs := defs';
      prog_public := prog_public p;
      prog_main := prog_main p;
      prog_types := prog_types p;
      prog_comp_env := prog_comp_env p;
      prog_comp_env_eq := prog_comp_env_eq p |},
   pl).

(** The pass that PtrIdxproof.v proves correct: shared bases, no caches.
    The caches ([mem]) are an extension outside the proof (ptridxgen
    -memory). *)
Definition transf_program (p: program) : res program := OK (fst (transf_program_plan true false p)).
