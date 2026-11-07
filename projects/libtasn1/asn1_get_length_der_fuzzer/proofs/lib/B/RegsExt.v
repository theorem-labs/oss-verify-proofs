(* Register-file extensionality for LPS's RISC-V step.

   LPS represents the register file as a bvmap (a binary trie), so two register files can
   read the same at every register yet differ as trees.  The ISA semantics only ever reads a
   register through [rget] (x0 forced to 0, missing keys 0) and writes one through [rset], so
   states whose register files agree at every register other than x0 step to states that again
   agree.  This lets a proof stated for one concrete register tree (as the cjson-style proofs
   state theirs, with [mkR]) be used at any register file with the same values. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.

(* two register files agree at every register except x0 *)
Definition rext (R1 R2 : bvmap 5 word) : Prop :=
  forall r, is_x0 r = false -> reg_get R1 r = reg_get R2 r.

Lemma rext_refl : forall R, rext R R.
Proof. intros R r _. reflexivity. Qed.
Lemma rext_sym : forall R1 R2, rext R1 R2 -> rext R2 R1.
Proof. intros R1 R2 H r Hr. symmetry. apply H, Hr. Qed.
Lemma rext_trans : forall R1 R2 R3, rext R1 R2 -> rext R2 R3 -> rext R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). apply H2, Hr. Qed.

Lemma rext_set : forall R1 R2 (k : reg) v, rext R1 R2 -> rext (bvmap_set k v R1) (bvmap_set k v R2).
Proof.
  intros R1 R2 k v H r Hr. unfold reg_get, bvmap_get, bvmap_set.
  destruct (Pos.eq_dec (bv_key k) (bv_key r)) as [E|E].
  - rewrite E, !tget_tset_same. reflexivity.
  - rewrite !tget_tset_other by exact E. apply H, Hr.
Qed.

(* cores that differ at most in the register file's representation *)
Definition cext (c1 c2 : core) : Prop :=
  rext (c_regs c1) (c_regs c2) /\ c_fregs c1 = c_fregs c2 /\ c_pc c1 = c_pc c2 /\
  c_fcsr c1 = c_fcsr c2 /\ c_resv c1 = c_resv c2.

Inductive eext : eff -> eff -> Prop :=
| ee_done : forall c1 c2, cext c1 c2 -> eext (EDone c1) (EDone c2)
| ee_illegal : forall c1 c2, cext c1 c2 -> eext (EIllegal c1) (EIllegal c2)
| ee_dillegal : forall c1 c2, cext c1 c2 -> eext (EDefinedIllegal c1) (EDefinedIllegal c2)
| ee_ecall : forall c1 c2, cext c1 c2 -> eext (EEcall c1) (EEcall c2)
| ee_ebreak : forall c1 c2, cext c1 c2 -> eext (EEbreak c1) (EEbreak c2)
| ee_fault : forall c1 c2, cext c1 c2 -> eext (EFault c1) (EFault c2)
| ee_load : forall n a k1 k2, (forall v, eext (k1 v) (k2 v)) -> eext (ELoad n a k1) (ELoad n a k2)
| ee_store : forall n a v k1 k2, eext k1 k2 -> eext (EStore n a v k1) (EStore n a v k2).

Lemma rget_ext : forall R1 R2 F pc fc rv r, rext R1 R2 ->
  rget (Core R1 F pc fc rv) r = rget (Core R2 F pc fc rv) r.
Proof. intros. unfold rget. cbn [c_regs]. destruct (is_x0 r) eqn:E; [reflexivity | apply H, E]. Qed.

(* reads that do not look at the integer register file *)
Lemma fread_ext : forall R1 R2 F pc fc rv fmt r,
  fread (Core R1 F pc fc rv) fmt r = fread (Core R2 F pc fc rv) fmt r.
Proof. reflexivity. Qed.
Lemma fget_ext : forall R1 R2 F pc fc rv r, fget (Core R1 F pc fc rv) r = fget (Core R2 F pc fc rv) r.
Proof. reflexivity. Qed.
Lemma resolve_rm_ext : forall R1 R2 F pc fc rv rm v,
  resolve_rm rm (with_pc v (Core R1 F pc fc rv)) = resolve_rm rm (with_pc v (Core R2 F pc fc rv)).
Proof. reflexivity. Qed.
Lemma resolve_rm_ext0 : forall R1 R2 F pc fc rv rm,
  resolve_rm rm (Core R1 F pc fc rv) = resolve_rm rm (Core R2 F pc fc rv).
Proof. reflexivity. Qed.

(* walk two effect trees that differ only in register-file representation *)
Ltac ext_core HR :=
  unfold cext, rset, fset, fwrite, accrue, inval_resv, with_regs, with_fregs, with_pc, with_fcsr, with_resv;
  repeat (cbn [c_regs c_fregs c_pc c_fcsr c_resv];
          match goal with
          | |- context [if is_x0 ?r then _ else _] => destruct (is_x0 r)
          | |- context [if ?b then _ else _] => destruct b
          | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
          end);
  cbn [c_regs c_fregs c_pc c_fcsr c_resv];
  repeat split; try reflexivity;
  repeat (first [ exact HR | apply rext_set ]).
Ltac ext_walk HR :=
  repeat first
    [ progress (intros)
    | match goal with
      | |- eext (EDone _) (EDone _) => apply ee_done; ext_core HR
      | |- eext (EIllegal _) (EIllegal _) => apply ee_illegal; ext_core HR
      | |- eext (EDefinedIllegal _) (EDefinedIllegal _) => apply ee_dillegal; ext_core HR
      | |- eext (EEcall _) (EEcall _) => apply ee_ecall; ext_core HR
      | |- eext (EEbreak _) (EEbreak _) => apply ee_ebreak; ext_core HR
      | |- eext (EFault _) (EFault _) => apply ee_fault; ext_core HR
      | |- eext (ELoad _ _ _) (ELoad _ _ _) => apply ee_load
      | |- eext (EStore _ _ _ _) (EStore _ _ _ _) => apply ee_store
      | |- eext (load_val ?z _ _ _) _ => destruct z; cbn [load_val]
      | |- eext (store_val ?z _ _ _) _ => destruct z; cbn [store_val]
      | |- eext (exec_csr _ _ _ _ _ _) _ => unfold exec_csr
      | |- eext (match ?x with Some _ => _ | None => _ end) _ => destruct x
      | |- eext (let '(_, _) := ?x in _) _ => destruct x
      | |- eext (if ?b then _ else _) _ => destruct b
      | |- cext (if ?b then _ else _) _ => destruct b
      | |- context [match ?x with AW => _ | AD => _ end] => destruct x
      | |- context [match ?x with FMT_S => _ | FMT_D => _ end] => destruct x
      | |- context [match ?x with SZ1 => _ | SZ2 => _ | SZ4 => _ | SZ8 => _ end] => destruct x
      | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
      | |- context [match ?x with (_, _) => _ end] => destruct x
      end ].

Lemma exec_ext : forall sz i R1 R2 F pc fc rv, rext R1 R2 ->
  eext (exec sz i (Core R1 F pc fc rv)) (exec sz i (Core R2 F pc fc rv)).
Proof.
  intros sz i R1 R2 F pc fc rv HR.
  destruct i; repeat match goal with x : fcvt_ty |- _ => destruct x end;
  cbn [exec]; rewrite ?(rget_ext R1 R2 F pc fc rv _ HR);
  rewrite ?(fread_ext R1 R2 F pc fc rv), ?(fget_ext R1 R2 F pc fc rv), ?(resolve_rm_ext R1 R2 F pc fc rv),
          ?(resolve_rm_ext0 R1 R2 F pc fc rv);
  cbn -[rget is_x0 bvmap_set alu64 alu32 mul_div sext zext low32 bv_extract amo_val
        slice_get slice_set csr_slice csr_write_illegal];
  cbn [fread fget c_fregs c_fcsr c_regs c_pc c_resv];
  ext_walk HR.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.

(* machine states that differ at most in the register file's representation *)
Definition msext (s1 s2 : machine_state) : Prop :=
  rext (ms_regs s1) (ms_regs s2) /\ ms_fregs s1 = ms_fregs s2 /\ ms_pc_val s1 = ms_pc_val s2 /\
  ms_svc_pending s1 = ms_svc_pending s2 /\ ms_resv s1 = ms_resv s2 /\ ms_fcsr s1 = ms_fcsr s2 /\
  ms_mem s1 = ms_mem s2 /\ ms_rom s1 = ms_rom s2.

Lemma ms_reg_ext : forall s1 s2 r, msext s1 s2 -> ms_reg s1 r = ms_reg s2 r.
Proof.
  intros s1 s2 r H. unfold ms_reg. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply (proj1 H). exact E.
Qed.

Section S.
Variable segs : list Segment.

(* the interpreter runs related effect trees against the same memory to related cores *)
Lemma interp_ext : forall e1 e2, eext e1 e2 -> forall m,
  match interp_eff_accesses segs e1 m, interp_eff_accesses segs e2 m with
  | MachineOk r1, MachineOk r2 =>
      cext (fst (access_value _ r1)) (fst (access_value _ r2)) /\ snd (access_value _ r1) = snd (access_value _ r2)
  | MachineFault, MachineFault | MachineUnmodeled, MachineUnmodeled => True
  | _, _ => False
  end.
Proof.
  intros e1 e2 H. induction H; intros m; cbn [interp_eff_accesses]; try exact I.
  - cbn [access_value fst snd]. split; [exact H | reflexivity].
  - match goal with |- context [match ov_read_bytes ?s ?mm ?aa ?nn with _ => _ end] =>
      destruct (ov_read_bytes s mm aa nn) as [bs|] end; [|exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k1 _) m), (interp_eff_accesses segs (k2 _) m); try contradiction; try exact I.
    cbn [access_value]. exact H0.
  - match goal with |- context [if store_ok ?s ?mm ?aa ?nn then _ else _] =>
      destruct (store_ok s mm aa nn) end; [|exact I].
    match goal with |- context [interp_eff_accesses segs k1 ?mm'] => specialize (IHeext mm') end.
    destruct (interp_eff_accesses segs k1 _), (interp_eff_accesses segs k2 _); try contradiction; try exact I.
    cbn [access_value]. exact IHeext.
Qed.


Lemma step_ext : forall s1 s2 s1', msext s1 s2 -> step segs s1 = MachineOk s1' ->
  exists s2', step segs s2 = MachineOk s2' /\ msext s1' s2'.
Proof.
  intros s1 s2 s1' H Hs.
  pose proof H as (HR & HF & HP & HV & HRv & HC & HM & HO).
  destruct s1 as [r1 f1 p1 v1 rv1 c1 m1 o1], s2 as [r2 f2 p2 v2 rv2 c2 m2 o2]; cbn in *; subst.
  unfold step, drop_access_report, step_accesses in *.
  unfold ms_pc in *; cbn [ms_pc_val ms_mem] in *.
  assert (DE : forall w,
    match decode_exec_accesses segs (Build_machine_state r1 f2 p2 v2 rv2 c2 m2 o2) w,
          decode_exec_accesses segs (Build_machine_state r2 f2 p2 v2 rv2 c2 m2 o2) w with
    | MachineOk a1, MachineOk a2 => msext (access_value _ a1) (access_value _ a2)
    | MachineFault, MachineFault | MachineUnmodeled, MachineUnmodeled => True
    | _, _ => False
    end).
  { intros w. unfold decode_exec_accesses. match goal with |- context [if ?b then _ else _] => destruct b end.
    - cbn [access_value]. unfold msext; cbn.
      rewrite (ms_reg_ext (Build_machine_state r1 f2 p2 v2 rv2 c2 m2 o2) (Build_machine_state r2 f2 p2 v2 rv2 c2 m2 o2) 17 H).
      repeat split; try reflexivity. exact HR.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); exact I].
      cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem].
      pose proof (interp_ext _ _ (exec_ext (Z_to_bv 64 isz) i r1 r2 f2 p2 c2 rv2 HR) m2) as X.
      destruct (interp_eff_accesses segs (exec _ i (Core r1 f2 p2 c2 rv2)) m2) as [a1| |],
               (interp_eff_accesses segs (exec _ i (Core r2 f2 p2 c2 rv2)) m2) as [a2| |]; try contradiction; try exact I.
      destruct (access_value _ a1) as [k1 mm1], (access_value _ a2) as [k2 mm2]. cbn [fst snd] in X.
      destruct X as ((XR & XF & XP & XC & XV) & <-). cbn [access_value]. unfold msext; cbn. repeat split; auto. }
  destruct (fetch_word segs p2) as [w|]; [|destruct (fetch_word_ov segs m2 p2) as [w|];
    [|destruct (fetch_tail_any segs m2 p2) as [w|]]].
  all: try (specialize (DE w);
            destruct (decode_exec_accesses segs (Build_machine_state r1 f2 p2 v2 rv2 c2 m2 o2) w) as [a1| |];
            [| discriminate | discriminate];
            destruct (decode_exec_accesses segs (Build_machine_state r2 f2 p2 v2 rv2 c2 m2 o2) w) as [a2| |];
            try contradiction; cbn [access_value] in Hs |- *; injection Hs as <-; eexists; split; [reflexivity | exact DE]).
  destruct (fetch_failure segs m2 p2) as [st'| |]; [|discriminate|discriminate].
  cbn [access_value] in Hs |- *. injection Hs as <-. eexists; split; [reflexivity|].
  unfold msext; repeat split; try reflexivity; try apply rext_refl.
Qed.
End S.
