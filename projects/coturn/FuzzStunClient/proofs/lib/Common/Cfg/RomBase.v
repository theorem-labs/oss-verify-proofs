(* SPDX-License-Identifier: MIT *)
(* Bridge (B2) part 1 for coturn's FuzzStunClient:
   the read-only backing of a state, and the system calls whose specification does not change
   when that backing grows.

   Made, statement and proof, from
     projects/bzip2/bzip2_compress_target/proofs/lib/Common/Cfg/RomBase.v
   lines 1-255, as in the LPS 727298f3 update.  In this file:
   - [sys_rob] is stated at each vDSO layer (its comment below says why), with [sys_rob_plain] for
     the source's form; the source's [read_bytes_aux_ext] and [read_bytes_map_ext] are not here;
   - the [memfree] lemmas cover the numbers coturn's walk issues.  Of the numbers proofs/lib
     names (29, 56, 57, 63, 64, 66, 93/94, 96, 214, 215, 222, 226), 57, 63, 93, 94, 96, 214,
     215, 222 and 226 are memfree; 29, 56, 64 and 66 read [in_mem] and are discharged at their
     nodes, not here.  172-178, 216 and 233 are memfree too: they cost one [reflexivity] each,
     and a walk that grows a getuid node does not need this file reopened.

   WHY ONLY A SYSTEM CALL CARES.  [ms_rom] is read by exactly one thing: [Run.sys_input]'s
   [in_mem], which is [RiscvSemantics.ms_read_byte] ([ms_mem] first, then [ms_rom]).  No
   machine step reads it -- [RiscvSemantics.step_accesses] goes through [ms_mem] and the
   segment list -- so an instruction configuration has nothing to show. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Monad Specs Vdso Run VdsoCommute VdsoCommuteSys.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.

Definition wrom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Lemma wrom_eta : forall ms, wrom ms (ms_rom ms) = ms.
Proof. intros []; reflexivity. Qed.

Definition cwrom (c : config) (r : word -> option byte) : config :=
  mkCfg (wrom (cfg_ms c) r) (cfg_model c).

(** [r2] answers every byte [r1] answers, the same way. *)
Definition rom_ext (r1 r2 : word -> option byte) : Prop :=
  forall a b, r1 a = Some b -> r2 a = Some b.

Lemma rom_ext_refl : forall r, rom_ext r r.
Proof. intros r a b H. exact H. Qed.

Lemma rom_ext_trans : forall r1 r2 r3, rom_ext r1 r2 -> rom_ext r2 r3 -> rom_ext r1 r3.
Proof. intros r1 r2 r3 H1 H2 a b H. apply H2, H1, H. Qed.

(** The process's read view grows with the backing. *)
Lemma ms_read_byte_wrom_ext : forall ms r a b,
  rom_ext (ms_rom ms) r -> ms_read_byte ms a = Some b -> ms_read_byte (wrom ms r) a = Some b.
Proof.
  intros ms r a b Hr. unfold ms_read_byte. cbn [ms_mem ms_rom wrom].
  destruct (ms_mem ms a); [intro H; exact H | apply Hr].
Qed.

Lemma ms_read_bytes_aux_wrom : forall n ms r a bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes_aux ms a n = Some bs ->
  ms_read_bytes_aux (wrom ms r) a n = Some bs.
Proof.
  induction n as [|n IH]; intros ms r a bs Hr H; [exact H|].
  cbn [ms_read_bytes_aux] in *.
  destruct (ms_read_byte ms a) as [b|] eqn:E; [|discriminate H].
  rewrite (ms_read_byte_wrom_ext ms r a b Hr E).
  destruct (ms_read_bytes_aux ms (a + 1) n) as [rest|] eqn:E2; [|discriminate H].
  rewrite (IH ms r (a + 1) rest Hr E2). exact H.
Qed.

Lemma ms_read_bytes_wrom : forall ms r a len bs,
  rom_ext (ms_rom ms) r -> ms_read_bytes ms a len = Some bs ->
  ms_read_bytes (wrom ms r) a len = Some bs.
Proof. intros ms r a len bs Hr. unfold ms_read_bytes. apply ms_read_bytes_aux_wrom. exact Hr. Qed.

(** ** System calls whose specification does not read [in_mem] *)
Definition with_mem (i : SyscallInput) (mp : word -> option byte) : SyscallInput :=
  mkInput (in_sysno i) (in_args i) mp (in_wmem i).

Definition memfree (no : Z) : Prop :=
  forall i mp eff m, bv_unsigned (in_sysno i) = no ->
  check_syscall (with_mem i mp) eff m = check_syscall i eff m.

Ltac memfree_tac := intros i mp eff m H; unfold check_syscall; cbn [with_mem in_sysno]; rewrite H; reflexivity.

Lemma memfree_57 : memfree 57. Proof. memfree_tac. Qed.
Lemma memfree_63 : memfree 63. Proof. memfree_tac. Qed.
Lemma memfree_93 : memfree 93. Proof. memfree_tac. Qed.
Lemma memfree_94 : memfree 94. Proof. memfree_tac. Qed.
Lemma memfree_96 : memfree 96. Proof. memfree_tac. Qed.
Lemma memfree_214 : memfree 214. Proof. memfree_tac. Qed.
Lemma memfree_215 : memfree 215. Proof. memfree_tac. Qed.
Lemma memfree_222 : memfree 222. Proof. memfree_tac. Qed.
Lemma memfree_216 : memfree 216. Proof. memfree_tac. Qed.
Lemma memfree_226 : memfree 226. Proof. memfree_tac. Qed.
Lemma memfree_233 : memfree 233. Proof. memfree_tac. Qed.
Lemma memfree_172 : memfree 172. Proof. memfree_tac. Qed.
Lemma memfree_173 : memfree 173. Proof. memfree_tac. Qed.
Lemma memfree_174 : memfree 174. Proof. memfree_tac. Qed.
Lemma memfree_175 : memfree 175. Proof. memfree_tac. Qed.
Lemma memfree_176 : memfree 176. Proof. memfree_tac. Qed.
Lemma memfree_177 : memfree 177. Proof. memfree_tac. Qed.
Lemma memfree_178 : memfree 178. Proof. memfree_tac. Qed.

Ltac memfree_lit :=
  first [ exact memfree_57 | exact memfree_63 | exact memfree_93 | exact memfree_94
        | exact memfree_96 | exact memfree_214 | exact memfree_215 | exact memfree_222
        | exact memfree_226 | exact memfree_233 | exact memfree_172 | exact memfree_173
        | exact memfree_174 | exact memfree_175 | exact memfree_176 | exact memfree_177
        | exact memfree_178 | exact memfree_216 ].

(** ** Reads that succeed are the same over a larger memory view *)
Definition mem_ext (mp mp' : word -> option byte) : Prop :=
  forall a b, mp a = Some b -> mp' a = Some b.

Lemma mem_ext_read_byte_wrom : forall ms r,
  rom_ext (ms_rom ms) r -> mem_ext (ms_read_byte ms) (ms_read_byte (wrom ms r)).
Proof. intros ms r Hr a b. apply ms_read_byte_wrom_ext. exact Hr. Qed.

Lemma read_cstr_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  read_cstr_aux mp' a k = read_cstr_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux] in *.
  destruct (negb (access_okb a 1)); [exfalso; apply Hnf; reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  destruct (read_cstr_aux mp (a + 1) k) as [r| |] eqn:E2.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - rewrite (IH mp mp' (a + 1) Hx ltac:(rewrite E2; discriminate)), E2. reflexivity.
  - exfalso. apply Hnf. reflexivity.
Qed.

Lemma cstr_access_len_aux_ext : forall k mp mp' a,
  mem_ext mp mp' -> read_cstr_aux mp a k <> CstrFault ->
  cstr_access_len_aux mp' a k = cstr_access_len_aux mp a k.
Proof.
  induction k as [|k IH]; intros mp mp' a Hx Hnf; [reflexivity|].
  cbn [read_cstr_aux cstr_access_len_aux] in *.
  destruct (negb (access_okb a 1)); [reflexivity|].
  destruct (mp a) as [b|] eqn:E; [|exfalso; apply Hnf; reflexivity].
  rewrite (Hx a b E).
  destruct (bv_eqb b (Z_to_bv 8 0)); [reflexivity|].
  rewrite (IH mp mp' (a + 1) Hx); [reflexivity|].
  intro Hf. apply Hnf. rewrite Hf. reflexivity.
Qed.

Lemma read_cstr_ext : forall mp mp' a,
  mem_ext mp mp' -> read_cstr mp a <> CstrFault -> read_cstr mp' a = read_cstr mp a.
Proof. intros mp mp' a. apply read_cstr_aux_ext. Qed.

Section Seg.
Variable segs : list Segment.

(** At a system-call configuration, the specification is the same for every larger backing.
    An instruction configuration has nothing to show.

    QUANTIFIED OVER THE vDSO LAYER, and that is not decoration.  Bridge (A)
    (Common/VdsoBridge.v) rebuilds every node of a derivation at [cfg_with_vdso v c], so it needs
    [sys_rob] there, and the plain form does not give it: LPS's [vdso_commutes] maps an outcome
    through [outcome_with_vdso] rather than fixing it ([c0dd863a:theories/LinuxProcessSem/VdsoCommute.v:60-61],
    [c0dd863a:theories/LinuxProcessSem/VdsoCommute.v:108-115]), and the
    model deliberately does NOT claim that a specification leaves the draw where it found it
    ([c0dd863a:theories/LinuxProcessSem/VdsoCommute.v:101-107]).  So the naive transport loses the outcome.  Quantifying the layer
    here instead costs nothing at any node — [memfree] is already stated for every model, and
    the write nodes need only [fd1chan (with_vdso v model)], which holds because [with_vdso]
    touches [m_vdso] alone — and it makes [sys_rob_with_vdso] one [with_vdso_idem].
    [sys_rob_plain] recovers the naive form by [with_vdso_same]. *)
Definition sys_rob (c : config) : Prop :=
  forall r x8, rom_ext (ms_rom (cfg_ms c)) r -> ms_svc_pending (cfg_ms c) = Some x8 ->
  forall v o, syscall_spec (sys_input segs (wrom (cfg_ms c) r) x8) (with_vdso v (cfg_model c)) o
              <-> syscall_spec (sys_input segs (cfg_ms c) x8) (with_vdso v (cfg_model c)) o.

Lemma sys_rob_plain : forall c, sys_rob c ->
  forall r x8, rom_ext (ms_rom (cfg_ms c)) r -> ms_svc_pending (cfg_ms c) = Some x8 ->
  forall o, syscall_spec (sys_input segs (wrom (cfg_ms c) r) x8) (cfg_model c) o
            <-> syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) o.
Proof.
  intros c Hrob r x8 Hr Hs o.
  pose proof (Hrob r x8 Hr Hs (m_vdso (cfg_model c)) o) as H.
  rewrite with_vdso_same in H. exact H.
Qed.

Lemma sys_rob_with_vdso : forall v ms m,
  sys_rob (mkCfg ms m) -> sys_rob (mkCfg ms (with_vdso v m)).
Proof.
  intros v ms m Hrob r x8 Hr Hs w o. cbn [cfg_ms cfg_model] in *.
  rewrite !with_vdso_idem. exact (Hrob r x8 Hr Hs w o).
Qed.

(** The form bridge (A) consumes. *)
Lemma sys_rob_cfg_with_vdso : forall v c, sys_rob c -> sys_rob (cfg_with_vdso v c).
Proof. intros v [ms m] H. exact (sys_rob_with_vdso v ms m H). Qed.

Lemma sys_rob_instr : forall c, ms_svc_pending (cfg_ms c) = None -> sys_rob c.
Proof. intros c H r x8 _ H'. congruence. Qed.

(** By the executable check: a check that is the same for the larger backing. *)
Lemma sys_rob_of_check : forall ms m,
  (forall r x8, rom_ext (ms_rom ms) r -> ms_svc_pending ms = Some x8 ->
     forall v eff, check_syscall (sys_input segs (wrom ms r) x8) eff (with_vdso v m)
                   = check_syscall (sys_input segs ms x8) eff (with_vdso v m)) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m H r x8 Hr Hs v o. cbn [cfg_ms cfg_model] in *.
  destruct o as [eff m' evs|].
  - rewrite <- !check_syscall_ok_iff. rewrite (H r x8 Hr Hs v eff). reflexivity.
  - set (e0 := mkEffect (Z_to_bv 64 0) [] []).
    rewrite <- (check_syscall_err_iff (sys_input segs (wrom ms r) x8) e0 (with_vdso v m)).
    rewrite <- (check_syscall_err_iff (sys_input segs ms x8) e0 (with_vdso v m)).
    rewrite (H r x8 Hr Hs v e0). reflexivity.
Qed.

(** By a characterisation of the outcomes that holds at every larger backing (the original
    backing included), at each vDSO layer. *)
Lemma sys_rob_of_char : forall ms m x8 (Q : VdsoRun -> outcome SyscallEffect -> Prop),
  ms_svc_pending ms = Some x8 ->
  (forall r v, rom_ext (ms_rom ms) r ->
     forall o, syscall_spec (sys_input segs (wrom ms r) x8) (with_vdso v m) o <-> Q v o) ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Q Hs HQ r x8' Hr Hs' v o. cbn [cfg_ms cfg_model] in *.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite (HQ r v Hr o).
  pose proof (HQ (ms_rom ms) v (rom_ext_refl _) o) as H0. rewrite wrom_eta in H0.
  symmetry. exact H0.
Qed.

Lemma sys_input_wrom : forall ms r x8,
  sys_input segs (wrom ms r) x8 = with_mem (sys_input segs ms x8) (ms_read_byte (wrom ms r)).
Proof. reflexivity. Qed.

(** A system call whose specification does not read [in_mem]: [memfree] is stated for EVERY
    model, so the vDSO layer costs nothing here. *)
Lemma sys_rob_memfree : forall ms m x8,
  ms_svc_pending ms = Some x8 -> memfree (bv_unsigned x8) -> sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs Hmf. apply sys_rob_of_check. intros r x8' Hr Hs' v eff.
  rewrite Hs in Hs'. injection Hs' as <-.
  rewrite sys_input_wrom. apply Hmf. reflexivity.
Qed.

(** exit (93) and exit_group (94). *)
Lemma sys_rob_exit : forall ms m x8,
  ms_svc_pending ms = Some x8 -> (bv_unsigned x8 = 93 \/ bv_unsigned x8 = 94)%Z ->
  sys_rob (mkCfg ms m).
Proof.
  intros ms m x8 Hs [E|E]; apply (sys_rob_memfree ms m x8 Hs); rewrite E;
    first [exact memfree_93 | exact memfree_94].
Qed.
End Seg.

(** [memfree] at a number a hypothesis names. *)
Ltac memfree_auto :=
  repeat match goal with
         | H : bv_unsigned ?x = _ |- memfree (bv_unsigned ?x) => rewrite H
         | H : ?x = Z_to_bv 64 _ |- memfree (bv_unsigned ?x) =>
             rewrite H; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small by (unfold bv_modulus; lia)
         end;
  memfree_lit.

(** [sys_rob] at an instruction configuration, or at a system call whose number a hypothesis
    names and whose specification does not read [in_mem]. *)
Ltac rob_auto :=
  first
    [ apply sys_rob_instr; cbn [cfg_ms]; first [assumption | reflexivity]
    | eapply sys_rob_memfree; [first [eassumption | reflexivity] |]; memfree_auto ].
