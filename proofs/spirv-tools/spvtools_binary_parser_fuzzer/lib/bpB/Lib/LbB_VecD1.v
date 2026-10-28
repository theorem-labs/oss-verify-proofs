(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition VDESTROY : Z := 0xe8e94.
Definition VD_SHR_RET : Z := 0xe9188.
Definition VD_DEL_RET : Z := 0xe90c8.

Definition VD_STACK : Z := 48 + AINTRIN_STACK.

Definition VD_LOOP : Z := 0xe9000.
Definition VD_LOOPX : Z := 0xe900c.

Lemma vd_add_u : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma vd_mul_u : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma vd_s64 : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite (SymExec3.SX2.swrap_small 64 (bv_unsigned (Z_to_bv 64 z)) (2 ^ 63) (2 ^ 64));
    [| reflexivity | reflexivity | rewrite u64_of_Z by lia; lia | lia].
  rewrite u64_of_Z by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma vd_sra : forall a k, 0 <= a < 2 ^ 63 -> 0 <= k < 64 ->
  alu64 ALU_SRA (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a / 2 ^ k).
Proof.
  intros a k Ha Hk. apply bv_eq.
  change (alu64 ALU_SRA (Z_to_bv 64 a) (Z_to_bv 64 k))
    with (bv_ashiftr (Z_to_bv 64 a) (bv_and (Z_to_bv 64 k) (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite vd_s64 by lia.
  rewrite (Z.mod_small k), (Z.mod_small 63) by lia.
  replace (Z.land k 63) with k.
  2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= a / 2 ^ k <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; try lia; nia]).
  rewrite ?bv_wrap64_mod, ?Z.mod_small by lia. reflexivity.
Qed.

Lemma vd_nw : forall P n, 0 <= n -> 4 * n < 2 ^ 63 ->
  alu64 ALU_SRA (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 P)) (Z_to_bv 64 (P + 4 * n))) (Z_to_bv 64 2)
  = Z_to_bv 64 n.
Proof.
  intros P n H1 H2. rewrite vd_mul_u, vd_add_u. replace (-1 * P + (P + 4 * n)) with (4 * n) by lia.
  rewrite vd_sra by lia. f_equal. change (2 ^ 2) with 4. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Ltac vd_scb :=
  cbn [sc_denot]; evs; cbn [edenot];
  rewrite ?vd_nw by lia; rewrite ?w_mul by lia; rewrite ?w_add by lia; rewrite ?w_srl by lia; rewrite ?Z.div_small by lia; rewrite ?w_sltu by lia;
  repeat match goal with |- context [?a <? ?b] =>
    first [ replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) ] end;
  rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.
Ltac vd_sc := first [ sc_dj | sc_shdj | sc_br | vd_scb ].

Definition vdl_sr : list expr := srs sr_id [(16%bv, EVar 32); (13%bv, EVar 33); (15%bv, ELit 4)].
Definition vdl_kn : list kentry := [KRange (EVar 32) 8 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 47)].
Definition vdlT_x := sym_exec asegs 40 true [VD_LOOP; VD_LOOPX] (SCR [true] [] []) (SS VD_LOOP vdl_sr [] vdl_kn 40) [].
Definition vdlT_ss : sym_state := Eval vm_compute in fst (fst vdlT_x).
Definition vdlT_scs : list sidecond := Eval vm_compute in snd (fst vdlT_x).
Lemma vdlT_eq : vdlT_x = (vdlT_ss, vdlT_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vdlT_regs : s_regs vdlT_ss = sr_upd vdl_sr (ridx 16%bv) (EAlu ALU_ADD (EVar 32) (ELit (-4))).
Proof. vm_compute. reflexivity. Qed.
Definition vdlX_x := sym_exec asegs 40 true [VD_LOOP; VD_LOOPX] (SCR [false] [] []) (SS VD_LOOP vdl_sr [] vdl_kn 40) [].
Definition vdlX_ss : sym_state := Eval vm_compute in fst (fst vdlX_x).
Definition vdlX_scs : list sidecond := Eval vm_compute in snd (fst vdlX_x).
Lemma vdlX_eq : vdlX_x = (vdlX_ss, vdlX_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.
Lemma vdlX_regs : s_regs vdlX_ss = sr_upd vdl_sr (ridx 16%bv) (EAlu ALU_ADD (EVar 32) (ELit (-4))).
Proof. vm_compute. reflexivity. Qed.

Lemma vdl_step : forall (fx : PropExec.FPState) (R : bvmap 5 word) (m rom : word -> option byte) (x p : Z) (b : bool),
  getr R 16%bv = Z_to_bv 64 x -> getr R 13%bv = Z_to_bv 64 p -> getr R 15%bv = Z_to_bv 64 4 ->
  8 <= x <= 2 ^ 47 -> 1 <= p <= 2 ^ 47 -> (x - 4 =? p) = negb b ->
  exists R', CatSim.msteps asegs (@PropExec.mkst fx R (Z_to_bv 64 VD_LOOP) m rom)
                              (@PropExec.mkst fx R' (Z_to_bv 64 (if b then VD_LOOP else VD_LOOPX)) m rom)
    /\ forall r, getr R' r = getr (regupd R 16%bv (Z_to_bv 64 (x - 4))) r.
Proof.
  intros fx R m rom x p b H16 H13 H15 Hx Hp Hb.
  set (E := Eseed R [Z_to_bv 64 x; Z_to_bv 64 p]).
  assert (HR : regs_ok E vdl_sr R).
  { unfold vdl_sr. apply regs_ok_srs; [apply regs_ok_seed|].
    repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs; assumption. }
  assert (HK : know_ok asegs E m vdl_kn).
  { unfold know_ok, vdl_kn.
    repeat (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
  assert (HU : regs_ok E (sr_upd vdl_sr (ridx 16%bv) (EAlu ALU_ADD (EVar 32) (ELit (-4))))
                       (regupd R 16%bv (Z_to_bv 64 (x - 4)))).
  { exact (regs_ok_upd E vdl_sr R 16%bv (Z_to_bv 64 (x - 4)) (EAlu ALU_ADD (EVar 32) (ELit (-4))) HR
             ltac:(subst E; evs; rewrite vd_add_u; f_equal; lia)). }
  destruct b.
  - assert (HS : scs_denot asegs m E vdlT_scs).
    { unfold vdlT_scs. split_scs. cbn [sc_denot]. subst E; evs. rewrite vd_add_u, br_ne by lia.
      replace (x + -4) with (x - 4) by lia. rewrite Hb. reflexivity. }
    destruct (@run_sound fx asegs _ _ _ _ _ _ _ _ _ _ E m rom R vdlT_eq HR HK HS) as (R' & HR' & _ & HM).
    exists R'. split; [exact HM|].
    intros r. rewrite (HR' r), vdlT_regs. symmetry. exact (HU r).
  - assert (HS : scs_denot asegs m E vdlX_scs).
    { unfold vdlX_scs. split_scs. cbn [sc_denot]. subst E; evs. rewrite vd_add_u, br_ne by lia.
      replace (x + -4) with (x - 4) by lia. rewrite Hb. reflexivity. }
    destruct (@run_sound fx asegs _ _ _ _ _ _ _ _ _ _ E m rom R vdlX_eq HR HK HS) as (R' & HR' & _ & HM).
    exists R'. split; [exact HM|].
    intros r. rewrite (HR' r), vdlX_regs. symmetry. exact (HU r).
Qed.

Lemma vd_loop : forall (fx : PropExec.FPState) (k : nat) (R : bvmap 5 word) (m rom : word -> option byte) (p : Z),
  getr R 16%bv = Z_to_bv 64 (p + 4 * Z.of_nat (S k)) -> getr R 13%bv = Z_to_bv 64 p -> getr R 15%bv = Z_to_bv 64 4 ->
  4 <= p -> p + 4 * Z.of_nat (S k) <= 2 ^ 47 ->
  exists R', CatSim.msteps asegs (@PropExec.mkst fx R (Z_to_bv 64 VD_LOOP) m rom)
                              (@PropExec.mkst fx R' (Z_to_bv 64 VD_LOOPX) m rom)
    /\ forall r, getr R' r = getr (regupd R 16%bv (Z_to_bv 64 p)) r.
Proof.
  intros fx k. induction k as [|k IH]; intros R m rom p H16 H13 H15 Hp Hpk.
  - destruct (vdl_step fx R m rom (p + 4 * Z.of_nat 1) p false) as (R' & HM & HE);
      [exact H16 | exact H13 | exact H15 | lia | lia | apply Z.eqb_eq; lia |].
    exists R'. split; [exact HM|]. intros r. rewrite HE. replace (p + 4 * Z.of_nat 1 - 4) with p by lia. reflexivity.
  - assert (N16 : (16%bv : reg) <> 0%bv) by (intros X; discriminate X).
    destruct (vdl_step fx R m rom (p + 4 * Z.of_nat (S (S k))) p true) as (R2 & HM2 & HE2);
      [exact H16 | exact H13 | exact H15 | lia | lia | apply Z.eqb_neq; lia |].
    destruct (IH R2 m rom p) as (R3 & HM3 & HE3).
    { rewrite HE2, getr_same by exact N16. f_equal. lia. }
    { rewrite HE2, getr_other by (intros X; discriminate X). exact H13. }
    { rewrite HE2, getr_other by (intros X; discriminate X). exact H15. }
    { lia. }
    { lia. }
    exists R3. split; [eapply CatSim.msteps_trans; [exact HM2 | exact HM3]|].
    intros r. rewrite HE3. destruct (decide (r = 16%bv)) as [->|Hr].
    + rewrite !getr_same by exact N16. reflexivity.
    + rewrite !getr_other by exact Hr. rewrite HE2, getr_other by exact Hr. reflexivity.
Qed.

Definition vda_sr : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33)].
Definition vda_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 32) 0) 8 (EVar 34); KWord (SA (EVar 34) 0) 8 (EVar 35);
    KWord (SA (EVar 34) 8) 8 (EVar 37); KWord (SA (EVar 34) 16) 8 (EVar 37);
    KWr (SA (EVar 33) (-64)) (ELit 64); KWr (SA (EVar 34) 8) (ELit 8);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KAlign (EVar 33) 16;
    KRange (EVar 32) (2 ^ 45) (2 ^ 47); KAlign (EVar 32) 8;
    KRange (EVar 34) AIMG_TOP (2 ^ 47); KAlign (EVar 34) 8;
    KRange (EVar 35) AIMG_TOP (2 ^ 47); KAlign (EVar 35) 16;
    KRange (EVar 36) 1 (2 ^ 24); KRange (EVar 37) AIMG_TOP (2 ^ 47) ].
Definition vda_knF : list kentry :=
  Eval vm_compute in kn_fix 30 [AANNOTATE_CC] (SCR (repeat false 30) [] []) VDESTROY vda_sr vda_kn 40.
Definition vda_x := sym_exec asegs 400 true [VD_LOOP] (SCR [false] [] []) (SS VDESTROY vda_sr [] vda_knF 40) [].
Definition vda_ss : sym_state := Eval vm_compute in fst (fst vda_x).
Definition vda_scs : list sidecond := Eval vm_compute in snd (fst vda_x).
Lemma vda_eq : vda_x = (vda_ss, vda_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.

Definition vdb_ss0 : sym_state :=
  SS VD_LOOPX (sr_upd (s_regs vda_ss) (ridx 16%bv) (EVar 35)) (s_log vda_ss) (s_know vda_ss) (s_next vda_ss).
Definition vdb_x := sym_exec asegs 400 true [AANNOTATE_CC] (SCR [false; false; false; false] [] []) vdb_ss0 [].
Definition vdb_ss : sym_state := Eval vm_compute in fst (fst vdb_x).
Definition vdb_scs : list sidecond := Eval vm_compute in snd (fst vdb_x).
Lemma vdb_eq : vdb_x = (vdb_ss, vdb_scs, SCR [] [] []).
Proof. vm_compute. reflexivity. Qed.

Section VecD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.

  Definition shw (x : Z) : word := alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880).

  Definition vd_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Dd V P n lo shi : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m2,
      ms' = MS (mkR (Z_to_bv 64 VD_SHR_RET) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp w0 w1 w2 (Z_to_bv 64 Dd) (Z_to_bv 64 0x7fff8000)
                    d0 d1 d2 d3 d4 d5 d6 d7 (shw Dd) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
               F (Z_to_bv 64 VD_SHR_RET) fc None m2 (seg_rom asegs)
      /\ munch [(V + 8, V + 16); (bv_unsigned sp - 48, bv_unsigned sp); (sh P, sh P + nsh (4 * n));
                (bv_unsigned sp - 48 - 4096, bv_unsigned sp - 48)] m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp)
      /\ rw_cells asegs m2 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))] /\ rw_cells asegs m2 Dd [C8 (wz V)]
      /\ rw_cells asegs m2 (bv_unsigned sp - 48) [C8 (wz Dd); C8 (wz 0xe8ef4); C8 s2; C8 s1; C8 s0; C8 ra]
      /\ SHAD m2 V (repeat (b8 0) 3) /\ stack0 m2 lo shi /\ SHAD m2 P (cc_gen (4 * n) 0) /\ ACONST m2.

  Lemma vd_a : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Dd V P n lo shi : Z),
    a0 = Z_to_bv 64 Dd ->
    rw_cells asegs m Dd [C8 (wz V)] -> Dd mod 8 = 0 -> bv_unsigned sp <= Dd -> Dd + 8 <= shi -> stack0 m lo shi ->
    rw_cells asegs m V [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] -> SHAD m V (repeat (b8 0) 3) -> V mod 8 = 0 ->
    aapp V 24 -> (V + 24 <= bv_unsigned sp - VD_STACK \/ bv_unsigned sp <= V) ->
    1 <= n <= 2 ^ 24 -> aapp P (4 * n) -> P mod 16 = 0 -> SHAD m P (shadow_of (4 * n)) -> (P + 4 * n <= V \/ V + 24 <= P) ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VD_STACK ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    evt asegs (vd_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dd V P n lo shi m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VDESTROY) fc None m (seg_rom asegs)).
Proof.
    intros until shi. intros Ha0 CD D8 DSP DHI S0 CV SV V8 VA VAP NB PA P16 SP PV ST CE LO SP16 SPR MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold VD_STACK, AINTRIN_STACK in LO, VAP.
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds V 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds P (4 * n) PA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1. unfold AAPP_HI in VB3, PB3.
    assert (SHE : forall x, sh x = 2147450880 + x / 8) by (intros x; reflexivity).
    assert (SHT : sh AIMG_TOP < 2 ^ 32) by reflexivity.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 Dd; Z_to_bv 64 spz; Z_to_bv 64 V; Z_to_bv 64 P; Z_to_bv 64 n; Z_to_bv 64 (P + 4 * n)]).
    assert (HR : regs_ok E vda_sr R).
    { unfold vda_sr. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZV : gz m V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (SDD : sh0 m Dd) by (eapply sh0_of_stack0; [exact S0 | lia]).
    assert (HK : know_ok asegs E m vda_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CD 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz P)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz (P + 4 * n))). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz (P + 4 * n))). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact (proj2 CV) | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
      do 10 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    assert (HSC1 : scs_denot asegs m E vda_scs).
    { unfold vda_scs. split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 VB1 VB2 VB3 SB0 DSP DHI NB.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: vd_sc. }
    destruct (@sym_exec_sound (PropExec.mkFP F fc) asegs 400 true [VD_LOOP] (SCR [false] [] []) (SS VDESTROY vda_sr [] vda_knF 40) []
                vda_ss vda_scs (SCR [] [] []) E m (seg_rom asegs) _ vda_eq HSC1
                (@st_ok_entry (PropExec.mkFP F fc) asegs E m (seg_rom asegs) VDESTROY vda_sr vda_knF 40 R HR HK)) as (ms1 & HM1 & HS1).
    destruct HS1 as (R1 & HMS1 & HR1 & HLF1 & HK1). subst ms1.
    assert (PC1 : s_pc vda_ss = VD_LOOP) by (vm_compute; reflexivity).
    rewrite PC1 in HM1.
    assert (L16 : getr R1 16%bv = Z_to_bv 64 (P + 4 * n)) by exact (HR1 16%bv).
    assert (L13 : getr R1 13%bv = Z_to_bv 64 P) by exact (HR1 13%bv).
    assert (L15 : getr R1 15%bv = Z_to_bv 64 4) by exact (HR1 15%bv).
    assert (LK : Z.of_nat (S (Z.to_nat (n - 1))) = n) by (rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia).
    destruct (vd_loop (PropExec.mkFP F fc) (Z.to_nat (n - 1)) R1 (mem_denot E m (s_log vda_ss)) (seg_rom asegs) P
                ltac:(rewrite L16, LK; reflexivity) L13 L15 ltac:(lia) ltac:(rewrite LK; lia)) as (R1' & HM1L & HE1).
    assert (HST2 : @st_ok (PropExec.mkFP F fc) asegs E m (seg_rom asegs) vdb_ss0
                     (@PropExec.mkst (PropExec.mkFP F fc) R1' (Z_to_bv 64 VD_LOOPX) (mem_denot E m (s_log vda_ss)) (seg_rom asegs))).
    { exists R1'. split; [reflexivity|]. split; [|split; [exact HLF1 | exact HK1]].
      intros r. rewrite HE1.
      exact (regs_ok_upd E (s_regs vda_ss) R1 16%bv (Z_to_bv 64 P) (EVar 35) HR1 ltac:(evs; reflexivity) r). }
    assert (HSC2 : scs_denot asegs m E vdb_scs).
    { unfold vdb_scs. split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 VB1 VB2 VB3 SB0 DSP DHI NB.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: vd_sc. }
    destruct (@sym_exec_sound (PropExec.mkFP F fc) asegs 400 true [AANNOTATE_CC] (SCR [false; false; false; false] [] []) vdb_ss0 []
                vdb_ss vdb_scs (SCR [] [] []) E m (seg_rom asegs) _ vdb_eq HSC2 HST2) as (ms2 & HM2 & HS2).
    destruct HS2 as (R' & HMS2 & HR' & Hlf & _). subst ms2.
    assert (Hms : CatSim.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 VDESTROY) m (seg_rom asegs))
                    (@PropExec.mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 (s_pc vdb_ss)) (mem_denot E m (s_log vdb_ss)) (seg_rom asegs))).
    { eapply CatSim.msteps_trans; [exact HM1|]. eapply CatSim.msteps_trans; [exact HM1L | exact HM2]. }
    clear HM1 HM1L HM2 HST2 HK1 HLF1 HR1 HE1 HSC1 HSC2 L13 L15 L16.
    unfold vdb_ss in HR', Hlf, Hms. cbn [s_pc s_regs s_log] in HR', Hlf, Hms.
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18.
    rewrite w_addm in L2 by lia. rewrite vd_nw, w_mul, w_add in L12 by lia.

    assert (WS1 : forall a, spz - 64 <= a -> a + 8 <= spz -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (WV1 : forall a, V <= a -> a + 8 <= V + 24 -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (V + (a - V + i)) by lia. apply W. cbn. lia. }
    assert (MU1 : munch [(V + 8, V + 16); (spz - 48, spz); (spz - 48 - 4096, spz - 48)] m M1).
    { subst M1. clear - Hlf VAP SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh P + nsh (4 * n) <= V \/ V + 24 <= sh P)
      by (apply (aapp_disjoint_sh V 24 P (4 * n) VA); unfold AAPP_HI; lia).
    assert (SPH : sh P + nsh (4 * n) <= AHI_LO)
      by (apply sh_nsh_high; [lia | lia | unfold AAPP_HI; lia]).
    assert (SPA : sh P + nsh (4 * n) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh V + 3 <= sh P \/ sh P + nsh (4 * n) <= sh V).
    { clear - PV V8 P16 NB. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SP' : SHAD m P (cc_gen (4 * n) (4 * n))) by (rewrite cc_gen_full; exact SP).
    assert (SB1 : SHAD M1 P (cc_gen (4 * n) (4 * n))).
    { eapply SHAD_transport; [exact SP' | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn.
      rewrite !SHE in *. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in PA, VA. unfold AHI_LO in SPH. Z.div_mod_to_equations. lia. }
    assert (SV1 : SHAD M1 V (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      rewrite !SHE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (stack0_ok_aapp V 24); [exact VA | lia | lia]|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [eapply (aconst_ok_app V 24); [exact VA | cbn; lia | cbn; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))]).
    { change [C8 (wz P); C8 (wz (P + 4 * n)); C8 (wz (P + 4 * n))] with ([C8 (wz P)] ++ [C8 (wz (P + 4 * n))] ++ [C8 (wz (P + 4 * n))]) in CV.
      apply rw_cells_app in CV as [CV0 CV']. apply rw_cells_app in CV' as [_ CV2].
      replace (V + Z.of_nat (cells_size [C8 (wz P)]) + Z.of_nat (cells_size [C8 (wz (P + 4 * n))])) with (V + 16) in CV2 by (cbn; lia).
      apply rw_cells_cons8_c.
      { eapply rw_cells_transport; [exact CV0 | exact MU1 | exact WM1 | cbn; lia]. }
      apply rw_cells_cons8_c.
      { subst M1. lgcell Hlf (WV1 (V + 8) ltac:(lia) ltac:(lia)) 3%nat. }
      replace (V + 8 + 8) with (V + 16) by lia.
      eapply rw_cells_transport; [exact CV2 | exact MU1 | exact WM1 | cbn; lia]. }
    assert (CF1 : rw_cells asegs M1 (spz - 48) [C8 (wz Dd); C8 (wz 0xe8ef4); C8 s2; C8 s1; C8 s0; C8 ra]).
    { subst M1.
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 48) ltac:(lia) ltac:(lia)) 1%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 48 + 8) ltac:(lia) ltac:(lia)) 2%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 48 + 8 + 8) ltac:(lia) ltac:(lia)) 5%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 48 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 6%nat|].
      apply rw_cells_cons8_c; [lgcell Hlf (WS1 (spz - 48 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 7%nat|].
      lgcell Hlf (WS1 (spz - 48 + 8 + 8 + 8 + 8 + 8) ltac:(lia) ltac:(lia)) 8%nat. }
    assert (CD1 : rw_cells asegs M1 Dd [C8 (wz V)])
      by (eapply rw_cells_transport; [exact CD | exact MU1 | exact WM1 | cbn; lia]).

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18.
    eapply evt_cut.
    { eapply HANN with (beg := P) (len := 4 * n) (oldmid := 4 * n) (newmid := 0) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - f_equal; lia.
      - f_equal; lia.
      - rewrite Z.add_0_r. reflexivity.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact PA.
      - unfold AAPP_HI; lia.
      - exact SB1.
      - exact (proj1 (stk_split asegs M1 lo (spz - 48) spz ST1 ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact PA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.
    rewrite (ret_pc_even 0xe9188 ltac:(lia) eq_refl).

    assert (CV2 : rw_cells asegs m2 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (CD2 : rw_cells asegs m2 Dd [C8 (wz V)])
      by (eapply rw_cells_transport; [exact CD1 | exact MU2 | exact WM2 | cbn; unfold AHI_LO in SPH; lia]).
    assert (CF2 : rw_cells asegs m2 (spz - 48) [C8 (wz Dd); C8 (wz 0xe8ef4); C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CF1 | exact MU2 | exact WM2 | cbn; unfold AHI_LO in SPH; lia]).
    assert (SV2 : SHAD m2 V (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh V + 3 <= 2 ^ 45 - 8192)
        by (rewrite !SHE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      lia. }
    assert (S02 : stack0 m2 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ST2f : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 48) spz); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 lo (spz - 48) spz ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. unfold AHI_LO in SPH. lia. }
    apply evt_done. exists w0, w1, w2, d0, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2.
    split; [reflexivity|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2]];
        intros x Hx; cbn [outside] in *; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|].
    split; [exact MI2|]. split; [exact ST2f|]. split; [exact CV2|]. split; [exact CD2|]. split; [exact CF2|].
    split; [exact SV2|]. split; [exact S02|]. split; [exact SH2 | exact AC2].
  Qed.
End VecD.
