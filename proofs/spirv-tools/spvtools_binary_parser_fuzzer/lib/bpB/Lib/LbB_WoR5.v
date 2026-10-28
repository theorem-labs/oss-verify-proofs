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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_WoR4.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_StateStmt LbB_ResvB.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS7_RA : Z := 0xeb400.
Definition WO_MS8_RA : Z := 0xeb414.
Definition WO_MS9_RA : Z := 0xeb428.
Definition WO_MS10_RA : Z := 0xeb448.
Definition WO_ON4_RA : Z := 0xeb454.
Definition WO_ON5_RA : Z := 0xeb460.
Definition WO_ON6_RA : Z := 0xeb46c.
Definition WO_MVA1_RA : Z := 0xeb478.
Definition WO_DT1_RA : Z := 0xeb480.

Ltac wo5_seed R :=
  apply regs_ok_srs; [apply regs_ok_seed|];
  repeat (apply Forall_cons; [split; [cbn [fst]; intros X; discriminate X
                                     | cbn [fst snd]; subst R; evs; first [reflexivity | rewrite w_add by lia; reflexivity]] |]);
  apply Forall_nil.

Ltac wo5_kwr WR :=
  eapply kwr_of_wr_at;
  [ exact WR | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia
  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia ].

Ltac wo5_sc :=
  first [ apply Forall_nil
        | split_scs; cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia; lia ].

Ltac wo5_r HR' HR0 r L T :=
  let G := fresh "G" in
  rreg HR' r G;
  assert (L : T) by (rewrite G; first [ reflexivity | rewrite HR0; reflexivity
                                      | rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia] ]);
  clear G.

Ltac wo5_mem E m Hlf Hms M1 :=
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.

Ltac wo5_munch M1 Hlf :=
  subst M1; apply munch_mem_denot; [exact Hlf|];
  repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia;
                              cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]);
  apply Forall_nil.

Ltac wo5_dj := cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia; lia.

Ltac wo5_lgc Hlf k :=
  eapply (rw_cells_log_nth _ _ _ k);
  [ exact Hlf | reflexivity
  | cbn [firstn]; repeat (apply Forall_cons; [wo5_dj |]); apply Forall_nil
  | wo5_dj | | reflexivity | exact I | try (first [ reflexivity | evs; reflexivity ]) ].

Lemma wo5_wr_sub : forall m A N, wr_at asegs m A N -> forall a n, A <= a -> a + n <= A + N -> wr_at asegs m a n.
Proof.
  intros m A N (W0 & W1 & W) a n X1 X2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply W. lia.
Qed.


Section WoR5.
  Context {HCEIL : HeapCeil}.

  Definition wt1_post (x2 gp tp x8 x9 x18 x19 x20 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS7_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2800)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (ff + 2800)) x22 x23 x24 x25 x26 x27
                    x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wt1 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt1_post x2 gp tp x8 x9 x18 x19 x20 x22 x23 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS6_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 (ff + 2800)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MS6_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 (ff + 2800)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(21%bv, EAlu ALU_ADD (EVar 32) (ELit 2800))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS6_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS7_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2800)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wo5_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wo5_r HR' HR0 (21%bv : reg) L21 (getr R' 21 = Z_to_bv 64 (ff + 2800)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L21.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wt2_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS8_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2840)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 2832, ff + 2836)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 2832) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wt2 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29
                      x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 2752) 240 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt2_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS7_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS7_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(23%bv, ELit 0x3f800000); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 2752))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 2832) (ELit 4)]).
    { apply Forall_cons; [wo5_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS7_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS8_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2840)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wo5_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wo5_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    wo5_r HR' HR0 (27%bv : reg) L27 (getr R' 27 = Z_to_bv 64 (ff + 2752)).
    assert (MU1 : munch [(ff + 2832, ff + 2836)] m M1) by wo5_munch M1 Hlf.
    assert (CC2832 : rw_cells asegs M1 (ff + 2832) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. wo5_lgc Hlf 0%nat; first [apply (wo5_wr_sub m (ff + 2752) 240 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L23, ?L27.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC2832.
  Qed.

  Definition wt3_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS9_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2880)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 2872, ff + 2876)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 2872) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wt3 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29
                      x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 2752) 240 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt3_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS8_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS8_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(23%bv, ELit 0x3f800000); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 2752))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 2872) (ELit 4)]).
    { apply Forall_cons; [wo5_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS8_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS9_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2880)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wo5_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wo5_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    wo5_r HR' HR0 (27%bv : reg) L27 (getr R' 27 = Z_to_bv 64 (ff + 2752)).
    assert (MU1 : munch [(ff + 2872, ff + 2876)] m M1) by wo5_munch M1 Hlf.
    assert (CC2872 : rw_cells asegs M1 (ff + 2872) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. wo5_lgc Hlf 0%nat; first [apply (wo5_wr_sub m (ff + 2752) 240 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L23, ?L27.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC2872.
  Qed.

  Definition wt4_post (x2 gp tp x8 x9 x18 x19 x20 x22 x26 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS10_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 0)
                    (Z_to_bv 64 72) x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (ff + 2920)) x22
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) x26
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 2912, ff + 2916)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 2912) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wt4 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29
                      x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 2752) 240 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt4_post x2 gp tp x8 x9 x18 x19 x20 x22 x26 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS9_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS9_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               (Z_to_bv 64 0x3f800000) x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(23%bv, ELit 0x3f800000); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 2752))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 2912) (ELit 4)]).
    { apply Forall_cons; [wo5_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS9_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS10_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2920)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wo5_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 72).
    wo5_r HR' HR0 (21%bv : reg) L21 (getr R' 21 = Z_to_bv 64 (ff + 2920)).
    wo5_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    wo5_r HR' HR0 (24%bv : reg) L24 (getr R' 24 = Z_to_bv 64 (ff + 2944)).
    wo5_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = Z_to_bv 64 (ff + 2968)).
    wo5_r HR' HR0 (27%bv : reg) L27 (getr R' 27 = Z_to_bv 64 (ff + 2752)).
    assert (MU1 : munch [(ff + 2912, ff + 2916)] m M1) by wo5_munch M1 Hlf.
    assert (CC2912 : rw_cells asegs M1 (ff + 2912) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. wo5_lgc Hlf 0%nat; first [apply (wo5_wr_sub m (ff + 2752) 240 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L21, ?L23, ?L24, ?L25, ?L27.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC2912.
  Qed.

  Definition wt5_post (x2 gp tp x8 x9 x18 x19 x20 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 25) x12 x13
                    x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (ff + 2920)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 RESV_OPND_ENTRY) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wt5 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wt5_post x2 gp tp x8 x9 x18 x19 x20 x22 x23 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS10_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 (ff + 2920)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS10_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MS10_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               (Z_to_bv 64 (ff + 2920)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(21%bv, EAlu ALU_ADD (EVar 32) (ELit 2920))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS10_RA m (seg_rom asegs) HR HK 20%nat [RESV_OPND_ENTRY] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_ON4_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2920)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 25).
    wo5_r HR' HR0 (21%bv : reg) L21 (getr R' 21 = Z_to_bv 64 (ff + 2920)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L21.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wf1b_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_ON5_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 25) x12 x13
                    x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 (ff + 2944)) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_W32)) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf1b : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf1b_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_ON4_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               (Z_to_bv 64 (ff + 2944)) x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_ON4_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_ON4_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               (Z_to_bv 64 (ff + 2944)) x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(24%bv, EAlu ALU_ADD (EVar 32) (ELit 2944))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON4_RA m (seg_rom asegs) HR HK 20%nat [(rv_entry RESV_W32)] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_ON5_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2944)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 25).
    wo5_r HR' HR0 (24%bv : reg) L24 (getr R' 24 = Z_to_bv 64 (ff + 2944)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L24.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wf2c_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_ON6_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 25) x12 x13
                    x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 2968)) x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_TYP)) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf2c : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf2c_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_ON5_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 2968)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_ON5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_ON5_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 2968)) x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 2968))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON5_RA m (seg_rom asegs) HR HK 20%nat [(rv_entry RESV_TYP)] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_ON6_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2968)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 25).
    wo5_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = Z_to_bv 64 (ff + 2968)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L25.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wf3c_post (x2 gp tp x8 x9 x18 x19 x20 x21 x23 x24 x25 x26 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MVA1_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 2752))
                    x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wf3c : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x28 x29
                      x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wf3c_post x2 gp tp x8 x9 x18 x19 x20 x21 x23 x24 x25 x26 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_ON6_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
          F (Z_to_bv 64 WO_ON6_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_ON6_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(22%bv, EAlu ALU_ADD (EVar 32) (ELit 3504)); (27%bv, EAlu ALU_ADD (EVar 32) (ELit 2752))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_ON6_RA m (seg_rom asegs) HR HK 20%nat [AST_MVA] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MVA1_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3504)).
    wo5_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 (ff + 2752)).
    wo5_r HR' HR0 (22%bv : reg) L22 (getr R' 22 = Z_to_bv 64 (ff + 3504)).
    wo5_r HR' HR0 (27%bv : reg) L27 (getr R' 27 = Z_to_bv 64 (ff + 2752)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L22, ?L27.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wd1_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_DT1_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 2752)) x11 x12 x13 x14 x15 x16
                    x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd1 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd1_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MVA1_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MVA1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MVA1_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 x25 x26 (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(27%bv, EAlu ALU_ADD (EVar 32) (ELit 2752))]) R) by wo5_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MVA1_RA m (seg_rom asegs) HR HK 20%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { wo5_sc. }
    clear HK.
    wo5_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo5_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_DT1_RA).
    wo5_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 2752)).
    wo5_r HR' HR0 (27%bv : reg) L27 (getr R' 27 = Z_to_bv 64 (ff + 2752)).
    assert (MU1 : munch [] m M1) by wo5_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L27.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

End WoR5.
