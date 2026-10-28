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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_StateStmt LbB_ResvB.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_AN7_RA : Z := 0xec200.
Definition WO_AN8_RA : Z := 0xec20c.
Definition WO_AN9_RA : Z := 0xec218.
Definition WO_MVA2_RA : Z := 0xec224.
Definition WO_DT2_RA : Z := 0xec22c.
Definition WO_DT3_RA : Z := 0xec2b0.

Ltac wo6_seed R :=
  apply regs_ok_srs; [apply regs_ok_seed|];
  repeat (apply Forall_cons; [split; [cbn [fst]; intros X; discriminate X
                                     | cbn [fst snd]; subst R; evs; first [reflexivity | rewrite w_add by lia; reflexivity]] |]);
  apply Forall_nil.

Ltac wo6_kwr WR :=
  eapply kwr_of_wr_at;
  [ exact WR | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia
  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia ].

Ltac wo6_sc :=
  first [ apply Forall_nil
        | split_scs; cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia; lia ].

Ltac wo6_r HR' HR0 r L T :=
  let G := fresh "G" in
  rreg HR' r G;
  assert (L : T) by (rewrite G; first [ reflexivity | rewrite HR0; reflexivity
                                      | rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
                                      | apply bv_eq; vm_compute; reflexivity ]);
  clear G.

Ltac wo6_mem E m Hlf Hms M1 :=
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.

Ltac wo6_munch M1 Hlf :=
  subst M1; apply munch_mem_denot; [exact Hlf|];
  repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia;
                              cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]);
  apply Forall_nil.

Lemma wo6_u8arr_fill : forall E M log b x0 (n : nat) v,
  log_flat E log ->
  forallb (fun se => expr_eqb (a_base (e_addr se)) b) log = true ->
  0 <= bv_unsigned (edenot E b) + x0 -> bv_unsigned (edenot E b) + x0 + Z.of_nat n <= 2 ^ 64 ->
  wr_at asegs M (bv_unsigned (edenot E b) + x0) (Z.of_nat n) ->
  (forall i, (i < n)%nat -> lbyte log b (x0 + Z.of_nat i) = Some (Some v)) ->
  u8arr asegs (mem_denot E M log) (bv_unsigned (edenot E b) + x0) (repeat (Z_to_bv 8 v) n).
Proof.
  intros E M log b x0 n v Hf HB H0 H1 (W0 & W1 & W) HL.
  assert (HM : forall y, Forall (lmiss E b y) log).
  { intros y. apply Forall_forall. intros se Hse. left. rewrite forallb_forall in HB. exact (HB se Hse). }
  split.
  - split; [exact H0|]. split; [rewrite repeat_length; lia|].
    intros i Hi. rewrite repeat_length in Hi.
    pose proof (mem_denot_lbyte E M log b (x0 + Z.of_nat i) Hf (HM _) ltac:(lia)) as K.
    rewrite (HL i Hi) in K.
    unfold mrd, wa. replace (bv_unsigned (edenot E b) + x0 + Z.of_nat i) with (bv_unsigned (edenot E b) + (x0 + Z.of_nat i)) by lia.
    rewrite K. rewrite (nth_error_nth' _ (Z_to_bv 8 v)) by (rewrite repeat_length; lia).
    rewrite nth_repeat. reflexivity.
  - rewrite repeat_length. split; [exact W0|]. split; [exact W1|].
    intros i Hi. exact (wmono_mem_denot E M log _ (W i Hi)).
Qed.

Ltac wo6_fill ff M1 Hlf WS :=
  subst M1;
  lazymatch type of Hlf with log_flat ?E _ =>
    replace (sh ff + 382) with (bv_unsigned (edenot E (EVar 33)) + 382) by (evs; rewrite u64_of_Z by lia; reflexivity);
    apply (wo6_u8arr_fill E _ _ (EVar 33) 382 30 248);
    [ exact Hlf
    | vm_compute; reflexivity
    | evs; rewrite u64_of_Z by lia; lia
    | evs; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    | evs; rewrite u64_of_Z by lia; exact WS
    | intros i Hi; do 30 (destruct i as [|i]; [vm_compute; reflexivity|]); lia ]
  end.

Section WoR6.
  Context {HCEIL : HeapCeil}.

  Definition wg1b_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_AN8_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (ff + 3248)) x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_W32)) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg1b : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg1b_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_AN7_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (ff + 3248)) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_AN7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_AN7_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (ff + 3248)) x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(23%bv, EAlu ALU_ADD (EVar 32) (ELit 3248))]) R) by wo6_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN7_RA m (seg_rom asegs) HR HK 20%nat [(rv_entry RESV_W32)] (SCR [] [] []) 40%N.
    { wo6_sc. }
    clear HK.
    wo6_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo6_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = (Z_to_bv 64 WO_AN8_RA)).
    wo6_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = (Z_to_bv 64 (ff + 3248))).
    wo6_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = (Z_to_bv 64 25)).
    wo6_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = (Z_to_bv 64 (ff + 3248))).
    assert (MU1 : munch [] m M1) by wo6_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L23.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.
  Definition wg2c_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_AN9_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 3272)) x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 (rv_entry RESV_TYP)) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg2c : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg2c_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_AN8_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 3272)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_AN8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_AN8_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 3272)) x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 3272))]) R) by wo6_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN8_RA m (seg_rom asegs) HR HK 20%nat [(rv_entry RESV_TYP)] (SCR [] [] []) 40%N.
    { wo6_sc. }
    clear HK.
    wo6_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo6_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = (Z_to_bv 64 WO_AN9_RA)).
    wo6_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = (Z_to_bv 64 (ff + 3272))).
    wo6_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = (Z_to_bv 64 25)).
    wo6_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = (Z_to_bv 64 (ff + 3272))).
    assert (MU1 : munch [] m M1) by wo6_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L25.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.
  Definition wg3c_post (x2 gp tp x8 x9 x19 x20 x21 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MVA2_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3056)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wg3c : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wg3c_post x2 gp tp x8 x9 x19 x20 x21 x23 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_AN9_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_AN9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_AN9_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3056)); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 3504))]) R) by wo6_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_AN9_RA m (seg_rom asegs) HR HK 20%nat [AST_MVA] (SCR [] [] []) 40%N.
    { wo6_sc. }
    clear HK.
    wo6_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo6_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = (Z_to_bv 64 WO_MVA2_RA)).
    wo6_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = (Z_to_bv 64 (ff + 3504))).
    wo6_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = (Z_to_bv 64 (ff + 3056))).
    wo6_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = (Z_to_bv 64 (ff + 3056))).
    wo6_r HR' HR0 (22%bv : reg) L22 (getr R' 22 = (Z_to_bv 64 (ff + 3504))).
    assert (MU1 : munch [] m M1) by wo6_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L18, ?L22.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.
  Definition wd3_post (x2 gp tp x8 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_DT2_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3056)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wd3 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd3_post x2 gp tp x8 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MVA2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MVA2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MVA2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3056))]) R) by wo6_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MVA2_RA m (seg_rom asegs) HR HK 20%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { wo6_sc. }
    clear HK.
    wo6_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo6_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = (Z_to_bv 64 WO_DT2_RA)).
    wo6_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = (Z_to_bv 64 (ff + 3056))).
    wo6_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = (Z_to_bv 64 (ff + 3056))).
    assert (MU1 : munch [] m M1) by wo6_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L18.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.
  Definition wd4_post (x2 gp tp x8 x9 x20 x21 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_DT3_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3504)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-8)) (Z_to_bv 64 (sh ff)) x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 382, sh ff + 412)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
         /\ u8arr asegs m1 (sh ff + 382) (repeat (Z_to_bv 8 248) 30).
  Lemma wd4 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (sh ff + 382) 30 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wd4_post x2 gp tp x8 x9 x20 x21 x23 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_DT2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (sh ff)) x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_DT2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH WS ST MI.
    remember (mkR (Z_to_bv 64 WO_DT2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (sh ff)) x20 x21 (Z_to_bv 64 (ff + 3504)) x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 412 <= 2 ^ 45)
      by (clear - F0 FH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 (sh ff)]).
    assert (HR : regs_ok E (srs sr_id [(19%bv, EVar 33); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 3504))]) R) by wo6_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 33) 382) (ELit 30)]).
    { apply Forall_cons; [|apply Forall_nil]. wo6_kwr WS. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_DT2_RA m (seg_rom asegs) HR HK 80%nat [AST_DTOR] (SCR [] [] []) 40%N.
    { wo6_sc. }
    clear HK.
    wo6_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wo6_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = (Z_to_bv 64 WO_DT3_RA)).
    wo6_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = (Z_to_bv 64 (ff + 3504))).
    wo6_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = (Z_to_bv 64 (-8))).
    wo6_r HR' HR0 (19%bv : reg) L19 (getr R' 19 = (Z_to_bv 64 (sh ff))).
    wo6_r HR' HR0 (22%bv : reg) L22 (getr R' 22 = (Z_to_bv 64 (ff + 3504))).
    assert (MU1 : munch [(sh ff + 382, sh ff + 412)] m M1) by wo6_munch M1 Hlf.
    assert (U1 : u8arr asegs M1 (sh ff + 382) (repeat (Z_to_bv 8 248) 30)) by wo6_fill ff M1 Hlf WS.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L18, ?L19, ?L22.
    apply evt_done.
    do 14 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact U1].
  Qed.

End WoR6.
