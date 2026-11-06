(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 259 of its 346 lines of code are new or changed and 2655 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import mix_call_c.
Import ListNotations.
Open Scope Z_scope.

Lemma da_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x343e0 <= lo ->
  evt rsegs (fun ms' => exists j m',
       ms' = MS (mkR (Z_to_bv 64 0x17238) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 a0 s1
                     (Z_to_bv 64 22) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 j; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1721c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma da_run2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x17244) sp gp tp t0 t1 t2 s0 a0 a0 s0 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17238) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step. apply evt_done. reflexivity.
Qed.

Lemma da_tail : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e p h : Z) (x slack j : list byte)
    (sp1 ra0 s00 s01 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 0x343e0 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [CB 8 j; C8 s01; C8 s00; C8 ra0] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 22) ++ le4 (Z_to_bv 64 1)) ->
  bytes_at rsegs m (e + 8) (le8 (Z_to_bv 64 p)) -> 0 < e -> e mod 8 = 0 -> e + 56 <= 0x343d8 ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  1 <= p -> p + Z.of_nat (length x) + 2 <= 2 ^ 64 ->
  bytes_at rsegs m p (x ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) x -> Z.of_nat (length x) <= LMAX ->
  (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
  p + Z.of_nat (length x) + 1 + Z.of_nat (length slack) <= bv_unsigned sp1 - 96 \/ bv_unsigned sp1 <= p ->
  evt rsegs (fun ms' => exists t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 32)) gp tp t0' t1' t2' s00 s01 b0 b1 b2 b3 b4 b5 b6 b7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343d8 [C8 (Z_to_bv 64 (mixcall h 22 [x]))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17244) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e p h x slack j sp1 ra0 s00 s01 MI ST LO LO2 FR EF EA E0 E8 E56 ES Hh Hp1 Hp2 HP NZ LX AL PW.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 22 [(Z_to_bv 64 p, x)]).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - cbn. lia.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact E8.
  - intros k p0 Hk. destruct k as [|k]; [|destruct k; discriminate].
    cbn in Hk. injection Hk as <-. unfold mc_arg. cbn [fst snd].
    rewrite !unsigned_lit by lia.
    split; [replace (e + 8 + 8 * Z.of_nat 0) with (e + 8) by lia; exact EA|].
    split; [exact NZ|]. split; [exact LX|]. split; [lia|]. split; [lia|].
    exists slack. split; [exact HP|]. split; [exact AL|]. exact PW.
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia. cbn [map snd].
    do 6 step.
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import descriptors_add_c.
Local Open Scope Z_scope.

Ltac da_pres X4 X2 X1 regs1 regs2 P1 P2 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X4 eq_refl); simp_regs;
    transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
    rewrite (P2 k ltac:(unfold callee_saved; lia));
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X2 eq_refl); simp_regs;
    transitivity (getr regs1 (Z_to_bv 5 k)); [reflexivity|];
    rewrite (P1 k ltac:(unfold callee_saved; lia));
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs; reflexivity
  end.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis ARGS : arg_s_contract B API.
Hypothesis MIX : mix_call_contract.

Theorem descriptors_add_holds : descriptors_add_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC ARGS MIX.
  unfold descriptors_add_contract, descriptors_add_ret.
  intros L A regs mem md pu uri R O b PRE A0 SA GR RA F18 RES ROOM.
  rewrite SEGS in GR, RA, F18 |- *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & _).
  unfold DESCRIPTORS_ADD_K in HCEIL, HWS.
  rewrite SEGS in HWS.
  pose proof (sinv_init B API 8368 L A regs mem md R O b PRE ltac:(lia) GR RA F18 RES) as SI0.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8368) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. eapply da_run1; [exact ST | lia | lia]. }
  intros ms1 (can1 & (j & m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & XR1).
  pose proof (sinv_stack B API SEGS GOWN AX 8368 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17238) by (rewrite (getr_of_eqv _ _ 1 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 XR1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pu) by (rewrite (getr_of_eqv _ _ 8 XR1 eq_refl); simp_regs; exact A0).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 22) by (rewrite (getr_of_eqv _ _ 10 XR1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 8368 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 22).
  - exact SI1.
  - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
  - rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
    rewrite Z.mod_add by lia. exact HAL.
  - rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia.
  - rewrite SP1. lia.
  - rewrite E1_4. exact HTP.
  - exact E1_10.
  - unfold REC_FN_COUNT. lia.
  - intros L1 A1 regs1 m2 md1 O1 SI2 BLE1 PR1 R10 FK1.
    rewrite E1_1. rewrite sb_shift_refl in BLE1.
    pose proof SI2 as (RJ2 & _). pose proof RJ2 as (HM2 & _).
    destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply da_run2. }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & XR2).
    assert (E2_1 : getr R2 1 = Z_to_bv 64 0x17244) by (rewrite (getr_of_eqv _ _ 1 XR2 eq_refl); simp_regs; reflexivity).
    assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32)).
    { rewrite (getr_of_eqv _ _ 2 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2). }
    assert (E2_4 : getr R2 4 = getr regs 4).
    { rewrite (getr_of_eqv _ _ 4 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4). }
    assert (E2_9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
      by (rewrite (getr_of_eqv _ _ 9 XR2 eq_refl); simp_regs; exact R10).
    assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
      by (rewrite (getr_of_eqv _ _ 10 XR2 eq_refl); simp_regs; exact R10).
    assert (E2_11 : getr R2 11 = Z_to_bv 64 pu).
    { rewrite (getr_of_eqv _ _ 11 XR2 eq_refl); simp_regs.
      exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8). }
    assert (SP2 : spZ R2 = bv_unsigned sp - 32) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
    assert (SRC2 : arg_s_src B L1 A1 (spZ R2) m2 pu uri).
    { apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 8368 (bv_unsigned sp) L A mem md O L1 A1 m2 md1
               (rec_record R 22 []) O1 b pu uri (spZ R2) SI2 RA).
      - rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
      - rewrite SP2. lia.
      - exact SA. }
    destruct (sarg_facts B L1 A1 (spZ R2) m2 pu uri SRC2) as (NO2 & LX2).
    assert (ROOM2 : room_slots (sb_malloc (sb_shift b A A1) (Z.of_nat (length (sarg uri)) + 1))
                      (Z.of_nat (length (sarg uri)) + 1)).
    { unfold sb_mallocs, descriptors_add_sizes in ROOM. cbn [fold_left] in ROOM.
      apply (room_slots_mono _ (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) _ (LMAX + 1));
        [exact (sb_malloc_mono _ _ _ BLE1) | unfold LMAX in *; lia | exact ROOM]. }
    apply (sinv_arg_s B API SEGS ERRNO_LOW GFACT GOWN AX ARGS 8368 (bv_unsigned sp) L A mem md O L1 A1 m2 md1 R 22 O1 b
             R2 pu uri).
    + exact SI2.
    + rewrite E2_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP2. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    + rewrite SP2. lia.
    + rewrite E2_4. exact HTP.
    + exact E2_10.
    + exact E2_11.
    + exact SRC2.
    + exact ROOM2.
    + intros L2 A2 regs2 m3 md2 p SI3 EQB INI PR2 FK2.
      rewrite E2_1.
      set (x := sarg uri) in *.
      set (k := Z.of_nat (length x) + 1) in *.
      pose proof SI3 as (RJ3 & GR3 & _ & _ & _ & RA3 & F183 & _).
      pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
      rewrite SEGS in HSC3.
      destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
      assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                      [CB 8 j; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        destruct (FK1 (bv_unsigned sp - 32 + i) ltac:(rewrite SP1; lia)) as [Ea Wa].
        destruct (FK2 (bv_unsigned sp - 32 + i) ltac:(rewrite SP2; lia)) as [Eb Wb].
        split; [rewrite Eb; exact Ea | intros W; apply Wb; apply Wa; exact W]. }
      assert (HN : (length (r_calls R) <= 16)%nat)
        by exact (rec_record_calls R 22 [x] (rec_rep_calls_le _ _ _ _ _ _ _ _ GR3)).
      destruct (rec_entry_bounds R HN) as (ER1 & ER2 & ER3).
      destruct (rec_entry_at rsegs L2 A2 m3 R 22 [x] _ GR3) as (P & CA).
      set (e := rec_entry G_REC REC_SC R) in *.
      destruct CA as (_ & _ & PL & CF & CN & _ & CK).
      destruct P as [|[q kq] [|? ?]]; cbn [length] in PL; try discriminate.
      destruct (CK 0%nat x (q, kq) eq_refl eq_refl) as (CA8 & PN0 & PIN & PSZ & PB & _).
      cbn [fst snd] in CF, CN, CA8, PN0, PIN, PSZ, PB.
      cbn [length Z.of_nat] in CN.
      assert (EF : bytes_at rsegs m3 e (le4 (Z_to_bv 64 22) ++ le4 (Z_to_bv 64 1))).
      { apply bytes_at_app. rewrite length_le4. change (Z.of_nat 4) with 4.
        split; [replace e with (e + CALL_OFF_FN) at 1 by (unfold CALL_OFF_FN; lia); exact CF | exact CN]. }
      assert (EA : bytes_at rsegs m3 (e + 8) (le8 (Z_to_bv 64 q)))
        by (replace (e + 8) with (e + CALL_OFF_ARGS + 8 * Z.of_nat 0) by (unfold CALL_OFF_ARGS; lia); exact CA8).
      pose proof GR3 as (Q3 & (_ & _ & _ & _ & (_ & _ & _ & X4 & _ & _ & _ & _ & Y4 & _) & _) & _).
      rewrite r_state_record in X4, Y4.
      destruct (block_facts B _ LAWS L2 A2 m3 md2 q kq 0 HM3 PIN ltac:(lia)) as (_ & BQ1 & BQ2 & _).
      destruct (slack_rebuild m3 q x PB ltac:(lia) ltac:(unfold LMAX in *; lia)) as (slack & BP & ALp & SL7 & SLe).
      { intros a Ha. destruct (Z_lt_ge_dec a (q + kq)) as [Hlt|Hge].
        - replace a with (q + (a - q)) by ring.
          exact (proj1 (block_facts B _ LAWS L2 A2 m3 md2 q kq (a - q) HM3 PIN ltac:(lia))).
        - apply (SLACK L2 A2 m3 md2 q kq a HM3 PIN). split; [lia|]. Z.div_mod_to_equations. lia. }
      assert (SP1v : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
      assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
        by exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E2_2).
      assert (Q9 : reg_get regs2 9 = Z_to_bv 64 e)
        by exact (eq_trans (PR2 9 ltac:(unfold callee_saved; lia)) E2_9).
      eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q9.
        eapply (evt_normalize rsegs); [exact wx_apart_rsegs | exact RA3 |].
        eapply (da_tail MIX) with (lo := bv_unsigned sp - 8368) (p := q) (x := x) (slack := slack) (h := r_state R).
        - apply mem_inv_normalize.
        - rewrite SP1v. apply stk_norm; [lia | lia |]. intros a Ha. apply HSC3. left. lia.
        - rewrite SP1v. lia.
        - lia.
        - rewrite SP1v. apply rw_cells_norm_hi; [exact RA3 | lia | exact FR3].
        - exact (bytes_at_normalize rsegs m3 _ _ RA3 EF).
        - exact (bytes_at_normalize rsegs m3 _ _ RA3 EA).
        - unfold REC_SC in ER1. lia.
        - exact ER3.
        - unfold e, rec_entry. destruct (Nat.ltb_spec (length (r_calls R)) 16);
            unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC; lia.
        - apply rw_cells_norm_glob; [exact RA3 | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
          apply bytes_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
          unfold G_REC, OFF_STATE in X4. exact X4.
        - exact Y4.
        - lia.
        - unfold LMAX in *. lia.
        - exact (bytes_at_normalize rsegs m3 _ _ RA3 BP).
        - exact NO2.
        - exact LX2.
        - exact ALp.
        - left. rewrite SP1v. unfold LMAX in *. lia. }
      intros ms4 (can4 & (s4 & Q4 & REL4 & RO4) & EQ4).
      destruct Q4 as (t0' & t1' & t2' & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & m4n & -> & MU4n
        & WM4n & ES4n).
      destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
      revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
      pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
      pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
      pose proof (rw_cells_rel rsegs _ _ _ _ MR4r ES4n) as ES4.
      clear MU4n WM4n ES4n MR4r.
      rewrite SP1v in MU4.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4').
      assert (SI4 : sinv B API 8368 (bv_unsigned sp) L A mem md O L2 A2 m4 md2
                      (set_state (rec_record R 22 [x]) (mixcall (r_state R) 22 [x])) (O1 ++ [(p, k)]) b).
      { apply (sinv_state B API SEGS GOWN AX 8368 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 (rec_record R 22 [x])
                 (O1 ++ [(p, k)]) b m4 _ (mixcall (r_state R) 22 [x]) SI3 MU4 WM4).
        - intros a Ra Hm. cbn [outside] in Hm. unfold G_REC, OFF_STATE. lia.
        - apply mixcall_range. exact Y4.
        - unfold G_REC, OFF_STATE. exact (cells_c8 m4 _ _ ES4). }
      assert (RP4 : regs_preserved regs R4).
      { intros r Hr. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 8 \/ r = 9 \/ r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        clear Hr.
        destruct C as [->|[->|[->|C]]].
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X4' eq_refl); simp_regs. rewrite SP1v.
          replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned. reflexivity.
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X4' eq_refl); simp_regs. reflexivity.
        - rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X4' eq_refl); simp_regs. reflexivity.
        - repeat (destruct C as [C|C]; [subst r; da_pres X4' XR2 XR1 regs1 regs2 PR1 PR2|]).
          subst r. da_pres X4' XR2 XR1 regs1 regs2 PR1 PR2. }
      destruct (sinv_ret B API SEGS CTX 8368 L A regs mem md O L2 A2 R4 m4 md2 _ _ b PRE SI4 RP4)
        as (CPR & GR4 & ON4 & BL4 & OK4 & RA4 & F184 & RG4 & RS4).
      apply SR_ret.
      exists L2, A2, R4, m4, md2, (O1 ++ [(p, k)]).
      split; [assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA); rewrite RPC; reflexivity|].
      split; [exact CPR|].
      split.
      { unfold descriptors_add_m, rec_stub_mix, rec_mix, REC_DESCRIPTORS_ADD. cbn [fst snd].
        rewrite r_state_record. exact GR4. }
      split; [exact ON4|]. split; [exact BL4|]. split; [exact OK4|]. split; [exact RA4|]. split; [exact F184|].
      split; [exact INI|]. split; [exact RG4|].
      split; [|exact RS4].
      rewrite EQB. unfold sb_mallocs, descriptors_add_sizes. cbn [fold_left]. fold x k.
      exact (sb_malloc_mono _ _ _ BLE1).
Qed.

End P.
