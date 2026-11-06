(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupA), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-10: the head-amp table layout and the contract and walk of reac_headamp_tx_effective on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupA.v, with shent_of_block_at from lib/A/Prog/HeadampTxEffective.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySchedSetupA.v,
   ported from a working branch 7c8c67da870 (blob 43b5541d37a): image B's own slots (0x81944 .. 0x819bc and
   0x81a04 .. 0x81a1c), its registers (s3 the frame's shadow, s7 the bytes left, s4 the table reloaded from slot
   152, s5 and s8 the scene's base and width, s11 the cursor, s2 the bytes left less two), the input cursor in
   slot 48 and the shadow offset LOADED from slot 144 before each check (so the walk's shadow base is
   `sch_Bx = SOff 32 0`), the UBSan pointer-overflow guard before each input byte (`addi aX,cursor,1;
   bgeu 1,aX,0x81f48`, decided by the interval of atom 33), image B's contract of reac_headamp_tx_arm_scene
   (GrantBContracts.v tb_reac_headamp_tx_arm_scene_spec), and the walk's shadow entry lemma carried here from
   image A's lib/A/Prog/HeadampTxEffective.v (shent_of_block_at), which has no lib/B twin. *)

(* Segment A of the scheduler's setup in fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan+UBSan build (LLVMFEntrySchedSetupDefs.v): from 0x81944 (GI_sched0) to the
   return of reac_headamp_tx_arm_scene, 0x81a20 (GI_sch1a) or 0x819c0 (GI_sch1b).

   0x81948 writes 0xf8 into shadow byte 70 of the frame through s3 (`raw` unusable again).
   With L input bytes left (s7):
   - L = 0: 0x8194c jumps to 0x81a04, which reloads the table into s4 and the cursor into
     s11, and 0x81a1c calls arm_scene (t, 0, 0);
   - L = 1: 0x81950 .. 0x81978 read the scene's base into s5, 0x81980 jumps to 0x81a10,
     and 0x81a1c calls arm_scene (t, b0, 0);
   - L >= 2: 0x81950 .. 0x819a0 read the base and the width (s5, s8), s2 := L - 2,
     s11 := the cursor + 2, and 0x819bc calls arm_scene (t, b0, b1).
   The table is reloaded from slot 152 at 0x8195c (or 0x81a08), the cursor from slot 48.
   Before each read the UBSan guard `bgeu 1,cursor+1` (0x81960, 0x81988) into the trap
   0x81f48 is false, as the cursor is at least 4096; then the read checks the shadow byte
   of its address, with the shadow offset loaded from slot 144 (0x81968, 0x81990); the
   bytes lie in the caller's input block, so the error path behind the check (0x81fa0,
   0x81fd8) is not reached. A byte past the end of the input reads as 0, as
   GrantSlotPlan.sched_rd reads it (Seg_sched_setup.bat). The call itself is the caller's
   journal form of image B's contract tb_reac_headamp_tx_arm_scene_spec (sch_arm). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c HeadampSched Seg_sched_setup Seg_sched_lib SegSetModel
reac_headamp_tx_arm_scene_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* The spill slots every cut of this phase carries, in sch_common's order: the frame,
   &unset_sent, the input cursor, &ch, the frame again, &value, &param, &set_to,
   &was_set, the shadow offset and the table. *)
Definition sch_slots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms : machine_state) (t : Z) : Prop :=
  gslot cx W3 ms 8 (gF cx fp) /\ gslot cx W3 ms 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms 48 (SCH_P cx) /\
  gslot cx W3 ms 64 (gF cx fp + GO_CH) /\ gslot cx W3 ms 72 (gF cx fp) /\
  gslot cx W3 ms 96 (gF cx fp + GO_VAL) /\ gslot cx W3 ms 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms 144 SHADOW_OFF /\ gslot cx W3 ms 152 t.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ARM : tb_reac_headamp_tx_arm_scene_spec B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ (L := grant_listing) B LAWS.

(* ---- the call of reac_headamp_tx_arm_scene and the cut it lands in ---- *)
Lemma sch_arm : forall POST cx fp k acc ly3 S3 W3 (regs : bvmap 5 word) mem md t retk,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  k <= 5 -> acc <= GE_A3 MT -> gblk1 B cx ly3 S3 t -> c_n cx < 2 ^ 26 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) ->
  ((sch_L cx <= 1 /\ retk = GP_sch1a) \/
   (2 <= sch_L cx /\ retk = GP_sch1b /\ getr regs 24 = w64 (sch_b cx 1) /\
    getr regs 27 = w64 (SCH_P cx + 2) /\ getr regs 18 = w64 (sch_L cx - 2) /\
    getr regs 23 = w64 (sch_L cx))) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (sch_b cx 0) -> getr regs 12 = w64 (sch_b cx 1) ->
  getr regs 19 = w64 (gSH cx fp) -> getr regs 20 = w64 t -> getr regs 21 = w64 (sch_b cx 0) ->
  getr regs 22 = w64 (gF cx fp + GO_CH) ->
  gregs cx (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) ->
  gsaved cx W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) ->
  gshadow cx fp W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) GSH_c ->
  rdword (aview SEGS (w_H W3) mem) (gF cx fp + 1016) = Some (gFL cx fp) ->
  garr8 SEGS (mrestrict (w_H W3) mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  sch_slots cx fp W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) t ->
  gfarr cx fp W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) GO_WAS
    (GrantSlotPlan.ws_end (c_pl cx)) ->
  gfarr cx fp W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) GO_SET
    (GrantSlotPlan.st_end (c_pl cx)) ->
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx)) (GrantSlotPlan.st_end (c_pl cx)) ->
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)) ->
  gtab B cx ly3 S3 W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) t
    (GrantSlotPlan.T_end (c_pl cx)) ->
  ge_from B MT POST (GI_sch1a B MT) -> ge_from B MT POST (GI_sch1b B MT) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 regs mem md t retk HB HJ Hfrs Hmo Hk Hacc Hblk Hn26 R1 HCASE
  R10 R11 R12 R19 R20 R21 R22 Hgr Hsav Hshad Hflag Hinp Hsl Hws Hst Hrel HI1 Htab HA H1b.
pose proof Hgr as (R2 & R8 & R9 & R3 & R4). cbn [ms_regs mkst] in R2, R8, R9, R3, R4.
pose proof HJ as (HAR & _).
assert (Hrk : 0 <= retk < 2 ^ 40 /\ retk mod 2 = 0)
  by (destruct HCASE as [(_ & ->) | (_ & -> & _)]; unfold GP_sch1a, GP_sch1b; (split; [lia | reflexivity])).
assert (HinT : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
pose proof Htab as (_ & Ht0 & HTl & _).
pose proof Hsav as (H8 & Hsj).
assert (H16 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ pose proof (Hsj 0 ltac:(lia)) as X. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in X by lia.
  exact X. }
eapply (gcall B MT LAWS STK_reac_headamp_tx_arm_scene [(t + 436, t + 438); (t + 440, t + 451); (t + 456, t + 460)] _
          (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) retk POST cx fp k ly3 S3 W3 regs mem md HB HJ
          R2 R8 R3 R4 R1 (proj1 Hrk) (proj2 Hrk) H8 H16).
- unfold STK_reac_headamp_tx_arm_scene, ESTACK. lia.
- intros a (r & Hr & Ha). exists t, 460. split; [exact HinT|]. split; [exact (sch_notin_base B LAWS cx ly3 S3 W3 mem md t HAR Hblk)|].
  change (req_size 460) with 460. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
- intros HPRE. rewrite pa_sigma_reac_headamp_tx_arm_scene.
  exact (ARM ly3 S3 W3 regs mem md (gch cx) t (sch_b cx 0) (sch_b cx 1) (GrantSlotPlan.T_end (c_pl cx)) HPRE R10 R11 R12
           (sbat_range _ _) (sbat_range _ _) HinT HTl (gtab_obj B cx ly3 S3 W3 _ t _ Htab)).
- intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & HO & _).
  pose proof (sch_keep_call B MT LAWS cx fp W3 (mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS))
                ly3 S3 md k t STK_reac_headamp_tx_arm_scene [(t + 436, t + 438); (t + 440, t + 451); (t + 456, t + 460)]
                mem md mem2 md2 0 HB HJ Hfrs Hblk HAR
                ltac:(intros a (r & Hr & Ha); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia)
                HJc) as HK.
  set (ms2 := mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)).
  set (ms1 := mkst regs (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) mem (seg_rom SEGS)) in *.
  assert (PR : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP.
  assert (Hcom : sch_common B MT cx fp retk GSH_c k acc ly3 S3 W3 ms2 t).
  { unfold sch_common.
    split.
    { unfold ge_body. unfold ms2; cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      split; [reflexivity|]. do 5 (split; [reflexivity|]).
      split; [unfold gregs; cbn [ms_regs mkst];
              split; [exact (eq_trans (PR 2 ltac:(unfold acallee_saved; lia)) R2)|];
              split; [exact (eq_trans (PR 8 ltac:(unfold acallee_saved; lia)) R8)|];
              split; [exact (eq_trans (PR 9 ltac:(unfold acallee_saved; lia)) R9)|];
              split; [exact (eq_trans (PR 3 ltac:(unfold acallee_saved; lia)) R3)|];
              exact (eq_trans (PR 4 ltac:(unfold acallee_saved; lia)) R4)|].
      split; [exact (ge_gsaved_keep B MT cx fp W3 HB [] ms1 ms2 HK Hsav)|].
      split; [exact (ge_gshadow_keep cx fp W3 [] ms1 ms2 GSH_c HK ltac:(vm_compute; discriminate) Hshad)|].
      split; [exact (ge_flag_keep cx fp W3 [] ms1 ms2 HK Hflag)|].
      split; [vm_compute; reflexivity|].
      exact (ge_input_keep cx fp W3 [] ms1 ms2 HK Hinp). }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hblk|]. split; [exact Hn26|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 19 ltac:(unfold acallee_saved; lia)) R19)|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 22 ltac:(unfold acallee_saved; lia)) R22)|].
    destruct Hsl as (L8 & L40 & L48 & L64 & L72 & L96 & L112 & L128 & L136 & L144 & L152).
    do 11 (split; [eapply (ge_gslot_keep B MT cx fp W3 HB [] ms1 ms2 _ _ HK); [lia | lia | eassumption]|]).
    split; [exact (ge_gfarr_keep cx fp W3 [] ms1 ms2 GO_WAS _ HK ltac:(unfold GO_WAS; lia)
                     ltac:(destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & HL & _); rewrite HL; vm_compute; discriminate) Hws)|].
    split; [exact (ge_gfarr_keep cx fp W3 [] ms1 ms2 GO_SET _ HK ltac:(unfold GO_SET; lia)
                     ltac:(destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & _ & HL & _); rewrite HL; vm_compute; discriminate) Hst)|].
    split; [exact Hrel | exact HI1]. }
  assert (Htab2 : gtab B cx ly3 S3 W3 ms2 t (sch_T1 cx)).
  { apply (obj_gtab B cx ly3 S3 W3 ms2 t (sch_T1 cx) HinT Ht0 (sch_T1_len cx HTl)). exact HO. }
  assert (X20 : getr (ms_regs ms2) 20 = w64 t)
    by (unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 20 ltac:(unfold acallee_saved; lia)) R20)).
  assert (X21 : getr (ms_regs ms2) 21 = w64 (sch_b cx 0))
    by (unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 21 ltac:(unfold acallee_saved; lia)) R21)).
  destruct HCASE as [(HL & ->) | (HL & -> & R24 & R27 & R18 & R23)].
  + apply (HA cx fp k acc ly3 S3 W3 ms2 md2 HB HJ2 Hfrs Hmo).
    exists t. split; [exact Hcom|]. split; [exact HL|].
    split; [exact X20|]. split; [exact X21|].
    exact Htab2.
  + apply (H1b cx fp k acc ly3 S3 W3 ms2 md2 HB HJ2 Hfrs Hmo).
    exists t. split; [exact Hcom|]. split; [exact HL|].
    split; [exact X20|]. split; [exact X21|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 24 ltac:(unfold acallee_saved; lia)) R24)|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 27 ltac:(unfold acallee_saved; lia)) R27)|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 18 ltac:(unfold acallee_saved; lia)) R18)|].
    split; [unfold ms2; cbn [ms_regs mkst]; exact (eq_trans (PR 23 ltac:(unfold acallee_saved; lia)) R23)|].
    exact Htab2.
Qed.

(* ---- the memory at the call, from the memory at 0x81944 ---- *)
Lemma rdword_keepA : forall H (m m' : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof. intros H m m' a v K Hr. rewrite (rdword_tr (aview SEGS H m) (aview SEGS H m') a K). exact Hr. Qed.

Lemma garr8_keepA : forall H (m m' : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l K Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (K (Z.of_nat j) ltac:(lia))). exact Hv0.
Qed.

Lemma GSH_c_raw : forall i, (i < 104)%nat -> i <> 70%nat -> nth i GSH_c 0 = nth i GSH_raw 0.
Proof.
intros i Hi H70.
assert (HA : forallb (fun n => (n =? 70)%nat || (nth n GSH_c 0 =? nth n GSH_raw 0)) (seq 0 104) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in HA. specialize (HA i ltac:(apply in_seq; lia)).
rewrite (proj2 (Nat.eqb_neq i 70) H70) in HA. cbn [orb] in HA. apply Z.eqb_eq. exact HA.
Qed.

Lemma sch_mem_tr : forall cx fp k ly3 S3 W3 (ms3 ms1 : machine_state) md3 t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
     aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  aview SEGS (w_H W3) (ms_mem ms1) (gSH cx fp + 70) = Some 248 ->
  ge_body cx fp GP_sched0 W3 ms3 GSH_raw ->
  sch_slots cx fp W3 ms3 t ->
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) ->
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) ->
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) ->
  gsaved cx W3 ms1 /\ gshadow cx fp W3 ms1 GSH_c /\
  rdword (aview SEGS (w_H W3) (ms_mem ms1)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  sch_slots cx fp W3 ms1 t /\
  gfarr cx fp W3 ms1 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms1 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  gtab B cx ly3 S3 W3 ms1 t (GrantSlotPlan.T_end (c_pl cx)).
Proof.
intros cx fp k ly3 S3 W3 ms3 ms1 md3 t HB HJ Hfrs Hblk KA H70 Hbody Hsl Hws Hst Htab.
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfrs Hblk) as GL.
destruct GL as (Hsp0ac & Hsp016 & Hsp047 & Hsp1r & Hsp1m & EFa & HF4096 & HFce & HF64 & HFzone & HSHeq
                & Ht4096 & Htce & Htzone & HtF & Hpn).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (HSB : SHADOW_OFF <= gSH cx fp + 70 < SHADOW_OFF + 2 ^ 44) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
(* a byte away from the shadow of the frame is kept *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= a) ->
               aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha Hz; apply KA; [exact Ha | lia]).
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
pose proof Hbody as (_ & _ & _ & _ & _ & _ & _ & Hsav & Hshad & Hflag & _ & Hinp).
assert (KS : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha; apply KB; lia).
assert (KF : forall a, gF cx fp <= a < gF cx fp + 1024 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a Ha; apply KB; lia).
assert (SLOT : forall off v, 0 <= off <= 184 -> gslot cx W3 ms3 off v -> gslot cx W3 ms1 off v).
{ intros off v Ho Hv. unfold gslot in *. apply (rdword_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1) _ _); [|exact Hv].
  intros i Hi. apply KS. lia. }
split.
{ destruct Hsav as (Hra & Hsj). split.
  - apply (rdword_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1) _ _); [|exact Hra]. intros i Hi. apply KS. lia.
  - intros j Hj. apply (rdword_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1) _ _); [|exact (Hsj j Hj)].
    intros i Hi. apply KS. lia. }
split.
{ intros i Hi. destruct (Nat.eq_dec i 70) as [-> | Hne].
  - change (Z.of_nat 70) with 70. rewrite H70. vm_compute. reflexivity.
  - change (length GSH_c) with 104%nat in Hi. rewrite (GSH_c_raw i Hi Hne).
    rewrite KA by (rewrite HSHeq; lia). apply Hshad. change (length GSH_raw) with 104%nat. exact Hi. }
split.
{ apply (rdword_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1) _ _); [|exact Hflag]. intros i Hi. apply KF. lia. }
split.
{ apply (garr8_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1)); [|exact Hinp].
  intros i Hi. rewrite length_map in Hi.
  destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn].
  - destruct (Hpn Hn) as (Hp0 & Hpc & Hpz & _). apply KB; unfold c_n in *; lia.
  - unfold c_n in Hn. lia. }
split.
{ destruct Hsl as (L8 & L40 & L48 & L64 & L72 & L96 & L112 & L128 & L136 & L144 & L152).
  repeat split; apply SLOT; try lia; assumption. }
assert (HWl : length (GrantSlotPlan.ws_end (c_pl cx)) = 144%nat /\ length (GrantSlotPlan.st_end (c_pl cx)) = 144%nat)
  by (destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & HL1 & HL2 & _); split; assumption).
split.
{ unfold gfarr in *. apply (garr8_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1)); [|exact Hws].
  intros i Hi. rewrite length_map, (proj1 HWl) in Hi. apply KF. unfold GO_WAS. lia. }
split.
{ unfold gfarr in *. apply (garr8_keepA (w_H W3) (ms_mem ms3) (ms_mem ms1)); [|exact Hst].
  intros i Hi. rewrite length_map, (proj2 HWl) in Hi. apply KF. unfold GO_SET. lia. }
destruct Htab as (Hin & Ht0 & HTl & Hb). split; [exact Hin|]. split; [exact Ht0|]. split; [exact HTl|].
intros i Hi H1 H2 H3. rewrite (KB (t + i)) by lia. exact (Hb i Hi H1 H2 H3).
Qed.

(* ---- the frame's shadow byte the block writes is the frame's own ---- *)
Lemma sch_awr_sh : forall cx fp ly3 E (rs : smem) STK sp0 bl0 blc,
  ge_E cx fp E -> frame_addr ly3 GE_CID fp = gF cx fp ->
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 -> 0 <= gSH cx fp -> gSH cx fp + 128 <= 2 ^ 64 ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
     (YP09.r_base r = Some 529%nat /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 128)) ->
  awr_ok E rs STK sp0 [] bl0 blc ly3 [(GE_CID, fp)].
Proof.
intros cx fp ly3 E rs STK sp0 bl0 blc HE Hfa HSH Hs0 Hs1 Hro a (r & Hin & Ha).
destruct (Hro r Hin) as [Hw | (Hb & Hlo & Hhi)]; [lia|].
rewrite Hb in Ha. cbn [YP09.base_val] in Ha.
pose proof HE as (_ & _ & _ & _ & _ & E529). unfold GA_FSH, w64 in E529. rewrite E529 in Ha.
rewrite unsigned_lit_small in Ha by lia.
right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
rewrite Hfa, Hfb. change (1024 / 8) with 128. unfold shadow_addr. rewrite HSH in Ha. lia.
Qed.

(* ---- the shadow of the input bytes the block reads ---- *)
(* The walk's shadow entry once the bytes lie in a block: image A's
   lib/A/Prog/HeadampTxEffective.v shent_of_block_at, stated for this walk's shadow base
   sch_Bx (the shadow offset, atom 32, which image B loads from slot 144). *)
Lemma sch_shent_of_block : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex sch_Bx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS sch_Bx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HBx Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

Lemma sch_shok : forall cx fp ly3 S3 W3 mem md E (m : nat),
  AR SEGS B ly3 S3 W3 mem md -> ge_E cx fp E -> ew E 33 = Z_to_bv 64 (SCH_P cx) ->
  (m <> 0%nat -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  c_p cx <= SCH_P cx -> SCH_P cx + Z.of_nat m <= c_p cx + c_n cx -> 0 <= SCH_P cx < 2 ^ 64 ->
  sh_ok SEGS sch_Bx (sch_SH m) E (mrestrict (w_H W3) mem).
Proof.
intros cx fp ly3 S3 W3 mem md E m HAR HE E33 HPin Hp0 Hp1 Hp2.
destruct m as [|m']; cbn [sch_SH]; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
specialize (HPin ltac:(discriminate)).
assert (Hn : 0 <= c_n cx) by (unfold c_n; lia).
pose proof (req_size_pos (c_n cx) Hn) as [_ Hrq].
pose proof HE as (_ & E32 & _). unfold GA_SB, w64 in E32.
apply (sch_shent_of_block ly3 S3 W3 mem md E 33 (SCH_P cx) (c_p cx) (c_n cx) 0 (Z.of_nat (S m')) HAR HPin).
- unfold sch_Bx, U. rewrite ge_sv_SOff0, E32. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
- unfold U. rewrite ge_sv_SOff0, E33. apply unsigned_lit_small. unfold SCH_P in *. lia.
- lia.
- lia.
- lia.
Qed.

(* ---- what the two runs of the block leave in memory ---- *)
Lemma sch_wr70 : forall cx fp E rs,
  ge_E cx fp E -> 0 <= gSH cx fp -> gSH cx fp + 128 <= 2 ^ 64 ->
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/
     (YP09.r_base r = Some 529%nat /\ YP09.r_wlo r = 70 /\ YP09.r_whi r = 71)) ->
  forall a, YP09.in_wrange E rs a -> a = gSH cx fp + 70.
Proof.
intros cx fp E rs HE Hs0 Hs1 Hro a (r & Hin & Ha).
destruct (Hro r Hin) as [Hw | (Hb & Hl & Hh)]; [lia|].
rewrite Hb, Hl, Hh in Ha. cbn [YP09.base_val] in Ha.
pose proof HE as (_ & _ & _ & _ & _ & E529). unfold GA_FSH, w64 in E529. rewrite E529 in Ha.
rewrite unsigned_lit_small in Ha by lia. lia.
Qed.

Lemma sch_awr_ro : forall E (rs : smem) STK sp0 FP bl0 blc ly own,
  (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own Hro a (r & Hin & Ha). pose proof (Hro r Hin). lia. Qed.

Lemma sch_wr_none : forall E rs, (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) ->
  forall a, YP09.in_wrange E rs a -> False.
Proof. intros E rs Hro a (r & Hin & Ha). pose proof (Hro r Hin). lia. Qed.

Lemma sch_byte_of_region : forall E m n lo hi wlo whi cs od e,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  In (YP09.mkChunk od (CVal 1 e)) cs ->
  YP09.mbyte SEGS m (bv_unsigned (ew E n) + od) = Some (YP09.byte_of_word (sv_denot E e) 0).
Proof.
intros E m n lo hi wlo whi cs od e (_ & _ & _ & Hcs) Hin.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base YP09.base_val] in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm.
injection Hb as <-. rewrite Z.add_0_r in Hm. exact Hm.
Qed.

Ltac sch_ro_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [first [left; cbn; lia | right; cbn; repeat split; lia] |]); destruct Hr.
Ltac sch_ro_only :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [ss_mem In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn; lia |]); destruct Hr.

(* The scene's bytes past the end of the input read as 0. *)
Lemma sch_b_out : forall cx j, sch_L cx <= Z.of_nat j -> sch_b cx j = 0.
Proof.
intros cx j H. unfold sch_b, sbat. apply Seg_sched_setup.bat_out. unfold sch_L, c_n in H. lia.
Qed.

(* ---- the walk from 0x81944 to the call of reac_headamp_tx_arm_scene ----
   With m (0, 1 or 2) bytes left to read and the bytes left (s7, atom 553) in [lo, hi],
   it seats the cut, runs the shadow store of 0x81948, makes the frame's shadow
   read-only, runs the reads (each behind its UBSan guard and its shadow check) up to the
   call, and leaves the registers at the call (Q1 .. Q27), the memory facts of the cut
   at the call (Hsav' .. Htab') and the goal at the callee's entry. *)

(* ---- 0x81944 .. 0x819bc: two or more bytes left ---- *)
Lemma sch_case2 : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  ge_from B MT POST (GI_sch1a B MT) -> ge_from B MT POST (GI_sch1b B MT) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_sched0 B MT cx fp k acc ly3 S3 W3 ms3 md3 -> 2 <= sch_L cx ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI HL.
destruct HI as (t & Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & R23 & S8 & S40 & S48 & S64 & S72
                & S96 & S112 & S128 & S136 & S144 & S152 & Htab & Hws & Hst & Hrel & HI1).
assert (Hsl : sch_slots cx fp W3 ms3 t) by (unfold sch_slots; repeat split; assumption).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _).
pose proof Hgr as (G2 & G8 & G9 & G3 & G4).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfrs Hblk) as GL.
destruct GL as (Hsp0ac & Hsp016 & Hsp047 & Hsp1r & Hsp1m & EFa & HF4096 & HFce & HF64 & HFzone & HSHeq
                & Ht4096 & Htce & Htzone & HtF & Hpn).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof HJ as HJ0.
pose proof (sch_seat B MT LAWS TL TLF cx fp k ly3 S3 W3 ms3 md3 2%nat t HB HJ Hfrs Hbody Hblk R19 R22
              S40 S48 S96 S112 S136 S144 S152 ltac:(lia) ltac:(unfold sch_L in *; lia)) as HS.
remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef.
assert (HE : ge_E cx fp E) by (subst E; exact (sch_env_E B MT cx fp t (ms_regs ms3) HB)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by (subst E; apply sch_env_33).
assert (E42 : ew E 42 = Z_to_bv 64 t) by (subst E; apply sch_env_42).
assert (EB : forall j, (j < 8)%nat -> ew E (34 + j) = Z_to_bv 64 (sbat (c_pl cx) j)) by (subst E; apply sch_env_b).
assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat ->
                 ew E (530 + Z.to_nat (bv_unsigned r)) = getr (ms_regs ms3) r) by (subst E; apply sch_env_reg).
assert (E553 : ew E 553 = w64 (sch_L cx)).
{ pose proof (EREG 23%bv ltac:(vm_compute; discriminate)) as X.
  change (530 + Z.to_nat (bv_unsigned 23%bv))%nat with 553%nat in X. rewrite X. exact R23. }
assert (F553 : afact_ok E 553 (mkAF 2 (2 ^ 26) 0)).
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E553.
  unfold w64, sch_L in *; rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia. }
clear HEdef.
pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH, w64 in E32, E60, E516, E528, E529.
apply (st_ok_pi_add_fact E _ _ 553 _ HS) in F553.
clear HS.
rename F553 into HS.
unfold sch_ss0 in HS.
cbn [sch_ex] in HS.
norm_ss HS.
(* 0x81944 .. 0x81948: `raw` unusable again *)
paj_run_to_sh RUNTOP HS HJ 0xf10.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ => rename msX into msa end.
assert (H70 : aview SEGS (w_H W3) (ms_mem msa) (gSH cx fp + 70) = Some 248).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    let RSH := fresh "RSH" in let Hm := fresh "Hm" in
    pose proof (st_ok_pi_region_nth E ssx _ 3%nat r HS ltac:(vm_compute; reflexivity)) as RSH;
    pose proof (sch_byte_of_region E _ _ _ _ _ _ _ 70 (SLit 18446744073709551608) RSH
                  ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as Hm;
    rewrite E529, unsigned_lit_small in Hm by lia; cbn [ms_mem restrict] in Hm;
    unfold aview; rewrite Hm; cbn; reflexivity end. }
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
                aview SEGS (w_H W3) (ms_mem msa) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msa)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
    intros a Ha Hne; eapply (frame_wins _ _ _ _ _ (fun x => x = gSH cx fp + 70) HFx); [|exact Ha|exact Hne];
    apply (sch_wr70 cx fp E _ HE Hs0 Hs1); sch_ro_list end. }
fs_roF HS.
assert (SHOK : sh_ok SEGS sch_Bx (sch_SH 2%nat) E (mrestrict (w_H W3) (ms_mem msa))).
{ let Hn := fresh "Hn" in
  destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn];
  [ let Hp0 := fresh "Hp0" in let Hpc := fresh "Hpc" in
    destruct (Hpn Hn) as (Hp0 & Hpc & _);
    apply (sch_shok cx fp ly3 S3 W3 (ms_mem msa) _ E 2%nat (proj1 HJ) HE E33);
    [ intros _; unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left;
      let Hpn0 := fresh "Hpn0" in
      pose proof HB as (_ & _ & _ & Hpn0 & _);
      let Hn0 := fresh "Hn0" in let Hin0 := fresh "Hin0" in
      destruct Hpn0 as [(Hn0 & _) | (_ & Hin0)]; [lia | exact Hin0]
    | unfold SCH_P; lia
    | unfold SCH_P, sch_L in *; lia
    | unfold SCH_P; let C1 := fresh "C1" in pose proof asan_consts as (C1 & _); unfold sch_L, c_n in *; lia ]
  | first [ cbn [sch_SH]; apply Forall_nil | exfalso; unfold sch_L, c_n in *; lia ] ]. }
cbn [sch_SH] in SHOK.
(* 0x8194c .. the call: the guards, the bytes and the arguments *)
paj_run_tok RUN HS HJ SHOK sch_span.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename msX into msc end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 ->
                aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem msa) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msc)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; eapply (frame_wins _ _ _ _ _ (fun _ => False) HFx); [|exact Ha|exact (fun x => x)];
    apply (sch_wr_none _ _); sch_ro_only end. }
prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24.
prreg HS (27%bv : bv 5) Q27.
let HE0 := fresh "HE0" in
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & _).
pose proof (EB 0%nat ltac:(lia)) as EB0.
pose proof (EB 1%nat ltac:(lia)) as EB1.
cbn [Nat.add] in EB0, EB1.
assert (X10 : getr (ms_regs msc) 10 = w64 t) by (rewrite Q10, E42; reflexivity).
assert (X20 : getr (ms_regs msc) 20 = w64 t) by (rewrite Q20, E42; reflexivity).
assert (X19 : getr (ms_regs msc) 19 = w64 (gSH cx fp)) by (rewrite Q19, E529; reflexivity).
assert (X22 : getr (ms_regs msc) 22 = w64 (gF cx fp + GO_CH)).
{ rewrite Q22, E516. unfold w64, GO_CH. rewrite unsigned_lit_small by lia. reflexivity. }
assert (XG : gregs cx (mkst (ms_regs msc) (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) (ms_mem msc) (seg_rom SEGS))).
{ unfold gregs; cbn [ms_regs mkst];
  split; [rewrite Q2, E60; reflexivity|];
  split; [rewrite Q8, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl); unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|];
  split; [rewrite Q9, E60; reflexivity|];
  split; [rewrite Q3, (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)|];
  rewrite Q4, (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl). }
(* the memory at the call *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
               aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
      intros a Ha Hne; rewrite (KA2 a Ha); exact (KA1 a Ha Hne)).
assert (H70c : aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + 70) = Some 248)
  by (rewrite (KA2 (gSH cx fp + 70)) by lia; exact H70).
destruct (sch_mem_tr cx fp k ly3 S3 W3 ms3 msc md3 t HB HJ0 Hfrs Hblk KA H70c Hbody Hsl Hws Hst Htab)
  as (Hsav' & Hshad' & Hflag' & Hinp' & Hsl' & Hws' & Hst' & Htab').
pmkst HS.
assert (HP : 0 <= SCH_P cx /\ SCH_P cx + 2 < 2 ^ 64).
{ destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|unfold sch_L in HL; lia].
  destruct (Hpn Hn) as (Hp0 & Hpc & _). pose proof asan_consts as (C1 & _). unfold SCH_P, sch_L, c_n in *. lia. }
assert (X11 : getr (ms_regs msc) 11 = w64 (sch_b cx 0)) by (rewrite Q11, EB0; reflexivity).
assert (X12 : getr (ms_regs msc) 12 = w64 (sch_b cx 1)) by (rewrite Q12, EB1; reflexivity).
assert (X21 : getr (ms_regs msc) 21 = w64 (sch_b cx 0)) by (rewrite Q21, EB0; reflexivity).
assert (X24 : getr (ms_regs msc) 24 = w64 (sch_b cx 1)) by (rewrite Q24, EB1; reflexivity).
assert (X27 : getr (ms_regs msc) 27 = w64 (SCH_P cx + 2)) by (rewrite Q27, E33, unsigned_lit_small by lia; reflexivity).
assert (X23 : getr (ms_regs msc) 23 = w64 (sch_L cx)) by (rewrite Q23; exact E553).
assert (X18 : getr (ms_regs msc) 18 = w64 (sch_L cx - 2)).
{ rewrite Q18, E553. unfold w64, sch_L in *. rewrite unsigned_lit_small by lia. f_equal; lia. }
(* 0x819bc: reac_headamp_tx_arm_scene (t, b0, b1) *)
exact (sch_arm POST cx fp k acc ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ t GP_sch1b HB HJ Hfrs Hmo Hk Hacc Hblk Hn26
  Q1 (or_intror (conj HL (conj eq_refl (conj X24 (conj X27 (conj X18 X23)))))) X10 X11 X12 X19 X20 X21 X22 XG
  Hsav' Hshad' Hflag' Hinp' Hsl' Hws' Hst' Hrel HI1 Htab' H1a H1b).
Qed.

(* ---- 0x81944 .. 0x81a1c: one byte left ---- *)
Lemma sch_case1 : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  ge_from B MT POST (GI_sch1a B MT) -> ge_from B MT POST (GI_sch1b B MT) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_sched0 B MT cx fp k acc ly3 S3 W3 ms3 md3 -> sch_L cx = 1 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI HL.
destruct HI as (t & Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & R23 & S8 & S40 & S48 & S64 & S72
                & S96 & S112 & S128 & S136 & S144 & S152 & Htab & Hws & Hst & Hrel & HI1).
assert (Hsl : sch_slots cx fp W3 ms3 t) by (unfold sch_slots; repeat split; assumption).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _).
pose proof Hgr as (G2 & G8 & G9 & G3 & G4).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfrs Hblk) as GL.
destruct GL as (Hsp0ac & Hsp016 & Hsp047 & Hsp1r & Hsp1m & EFa & HF4096 & HFce & HF64 & HFzone & HSHeq
                & Ht4096 & Htce & Htzone & HtF & Hpn).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof HJ as HJ0.
pose proof (sch_seat B MT LAWS TL TLF cx fp k ly3 S3 W3 ms3 md3 1%nat t HB HJ Hfrs Hbody Hblk R19 R22
              S40 S48 S96 S112 S136 S144 S152 ltac:(lia) ltac:(unfold sch_L in *; lia)) as HS.
remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef.
assert (HE : ge_E cx fp E) by (subst E; exact (sch_env_E B MT cx fp t (ms_regs ms3) HB)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by (subst E; apply sch_env_33).
assert (E42 : ew E 42 = Z_to_bv 64 t) by (subst E; apply sch_env_42).
assert (EB : forall j, (j < 8)%nat -> ew E (34 + j) = Z_to_bv 64 (sbat (c_pl cx) j)) by (subst E; apply sch_env_b).
assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat ->
                 ew E (530 + Z.to_nat (bv_unsigned r)) = getr (ms_regs ms3) r) by (subst E; apply sch_env_reg).
assert (E553 : ew E 553 = w64 (sch_L cx)).
{ pose proof (EREG 23%bv ltac:(vm_compute; discriminate)) as X.
  change (530 + Z.to_nat (bv_unsigned 23%bv))%nat with 553%nat in X. rewrite X. exact R23. }
assert (F553 : afact_ok E 553 (mkAF 1 1 0)).
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E553.
  unfold w64, sch_L in *; rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia. }
clear HEdef.
pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH, w64 in E32, E60, E516, E528, E529.
apply (st_ok_pi_add_fact E _ _ 553 _ HS) in F553.
clear HS.
rename F553 into HS.
unfold sch_ss0 in HS.
cbn [sch_ex] in HS.
norm_ss HS.
(* 0x81944 .. 0x81948: `raw` unusable again *)
paj_run_to_sh RUNTOP HS HJ 0xf10.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ => rename msX into msa end.
assert (H70 : aview SEGS (w_H W3) (ms_mem msa) (gSH cx fp + 70) = Some 248).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    let RSH := fresh "RSH" in let Hm := fresh "Hm" in
    pose proof (st_ok_pi_region_nth E ssx _ 3%nat r HS ltac:(vm_compute; reflexivity)) as RSH;
    pose proof (sch_byte_of_region E _ _ _ _ _ _ _ 70 (SLit 18446744073709551608) RSH
                  ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as Hm;
    rewrite E529, unsigned_lit_small in Hm by lia; cbn [ms_mem restrict] in Hm;
    unfold aview; rewrite Hm; cbn; reflexivity end. }
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
                aview SEGS (w_H W3) (ms_mem msa) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msa)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
    intros a Ha Hne; eapply (frame_wins _ _ _ _ _ (fun x => x = gSH cx fp + 70) HFx); [|exact Ha|exact Hne];
    apply (sch_wr70 cx fp E _ HE Hs0 Hs1); sch_ro_list end. }
fs_roF HS.
assert (SHOK : sh_ok SEGS sch_Bx (sch_SH 1%nat) E (mrestrict (w_H W3) (ms_mem msa))).
{ let Hn := fresh "Hn" in
  destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn];
  [ let Hp0 := fresh "Hp0" in let Hpc := fresh "Hpc" in
    destruct (Hpn Hn) as (Hp0 & Hpc & _);
    apply (sch_shok cx fp ly3 S3 W3 (ms_mem msa) _ E 1%nat (proj1 HJ) HE E33);
    [ intros _; unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left;
      let Hpn0 := fresh "Hpn0" in
      pose proof HB as (_ & _ & _ & Hpn0 & _);
      let Hn0 := fresh "Hn0" in let Hin0 := fresh "Hin0" in
      destruct Hpn0 as [(Hn0 & _) | (_ & Hin0)]; [lia | exact Hin0]
    | unfold SCH_P; lia
    | unfold SCH_P, sch_L in *; lia
    | unfold SCH_P; let C1 := fresh "C1" in pose proof asan_consts as (C1 & _); unfold sch_L, c_n in *; lia ]
  | first [ cbn [sch_SH]; apply Forall_nil | exfalso; unfold sch_L, c_n in *; lia ] ]. }
cbn [sch_SH] in SHOK.
(* 0x8194c .. 0x81980: the guard, the base and the arguments *)
paj_run_tok RUN HS HJ SHOK sch_span.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ => rename msX into msb end.
assert (KA2a : forall a, 0 <= a < 2 ^ 64 ->
                aview SEGS (w_H W3) (ms_mem msb) a = aview SEGS (w_H W3) (ms_mem msa) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msb)) |- _ =>
    intros a Ha; eapply (frame_wins _ _ _ _ _ (fun _ => False) HFx); [|exact Ha|exact (fun x => x)];
    apply (sch_wr_none _ _); sch_ro_only end. }
(* 0x81980: one byte left, so the call with width 0 *)
psrr_branch_tok RUN BR HS SHOK sch_span.
2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc.
     rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite E553 in Hc.
     unfold w64 in Hc. rewrite HL in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK sch_span.
{ apply sch_awr_ro. sch_ro_only. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename msX into msc end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 ->
                aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem msa) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem msb)) (mrestrict _ (ms_mem msc)) |- _ =>
    intros a Ha; rewrite <- (KA2a a Ha);
    eapply (frame_wins _ _ _ _ _ (fun _ => False) HFx); [|exact Ha|exact (fun x => x)];
    apply (sch_wr_none _ _); sch_ro_only end. }
prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22.
let HE0 := fresh "HE0" in
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & _).
pose proof (EB 0%nat ltac:(lia)) as EB0.
cbn [Nat.add] in EB0.
assert (X10 : getr (ms_regs msc) 10 = w64 t) by (rewrite Q10, E42; reflexivity).
assert (X20 : getr (ms_regs msc) 20 = w64 t) by (rewrite Q20, E42; reflexivity).
assert (X19 : getr (ms_regs msc) 19 = w64 (gSH cx fp)) by (rewrite Q19, E529; reflexivity).
assert (X22 : getr (ms_regs msc) 22 = w64 (gF cx fp + GO_CH)).
{ rewrite Q22, E516. unfold w64, GO_CH. rewrite unsigned_lit_small by lia. reflexivity. }
assert (XG : gregs cx (mkst (ms_regs msc) (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) (ms_mem msc) (seg_rom SEGS))).
{ unfold gregs; cbn [ms_regs mkst];
  split; [rewrite Q2, E60; reflexivity|];
  split; [rewrite Q8, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl); unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|];
  split; [rewrite Q9, E60; reflexivity|];
  split; [rewrite Q3, (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)|];
  rewrite Q4, (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl). }
(* the memory at the call *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
               aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
      intros a Ha Hne; rewrite (KA2 a Ha); exact (KA1 a Ha Hne)).
assert (H70c : aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + 70) = Some 248)
  by (rewrite (KA2 (gSH cx fp + 70)) by lia; exact H70).
destruct (sch_mem_tr cx fp k ly3 S3 W3 ms3 msc md3 t HB HJ0 Hfrs Hblk KA H70c Hbody Hsl Hws Hst Htab)
  as (Hsav' & Hshad' & Hflag' & Hinp' & Hsl' & Hws' & Hst' & Htab').
pmkst HS.
assert (X11 : getr (ms_regs msc) 11 = w64 (sch_b cx 0)) by (rewrite Q11, EB0; reflexivity).
assert (X12 : getr (ms_regs msc) 12 = w64 (sch_b cx 1)) by (rewrite Q12, (sch_b_out cx 1) by lia; reflexivity).
assert (X21 : getr (ms_regs msc) 21 = w64 (sch_b cx 0)) by (rewrite Q21, EB0; reflexivity).
assert (HL1 : sch_L cx <= 1) by lia.
(* 0x81a1c: reac_headamp_tx_arm_scene (t, b0, 0) *)
exact (sch_arm POST cx fp k acc ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ t GP_sch1a HB HJ Hfrs Hmo Hk Hacc Hblk Hn26
  Q1 (or_introl (conj HL1 eq_refl)) X10 X11 X12 X19 X20 X21 X22 XG
  Hsav' Hshad' Hflag' Hinp' Hsl' Hws' Hst' Hrel HI1 Htab' H1a H1b).
Qed.

(* ---- 0x81944 .. 0x81a1c: no byte left ---- *)
Lemma sch_case0 : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3,
  ge_from B MT POST (GI_sch1a B MT) -> ge_from B MT POST (GI_sch1b B MT) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  GI_sched0 B MT cx fp k acc ly3 S3 W3 ms3 md3 -> sch_L cx = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI HL.
destruct HI as (t & Hbody & Hk & Hacc & Hblk & Hn26 & R19 & R22 & R23 & S8 & S40 & S48 & S64 & S72
                & S96 & S112 & S128 & S136 & S144 & S152 & Htab & Hws & Hst & Hrel & HI1).
assert (Hsl : sch_slots cx fp W3 ms3 t) by (unfold sch_slots; repeat split; assumption).
pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _).
pose proof Hgr as (G2 & G8 & G9 & G3 & G4).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfrs Hblk) as GL.
destruct GL as (Hsp0ac & Hsp016 & Hsp047 & Hsp1r & Hsp1m & EFa & HF4096 & HFce & HF64 & HFzone & HSHeq
                & Ht4096 & Htce & Htzone & HtF & Hpn).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof HJ as HJ0.
pose proof (sch_seat B MT LAWS TL TLF cx fp k ly3 S3 W3 ms3 md3 0%nat t HB HJ Hfrs Hbody Hblk R19 R22
              S40 S48 S96 S112 S136 S144 S152 ltac:(lia) ltac:(unfold sch_L in *; lia)) as HS.
remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef.
assert (HE : ge_E cx fp E) by (subst E; exact (sch_env_E B MT cx fp t (ms_regs ms3) HB)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by (subst E; apply sch_env_33).
assert (E42 : ew E 42 = Z_to_bv 64 t) by (subst E; apply sch_env_42).
assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat ->
                 ew E (530 + Z.to_nat (bv_unsigned r)) = getr (ms_regs ms3) r) by (subst E; apply sch_env_reg).
assert (E553 : ew E 553 = w64 (sch_L cx)).
{ pose proof (EREG 23%bv ltac:(vm_compute; discriminate)) as X.
  change (530 + Z.to_nat (bv_unsigned 23%bv))%nat with 553%nat in X. rewrite X. exact R23. }
assert (F553 : afact_ok E 553 (mkAF 0 0 0)).
{ unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E553.
  unfold w64, sch_L in *; rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia. }
clear HEdef.
pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH, w64 in E32, E60, E516, E528, E529.
apply (st_ok_pi_add_fact E _ _ 553 _ HS) in F553.
clear HS.
rename F553 into HS.
unfold sch_ss0 in HS.
cbn [sch_ex] in HS.
norm_ss HS.
(* 0x81944 .. 0x81948: `raw` unusable again *)
paj_run_to_sh RUNTOP HS HJ 0xf10.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msX) |- _ => rename msX into msa end.
assert (H70 : aview SEGS (w_H W3) (ms_mem msa) (gSH cx fp + 70) = Some 248).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    let RSH := fresh "RSH" in let Hm := fresh "Hm" in
    pose proof (st_ok_pi_region_nth E ssx _ 3%nat r HS ltac:(vm_compute; reflexivity)) as RSH;
    pose proof (sch_byte_of_region E _ _ _ _ _ _ _ 70 (SLit 18446744073709551608) RSH
                  ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as Hm;
    rewrite E529, unsigned_lit_small in Hm by lia; cbn [ms_mem restrict] in Hm;
    unfold aview; rewrite Hm; cbn; reflexivity end. }
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
                aview SEGS (w_H W3) (ms_mem msa) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msa)) |- _ =>
    let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
    intros a Ha Hne; eapply (frame_wins _ _ _ _ _ (fun x => x = gSH cx fp + 70) HFx); [|exact Ha|exact Hne];
    apply (sch_wr70 cx fp E _ HE Hs0 Hs1); sch_ro_list end. }
fs_roF HS.
assert (SHOK : sh_ok SEGS sch_Bx (sch_SH 0%nat) E (mrestrict (w_H W3) (ms_mem msa)))
  by (cbn [sch_SH]; apply Forall_nil).
cbn [sch_SH] in SHOK.
(* 0x8194c: no byte left, so the call with base and width 0 *)
psrr_branch_tok RUN BR HS SHOK sch_span.
2: { exfalso. cbn [sv_denot ew ewset Nat.eqb] in Hc.
     rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite E553 in Hc.
     unfold w64 in Hc. rewrite HL in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* 0x81a04 .. the call: the table and the cursor reloaded, the arguments *)
paj_run_tok RUN HS HJ SHOK sch_span.
{ apply (sch_awr_sh cx fp ly3 E); try assumption; sch_ro_list. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- _ => rename msX into msc end.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 ->
                aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem msa) a).
{ lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msc)) |- _ =>
    intros a Ha; eapply (frame_wins _ _ _ _ _ (fun _ => False) HFx); [|exact Ha|exact (fun x => x)];
    apply (sch_wr_none _ _); sch_ro_only end. }
prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22.
let HE0 := fresh "HE0" in
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE0 & _).
assert (X10 : getr (ms_regs msc) 10 = w64 t) by (rewrite Q10, E42; reflexivity).
assert (X20 : getr (ms_regs msc) 20 = w64 t) by (rewrite Q20, E42; reflexivity).
assert (X19 : getr (ms_regs msc) 19 = w64 (gSH cx fp)) by (rewrite Q19, E529; reflexivity).
assert (X22 : getr (ms_regs msc) 22 = w64 (gF cx fp + GO_CH)).
{ rewrite Q22, E516. unfold w64, GO_CH. rewrite unsigned_lit_small by lia. reflexivity. }
assert (XG : gregs cx (mkst (ms_regs msc) (Z_to_bv 64 (SIGMA GS_reac_headamp_tx_arm_scene)) (ms_mem msc) (seg_rom SEGS))).
{ unfold gregs; cbn [ms_regs mkst];
  split; [rewrite Q2, E60; reflexivity|];
  split; [rewrite Q8, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl); unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|];
  split; [rewrite Q9, E60; reflexivity|];
  split; [rewrite Q3, (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)|];
  rewrite Q4, (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl). }
(* the memory at the call *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
               aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
      intros a Ha Hne; rewrite (KA2 a Ha); exact (KA1 a Ha Hne)).
assert (H70c : aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + 70) = Some 248)
  by (rewrite (KA2 (gSH cx fp + 70)) by lia; exact H70).
destruct (sch_mem_tr cx fp k ly3 S3 W3 ms3 msc md3 t HB HJ0 Hfrs Hblk KA H70c Hbody Hsl Hws Hst Htab)
  as (Hsav' & Hshad' & Hflag' & Hinp' & Hsl' & Hws' & Hst' & Htab').
pmkst HS.
assert (X11 : getr (ms_regs msc) 11 = w64 (sch_b cx 0)) by (rewrite Q11, (sch_b_out cx 0) by lia; reflexivity).
assert (X12 : getr (ms_regs msc) 12 = w64 (sch_b cx 1)) by (rewrite Q12, (sch_b_out cx 1) by lia; reflexivity).
assert (X21 : getr (ms_regs msc) 21 = w64 (sch_b cx 0)) by (rewrite Q21, (sch_b_out cx 0) by lia; reflexivity).
assert (HL1 : sch_L cx <= 1) by lia.
(* 0x81a1c: reac_headamp_tx_arm_scene (t, 0, 0) *)
exact (sch_arm POST cx fp k acc ly3 S3 W3 (ms_regs msc) (ms_mem msc) _ t GP_sch1a HB HJ Hfrs Hmo Hk Hacc Hblk Hn26
  Q1 (or_introl (conj HL1 eq_refl)) X10 X11 X12 X19 X20 X21 X22 XG
  Hsav' Hshad' Hflag' Hinp' Hsl' Hws' Hst' Hrel HI1 Htab' H1a H1b).
Qed.

(* ---- segment A: 0x81944 to the return of reac_headamp_tx_arm_scene ---- *)
Theorem sch_segA : forall POST, sch_segA_stmt B MT POST.
Proof.
intros POST H1a H1b cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HI.
pose proof (Seg_sched_setup.pos_raw_le (c_pl cx)) as Hpr.
assert (HL0 : 0 <= sch_L cx) by (unfold sch_L, c_n; lia).
destruct (Z_lt_le_dec (sch_L cx) 2) as [HL|HL].
- destruct (Z.eq_dec (sch_L cx) 0) as [H0|H0].
  + exact (sch_case0 POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI H0).
  + exact (sch_case1 POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI ltac:(lia)).
- exact (sch_case2 POST cx fp k acc ly3 S3 W3 ms3 md3 H1a H1b HB HJ Hfrs Hmo HI HL).
Qed.

End c.
End b.
End a.
