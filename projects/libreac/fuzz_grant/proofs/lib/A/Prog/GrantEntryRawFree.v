(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawFree), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE3f.v. *)
(* The last slot of the hand-built allocation phase of LLVMFuzzerTestOneInput on the ASan
   build: 0x813b4 (GR_free), `jal 52b4c <wrapper_free>` with a0 = s, the 4352-byte sweep
   buffer the phase allocated, and the return address BASE + 0xd08 (GP_sched0, one of the
   three sites in GE_FSITES).

   The step is one instruction. It is run concretely: the slot of the listing is a PCall
   of the wrapper for free, so the machine step is `step_jal_link` (ra := BASE + 0xd08,
   pc := the wrapper's first slot). Then afree04_rule gives back the block list without
   (s, 4352), the journal with one more event, and `acall_kept`, which keeps every byte
   outside [sp1 - ASTACK, sp1) and outside the freed block: that is what carries rcore and
   the table (rm_rcore, rm_gtab of GrantEntryRawLib.v) to the cut GI_sched0 at 0x813b8. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegSetModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryRawDefs GrantEntryRawLib GrantEntrySeat GrantEntrySetDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Two registers of a 5-bit map are different when their numbers are. *)
Ltac bvne := let H := fresh "Hbv" in intros H; apply (f_equal bv_unsigned) in H;
             vm_compute in H; discriminate.

(* `l1 ++ x :: l2` is `L ++ [x]` only when l1 is L and l2 is empty, for an x that L lacks. *)
Lemma gr_split_last : forall (L l1 l2 : list (Z * Z)) (x : Z * Z),
  L ++ [x] = l1 ++ x :: l2 -> ~ In x L -> l1 = L /\ l2 = [].
Proof.
  induction L as [|a L IH]; intros l1 l2 x E Hni.
  - destruct l1 as [|b l1]; cbn [app] in E.
    + split; [reflexivity|]. destruct l2 as [|c l2]; [reflexivity | discriminate E].
    + exfalso. destruct l1 as [|c l1]; cbn [app] in E; discriminate E.
  - destruct l1 as [|b l1]; cbn [app] in E.
    + injection E as Ea E2. exfalso. apply Hni. left. exact Ea.
    + injection E as Hab E2. subst b.
      destruct (IH l1 l2 x E2 ltac:(intros Hq; apply Hni; right; exact Hq)) as (-> & ->).
      split; reflexivity.
Qed.

Section rg.
Context {fx : YK11.FPState}.
(* A register other than ra is what it was before the call wrote ra. *)
Lemma gr_reg_other : forall (regs : bvmap 5 word) (v : word) (r : bv 5),
  r <> (1%bv : bv 5) -> getr (regupd regs (1%bv : bv 5) v) r = getr regs r.
Proof.
  intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
  apply regupd_other. exact Hr.
Qed.
Lemma gr_reg_ra : forall (regs : bvmap 5 word) (v : word),
  getr (regupd regs (1%bv : bv 5) v) (1%bv : bv 5) = v.
Proof.
  intros regs v. unfold getr.
  replace (bv_eqb (1%bv : bv 5) 0) with false by (vm_compute; reflexivity).
  apply regupd_same.
Qed.
End rg.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.

(* 0x813b4 -> 0x813b8: free (s). *)
Theorem seg_raw_free : forall POST,
  ge_from B MT POST (GI_sched0 B MT) -> ge_from B MT POST (GR_freeI B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMLE HINV.
(* ---- what the cut gives ---- *)
destruct HINV as (t & s & HRC & Hk & Hacc & Hbl2 & HTAB & Hs4096 & R18 & R10).
pose proof HRC as HRCd.
destruct HRCd as (HBODY & Hn26 & R20 & R21 & R22 & R24 & R25 & SL88 & SLATE & GB0 & GB1 & GWS & GST & HHrel & HI1).
destruct HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HSHD & HFLW & Hlensh & HINP).
destruct HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct HSAVED as (Hra_sv & Hsv).
pose proof HB as (HPRE & Hp10 & Hp11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & Usp & E32c & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra1 & Hra4 & Hgp & Htp & Hstk & HpresW & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ as (HAR3 & Hly3 & Hsecs3 & Hwle3 & Hio3 & Hfrs3 & Hnev3 & Hk0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (PB0 & PB1 & PB4).
pose proof (pa_base_lo (L := grant_listing)) as PBLO.
unfold gblk2 in Hbl2.
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (ERQS : req_size RAW_SW = RAW_SW) by reflexivity.
assert (ERQT : req_size 460 = 460) by reflexivity.
assert (ESW : RAW_SW = 4352) by reflexivity.
rewrite ESW in Hacc.
rewrite FFS in Hslo.
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp).
{ unfold gF, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (FB : fs_frame_bytes GE_CID = 1024) by reflexivity.
assert (EG : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 Hfin)
  as (HF4096 & HFceil & HFapp).
rewrite EFA in HF4096, HFceil, HFapp. rewrite FB in HFceil, HFapp.
assert (Hsp1 : spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288).
{ rewrite Esp1. pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)). lia. }
assert (Hsp132 : c_sp1 cx mod 32 = 0) by (rewrite Esp1, Z.mul_comm; apply Z_mod_mult).
assert (Hsp1lo : alloc_ceiling <= c_sp1 cx) by lia.
(* ---- the freed block and what it is apart from ---- *)
assert (Hins : In (s, RAW_SW) (ablocks B ly3 S3))
  by (rewrite Hbl2; apply in_or_app; right; right; left; reflexivity).
assert (Hint : In (t, 460) (ablocks B ly3 S3))
  by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 s RAW_SW HAR3 Hins)
  as (Hs16 & _ & Hsceil & Hsapp & _).
rewrite ERQS in Hsceil, Hsapp.
assert (Dts : t + 460 <= s \/ s + RAW_SW <= t).
{ pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (t, 460) (s, RAW_SW)
    (ablocks B (c_ly cx) (c_S cx)) [] [] HAR3 ltac:(rewrite Hbl2; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite ERQS, ERQT in D. lia. }
assert (Dps : c_n cx = 0 \/ c_p cx + c_n cx <= s \/ s + RAW_SW <= c_p cx).
{ destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [left; exact Hn0 | right].
  apply in_split in Hin0. destruct Hin0 as (m1 & m2 & Em).
  assert (Heq : ablocks B ly3 S3 = m1 ++ (c_p cx, c_n cx) :: (m2 ++ [(t, 460)]) ++ (s, RAW_SW) :: []).
  { rewrite Hbl2, Em, <- !app_assoc. reflexivity. }
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx, c_n cx) (s, RAW_SW)
    m1 (m2 ++ [(t, 460)]) [] HAR3 Heq) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite ERQS in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq). lia. }
assert (DFs : gF cx fp + 1024 <= s \/ s + RAW_SW <= gF cx fp).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 s RAW_SW GE_CID fp
    HAR3 Hins Hfin) as D.
  rewrite EFA, FB, ERQS in D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
assert (DSHs : gSH cx fp + 128 <= s \/ s + RAW_SW <= gSH cx fp).
{ destruct (shadow_addr_bounds (gF cx fp) ltac:(lia)) as (Hb1 & _).
  destruct (shadow_addr_bounds (gF cx fp + 1024) ltac:(lia)) as (_ & Hb2).
  pose proof (Hb2 ltac:(lia)) as Hb2'. unfold shadow_addr in Hb1, Hb2'.
  assert (HD8 : (gF cx fp + 1024) / 8 = gF cx fp / 8 + 128).
  { replace (gF cx fp + 1024) with (gF cx fp + 128 * 8) by lia. apply Z.div_add. lia. }
  rewrite HD8 in Hb2'. rewrite EG.
  destruct Hsapp as (_ & [Hlo | (Hhi & _)]).
  - right. unfold kLowShadowBeg in Hlo. unfold SHADOW_OFF in Hb1 |- *. lia.
  - left. lia. }
assert (Dsps : s + RAW_SW <= c_sp1 cx) by lia.
assert (Hnotin : ~ In (s, RAW_SW) (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)])).
{ intros Hin. apply in_split in Hin. destruct Hin as (m1 & m2 & Em).
  assert (Heq : ablocks B ly3 S3 = m1 ++ (s, RAW_SW) :: m2 ++ (s, RAW_SW) :: []).
  { rewrite Hbl2.
    replace (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460); (s, RAW_SW)])
      with ((ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]) ++ [(s, RAW_SW)])
      by (rewrite <- app_assoc; reflexivity).
    rewrite Em, <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (s, RAW_SW) (s, RAW_SW)
    m1 m2 [] HAR3 Heq) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite ERQS in D. lia. }
(* ---- the registers the jal leaves ---- *)
assert (RUPD : forall r : bv 5, r <> (1%bv : bv 5) ->
  getr (regupd (ms_regs ms3) (1%bv : bv 5) (Z_to_bv 64 (BASE + GP_sched0))) r = getr (ms_regs ms3) r)
  by (intros r Hr; apply gr_reg_other; exact Hr).
assert (RSAME : getr (regupd (ms_regs ms3) (1%bv : bv 5) (Z_to_bv 64 (BASE + GP_sched0))) (1%bv : bv 5)
  = Z_to_bv 64 (BASE + GP_sched0)) by apply gr_reg_ra.
assert (RSP1 : spZ (regupd (ms_regs ms3) (1%bv : bv 5) (Z_to_bv 64 (BASE + GP_sched0))) = c_sp1 cx).
{ unfold spZ. rewrite (RUPD (2%bv : Prelude.reg) ltac:(bvne)), Rsp. unfold w64.
  apply unsigned_lit_small. lia. }
(* ---- the step of the jal at 0x813b4 ---- *)
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GR_free)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
assert (Hslot : plookup (pl_tpi (L := grant_listing)) GR_free
  = Some (PCall GS___interceptor_trampoline_free (1%bv : Prelude.reg))) by (vm_compute; reflexivity).
rewrite <- (pl_tpi_eq (L := grant_listing)) in Hslot.
pose proof (cert_slot gsym (clookup pa_tbl) VAL SIGMA grant_listing pa_cert _ _ Hslot) as HCK.
destruct HCK as (Hck & _ & _).
cbv beta iota zeta delta [pi_slot_check] in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + GR_free)) as [wz|] eqn:Hfw; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck. destruct Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck. destruct Hck as (Hck1 & Ht).
apply andb_prop in Hck1. destruct Hck1 as (Hrd & _).
apply reg_eqb_eq in Hrd. apply Z.eqb_eq in Ht. rewrite <- Hrd in Hdec.
assert (HSTEP : RiscvSemantics.step SEGS (restrict (w_H W3) ms3) =
  MachineOk (mkst (regupd (ms_regs ms3) (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + GP_sched0)))
                  (Z_to_bv 64 (pc_wrap_free (as_code B)))
                  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
{ rewrite Ems3 at 1. rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS (ms_regs ms3) (Z_to_bv 64 (BASE + GR_free))
    (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS) (Z_to_bv 32 wz) (1%bv : Prelude.reg) _
    (pa_fetch_ok _ _ Hfw) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  destruct (bv_eqb (1%bv : Prelude.reg) 0) eqn:Hx0; [vm_compute in Hx0; discriminate|].
  f_equal. f_equal.
  - f_equal. unfold v_addi. rewrite unsigned_lit_small by (unfold GR_free; lia).
    f_equal. unfold GR_free, GP_sched0. lia.
  - unfold btgt, v_addi. rewrite unsigned_lit_small by (unfold GR_free; lia).
    rewrite <- (pal_free B TL), <- Ht. symmetry. apply lit_canon. }
eapply (SRr_step SEGS pa_wx W3 ms3 _ md3); [exact Hsvc | exact HSTEP |].
intros model' Hsame.
rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb md3 model' Hsame).
(* ---- the call of the wrapper for free ---- *)
eapply SRr_bind.
{ eapply (AFREE4 W3 (regupd (ms_regs ms3) (1%bv : Prelude.reg) (Z_to_bv 64 (BASE + GP_sched0)))
    (ms_mem ms3) GE_STK (spZ (c_regs cx)) (@nil (Z * Z))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3
    (with_vm_backing (m_vm_lazy md3) (m_vm_materialized model') md3) k s RAW_SW
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + GP_sched0)) (gch cx)
    ltac:(apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ) Hins).
  - rewrite (RUPD (10%bv : Prelude.reg) ltac:(bvne)). exact R10.
  - rewrite RSP1. lia.
  - apply mod_sub16; [exact Hsp132 | exact Hal16].
  - lia.
  - rewrite Has, FFS. lia.
  - rewrite (RUPD (3%bv : Prelude.reg) ltac:(bvne)), Rgp. exact Hgp.
  - rewrite (RUPD (4%bv : Prelude.reg) ltac:(bvne)), Rtp. exact Htp.
  - exact RSAME.
  - apply ret_ok_codeptr_v; [unfold GP_sched0; lia | reflexivity].
  - unfold GE_EV in Hev. lia.
  - assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
    { eapply g_chain; [exact HB | exact HJ | exact Hra_sv |].
      replace (spZ (c_regs cx) - 16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia.
      exact (Hsv 0 ltac:(lia)). }
    apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms3)) (c_sp1 cx) (spZ (c_regs cx))
      (gch cx) _ HCH).
    + rewrite RSP1. lia.
    + unfold s0Z. rewrite (RUPD (8%bv : Prelude.reg) ltac:(bvne)), Rs0. unfold w64.
      apply unsigned_lit_small. lia.
    + unfold raZ. rewrite RSAME, unsigned_lit_small by (unfold GP_sched0; lia).
      unfold GP_sched0. lia.
  - apply HTR. right. split; [reflexivity|].
    unfold raZ. rewrite RSAME, unsigned_lit_small by (unfold GP_sched0; lia).
    replace (BASE + GP_sched0 - BASE) with GP_sched0 by lia.
    unfold GE_FSITES, GP_sched0. cbn [In]. right. left. reflexivity.
  - intros Hcon i Hi. exfalso. apply Hnotin. apply in_or_app. left. exact Hcon.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMLE).
    + apply (mo_free_nonneg MT MTL).
    + unfold GE_NEED, GE_A3 in HNEED. pose proof (mo_free_nonneg MT MTL). lia. }
cbv beta. intros W2 c2 Hwle Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsplit & Hfrs2 & HK2 & MLE2).
(* ---- the blocks after the free: the table is all that is left ---- *)
destruct Hsplit as (l1 & l2 & Eb3 & Eb2).
assert (Egb1 : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]).
{ assert (E1 : (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]) ++ [(s, RAW_SW)] = l1 ++ (s, RAW_SW) :: l2).
  { rewrite <- app_assoc. cbn [app]. rewrite <- Hbl2. exact Eb3. }
  destruct (gr_split_last _ _ _ _ E1 Hnotin) as (-> & ->).
  rewrite Eb2, app_nil_r. reflexivity. }
(* ---- the bytes the call kept ---- *)
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK2 by lia.
destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KEEP : forall a : Z,
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/
  gF cx fp <= a < gF cx fp + 1024 \/ gSH cx fp <= a < gSH cx fp + 128 \/
  t <= a < t + 460 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; lia.
  - destruct Hpn as [(Hn0 & _) | (Hnpos & Hin0)]; [exfalso; unfold c_n in *; lia|].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (rewrite Hbl2; apply in_or_app; left; exact Hin0).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq).
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hin3); [lia|]. rewrite ERQS. lia.
  - apply (K4 GE_CID fp a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, FB. lia.
    + rewrite ERQS. lia.
  - apply (K4 GE_CID fp a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite EFA, FB.
      change (1024 / 8) with 128. unfold shadow_addr. rewrite <- EG. lia.
    + rewrite ERQS. lia.
  - replace a with (t + (a - t)) by lia.
    apply (K2 t 460 (a - t) Hint); [rewrite ERQT; lia|]. rewrite ERQS. lia. }
(* ---- the registers the call kept ---- *)
assert (QP : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r Hr). apply gr_reg_other.
  intros Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite Z_to_bv_unsigned in Hq. unfold bv_wrap in Hq.
  change (bv_modulus 5) with 32 in Hq.
  rewrite Z.mod_small in Hq by (unfold acallee_saved in Hr; lia).
  vm_compute in Hq. unfold acallee_saved in Hr. lia. }
(* ---- the cut at 0x813b8 ---- *)
assert (RC2 : rcore cx fp GP_sched0 t W2
  (mkst regs2 (Z_to_bv 64 (BASE + GP_sched0)) mem2 (seg_rom SEGS))).
{ eapply rm_rcore;
  [ exact HRC | lia | lia | exact KEEP
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | exact (QP 2 ltac:(unfold acallee_saved; lia))
  | exact (QP 3 ltac:(unfold acallee_saved; lia))
  | exact (QP 4 ltac:(unfold acallee_saved; lia))
  | exact (QP 8 ltac:(unfold acallee_saved; lia))
  | exact (QP 9 ltac:(unfold acallee_saved; lia))
  | exact (QP 20 ltac:(unfold acallee_saved; lia))
  | exact (QP 21 ltac:(unfold acallee_saved; lia))
  | exact (QP 22 ltac:(unfold acallee_saved; lia))
  | exact (QP 24 ltac:(unfold acallee_saved; lia))
  | exact (QP 25 ltac:(unfold acallee_saved; lia)) ]. }
assert (GT2 : gtab B cx ly2 S2 W2
  (mkst regs2 (Z_to_bv 64 (BASE + GP_sched0)) mem2 (seg_rom SEGS)) t (GrantSlotPlan.T_end (c_pl cx))).
{ eapply rm_gtab; [exact HTAB | rewrite Egb1; apply in_or_app; right; left; reflexivity |].
  intros a Ha. apply KEEP. right. right. right. right. exact Ha. }
apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2
  (mkst regs2 (Z_to_bv 64 (BASE + GP_sched0)) mem2 (seg_rom SEGS)) md2 HB HJ2
  ltac:(rewrite Hfrs2; exact HFR)
  (mle_station MT (c_S cx) S3 S2 acc (mo_free MT) MTL HMLE MLE2)).
destruct RC2 as (B2 & N2 & R20' & R21' & R22' & R24' & R25' & S88' & SL2 & _ & _ & WS2 & ST2 & HR2 & HI2).
unfold GI_sched0. exists t.
split; [exact B2|].
split; [lia|].
split; [unfold GE_A3; lia|].
split; [exact Egb1|].
split; [exact N2|].
split; [exact R20'|].
split; [exact R21'|].
split; [exact R22'|].
split; [exact R25'|].
split; [exact R24'|].
split; [exact S88'|].
split; [exact SL2|].
split; [exact GT2|].
split; [exact WS2|].
split; [exact ST2|].
split; [exact HR2 | exact HI2].
Qed.

End c.
End b.
End a.
