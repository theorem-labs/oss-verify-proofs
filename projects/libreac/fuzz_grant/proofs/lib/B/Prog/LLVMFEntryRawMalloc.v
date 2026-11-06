(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawMalloc), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryRawMalloc.v. *)
(* Ported from lib/A/Prog/GrantEntryRawMalloc.v of a working branch 7c8c67da870 (blob 919b28c3e49). *)
(* The malloc segment of the hand-built allocation phase of LLVMFuzzerTestOneInput on image B
   (fuzz_grant.c:369; slots 0x818b4 .. 0x818cc).

   At GR_mal (0x818b4) a0 holds 4352 and `jal 0x52edc` calls the memory-checking runtime's
   wrapper for malloc with the return address BASE + 0xe7c. `amalloc04_rule` gives a block
   s >= 4096 of 4352 bytes after the blocks the call found, and keeps every byte outside the
   stack window under s1 and outside the new block: the spill slots and saved words above
   s1, the caller's input, the frame on the side stack for frames and its shadow, and the
   table. Then `beqz a0, 0x81d98` (the abort) is not taken, because s >= 4096, and
   `mv s2,a0; li a1,128; mv a2,s5; mv a3,s4` set up the call of reac_grant_build_sweep at
   GR_bs1 (0x818cc), which is the cut GR_bs1I. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib YC1g YC1h YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySetDefs LLVMFEntryRawDefs LLVMFEntryRawLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* A register of the current state, read back from the symbolic state `HS` as the atom of
   the register in the entry environment `E` (EE : ew E n = getr regs r). *)
Ltac rm_q HS EE r n Q := prreg HS r Q; rewrite (EE n r eq_refl) in Q.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- 0x818b4 .. 0x818cc: malloc(4352), the check of its answer, the arguments of the
   first call of reac_grant_build_sweep ---- *)
Theorem seg_raw_mal : forall POST, ge_from B MT POST (GR_bs1I B MT) -> ge_from B MT POST (GR_malI B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HRC & Hk & Hacc & Hbl & HTAB & R20 & R10).
pose proof HRC as (HBODY & Hn26 & R19 & R21 & R22 & R23 & _).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HGR & HSAVED & _).
pose proof HGR as (G2 & G8 & G9 & G3 & G4).
pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ & HMOK & HTR & HNEED).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
unfold gblk1 in Hbl.
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (L := grant_listing)) as HBLO.
rewrite IMG_LO_B_val in HBLO.
assert (HtIn : In (t, 460) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hfin3 : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (HgF8 : 0 <= gF cx fp / 8 /\ 8 * (gF cx fp / 8) <= gF cx fp)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by (unfold shadow_addr; rewrite L11; reflexivity).
assert (RNG : forall a, rm_at cx fp t a -> 0 <= a < 2 ^ 64).
{ intros a [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - lia.
  - assert (Hn0 : 0 < c_n cx) by lia. destruct (L16 Hn0) as (P1 & P2 & _). lia.
  - lia.
  - rewrite L11 in Ha. unfold SHADOW_OFF in Ha. lia.
  - lia. }
(* the call: `jal 0x52edc` at 0x818b4 *)
rewrite (gmach_mkst cx ms3 GR_mal ltac:(split; [exact Hpc|]; split; [exact Hresv|]; split; [exact Hsvc|];
  split; [exact Hrom|]; split; [exact Hfrg|]; split; [exact Hfcsr | exact HGR])).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS GR_mal sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GR_mal)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. first
  [ match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ => exact (frame_nil_eq _ _ _ _ _ eq_refl H1 a) end
  | match goal with H1 : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms1)) |- _ =>
      exact (frame_wins _ _ _ _ _ (fun _ => False) H1 ltac:(intros x (r & Hr & _); destruct Hr) a Ha (fun x => x)) end
  | (match goal with |- ?g => idtac "M1-LEFT" g end; fail) ]. }
rm_q HS EE (2%bv : bv 5) 2%nat Q2. rm_q HS EE (3%bv : bv 5) 3%nat Q3. rm_q HS EE (4%bv : bv 5) 4%nat Q4.
rm_q HS EE (8%bv : bv 5) 8%nat Q8. rm_q HS EE (9%bv : bv 5) 9%nat Q9. rm_q HS EE (10%bv : bv 5) 10%nat Q10.
rm_q HS EE (19%bv : bv 5) 19%nat Q19. rm_q HS EE (20%bv : bv 5) 20%nat Q20. rm_q HS EE (21%bv : bv 5) 21%nat Q21.
rm_q HS EE (22%bv : bv 5) 22%nat Q22. rm_q HS EE (23%bv : bv 5) 23%nat Q23.
assert (Q1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 0xe7c)) by (prreg HS (1%bv : bv 5) RR; exact RR).
assert (Usp : spZ (ms_regs ms1) = c_sp1 cx) by (unfold spZ; rewrite Q2, G2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS. rewrite (pal_malloc B TL).
(* the chain the wrapper gets *)
assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
{ rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1))); [exact (proj1 HSAVED)|].
  intros j Hj. apply M1. lia. }
assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem ms1)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms1))).
  - pose proof (proj2 HSAVED 0 ltac:(lia)) as Hj0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
    cbn [Z.ltb Z.compare] in Hj0. exact Hj0.
  - intros j Hj. apply M1. lia. }
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ eapply g_chain; first [exact LAWS | exact HB | exact HJ | exact H8 | exact H16]. }
(* the malloc wrapper: a block s >= 4096 of 4352 bytes after the blocks so far *)
eapply SRr_bind.
{ eapply (AMALLOC4 W3 (ms_regs ms1) (ms_mem ms1) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k RAW_SW (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 0xe7c)) (gch cx) HJ).
  - rewrite Q10. exact R10.
  - unfold RAW_SW, MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B ly3 S3), Hbl, bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
    cbn [bsum fold_right snd]. unfold GE_LIVE, LIVE_LIB_B, LIVE_MAX, RAW_SW in *. lia.
  - rewrite Usp. lia.
  - exact (mod_sub16 _ _ L5 L2).
  - lia.
  - lia.
  - rewrite Q3, G3. exact Hgp.
  - rewrite Q4, G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold GE_EV, EV_LIB_B in Hev. lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (gch cx) (ms_regs ms1) HCH).
    + rewrite Usp. lia.
    + unfold s0Z. rewrite Q8, G8. unfold w64. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply HTR. left. split; [reflexivity|]. unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    replace (BASE + 0xe7c - BASE) with 0xe7c by lia. unfold GE_MSITES, TB_LLVMF_MSITES. cbn [In]. auto.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT RAW_SW) MTL HMOK HMO).
    + apply (mo_malloc_nonneg MT MTL). unfold RAW_SW. lia.
    + unfold GE_NEED, GE_A3, RAW_SW in *. pose proof (mo_free_nonneg MT MTL). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & s & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hs4096 & Eab2 & HK2 & MLE2).
assert (HsIn : In (s, RAW_SW) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ s RAW_SW HAR2 HsIn) as (_ & _ & Hsc & Hsapp & _).
change (req_size RAW_SW) with 4352 in Hsc, Hsapp.
assert (EF2 : frame_addr ly2 GE_CID fp = gF cx fp)
  by (unfold gF; apply (proj2 (g_ly B cx fp (k + 1) ly2 S2 W2 mem2 md2 HJ2))).
assert (Hfin2 : In (GE_CID, fp) (frames S2)) by (rewrite Hfrs2; exact Hfin3).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ s RAW_SW GE_CID fp HAR2 HsIn Hfin2) as DSF.
rewrite EF2 in DSF. unfold zdisjoint in DSF. cbn [fst snd] in DSF.
change (req_size RAW_SW) with 4352 in DSF. change (fs_frame_bytes GE_CID) with 1024 in DSF.
pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (t, 460) (s, RAW_SW) (ablocks B (c_ly cx) (c_S cx)) [] [] HAR2
  ltac:(rewrite Eab2, Hbl, <- app_assoc; reflexivity)) as DTS.
unfold zdisjoint, block_rng in DTS. cbn [fst snd] in DTS.
change (req_size 460) with 460 in DTS. change (req_size RAW_SW) with 4352 in DTS.
assert (DPS : 0 < c_n cx -> c_p cx + c_n cx <= s \/ s + 4352 <= c_p cx).
{ intros Hn0. destruct Hpn as [[Hz _] | [_ Hin0]]; [lia|].
  apply in_split in Hin0 as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (c_p cx, c_n cx) (s, RAW_SW) l1 (l2 ++ [(t, 460)]) [] HAR2
    ltac:(rewrite Eab2, Hbl, El, <- !app_assoc; reflexivity)) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size RAW_SW) with 4352 in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
assert (DSH : forall a, gSH cx fp <= a < gSH cx fp + 128 -> ~ (s <= a < s + 4352)).
{ intros a Ha. rewrite L11 in Ha.
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hsapp. try rewrite C3 in Hsapp.
  unfold SHADOW_OFF in Ha. lia. }
(* what the call kept *)
assert (KM2 : forall a, rm_at cx fp t a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms1) a).
{ destruct HK2 as (K1 & K2 & _ & K4 & _ & _).
  intros a [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; lia.
  - assert (Hn0 : 0 < c_n cx) by lia. specialize (DPS Hn0).
    destruct Hpn as [[Hz _] | [_ Hin0]]; [lia|].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx)).
    + rewrite Hbl. apply in_or_app. left. exact Hin0.
    + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
    + cbv beta. change (req_size RAW_SW) with 4352. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite L6. change (fs_frame_bytes GE_CID) with 1024. lia.
    + cbv beta. change (req_size RAW_SW) with 4352. lia.
  - apply (K4 GE_CID fp a Hfin3).
    + right. unfold in_zr. cbn [fst snd]. rewrite L6, Hsa. change (fs_frame_bytes GE_CID / 8) with 128. lia.
    + cbv beta. change (req_size RAW_SW) with 4352. exact (DSH a Ha).
  - replace a with (t + (a - t)) by lia.
    apply (K2 t 460 (a - t) HtIn).
    + change (req_size 460) with 460. lia.
    + cbv beta. change (req_size RAW_SW) with 4352. lia. }
assert (KP : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms1) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
(* 0x818b8: `beqz a0, 0x81d98`, then the moves up to 0x818cc *)
remember (Eimg (Ereg regs2 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 0xe7c sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xe7c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK2 : sh_ok SEGS GBx [] E2 (mrestrict (w_H W2) mem2)) by constructor.
assert (E2a0 : ew E2 10 = Z_to_bv 64 s) by (rewrite (EE2 10%nat 10%bv eq_refl); exact Ha02).
clear HS SHOK.
psrr_branch_tok RUN BR HS2 SHOK2 GBspan.
- (* a0 = 0: the abort at 0x81d98, not reached *)
  exfalso. rewrite branch_eq_U, (U_atom _ 10 s E2a0), U_SLit in Hc by lia.
  apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. lia.
- clear Hc.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan GR_bs1; [first [apply awr_ok_nil | gshow] |].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms4 end.
  assert (M4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. first
    [ match goal with H1 : frame_of _ _ mem2 (ms_mem ms4) |- _ => exact (frame_nil_eq _ _ _ _ _ eq_refl H1 a) end
    | match goal with H1 : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms4)) |- _ =>
        exact (frame_wins _ _ _ _ _ (fun _ => False) H1 ltac:(intros x (r & Hr & _); destruct Hr) a Ha (fun x => x)) end
    | (match goal with |- ?g => idtac "M4-LEFT" g end; fail) ]. }
  destruct (gst_ok_mach _ _ _ _ HS2 eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
  assert (KF : forall a, rm_at cx fp t a -> aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite (M4 a (RNG a Ha)), (KM2 a Ha), (M1 a (RNG a Ha)). reflexivity. }
  (* the registers at 0x818cc *)
  rm_q HS2 EE2 (2%bv : bv 5) 2%nat F2. rm_q HS2 EE2 (3%bv : bv 5) 3%nat F3. rm_q HS2 EE2 (4%bv : bv 5) 4%nat F4.
  rm_q HS2 EE2 (8%bv : bv 5) 8%nat F8. rm_q HS2 EE2 (9%bv : bv 5) 9%nat F9.
  rm_q HS2 EE2 (19%bv : bv 5) 19%nat F19. rm_q HS2 EE2 (20%bv : bv 5) 20%nat F20.
  rm_q HS2 EE2 (21%bv : bv 5) 21%nat F21. rm_q HS2 EE2 (22%bv : bv 5) 22%nat F22.
  rm_q HS2 EE2 (23%bv : bv 5) 23%nat F23.
  rm_q HS2 EE2 (10%bv : bv 5) 10%nat F10.
  prreg HS2 (18%bv : bv 5) F18. rewrite (EE2 10%nat 10%bv eq_refl) in F18.
  prreg HS2 (12%bv : bv 5) F12. rewrite (EE2 21%nat 21%bv eq_refl) in F12.
  prreg HS2 (13%bv : bv 5) F13. rewrite (EE2 20%nat 20%bv eq_refl) in F13.
  prreg HS2 (11%bv : bv 5) F11.
  rewrite (KP 2%bv ltac:(change (bv_unsigned (2%bv : bv 5)) with 2; unfold acallee_saved; lia)), Q2 in F2.
  rewrite (KP 3%bv ltac:(change (bv_unsigned (3%bv : bv 5)) with 3; unfold acallee_saved; lia)), Q3 in F3.
  rewrite (KP 4%bv ltac:(change (bv_unsigned (4%bv : bv 5)) with 4; unfold acallee_saved; lia)), Q4 in F4.
  rewrite (KP 8%bv ltac:(change (bv_unsigned (8%bv : bv 5)) with 8; unfold acallee_saved; lia)), Q8 in F8.
  rewrite (KP 9%bv ltac:(change (bv_unsigned (9%bv : bv 5)) with 9; unfold acallee_saved; lia)), Q9 in F9.
  rewrite (KP 19%bv ltac:(change (bv_unsigned (19%bv : bv 5)) with 19; unfold acallee_saved; lia)), Q19 in F19.
  rewrite (KP 20%bv ltac:(change (bv_unsigned (20%bv : bv 5)) with 20; unfold acallee_saved; lia)), Q20 in F20, F13.
  rewrite (KP 21%bv ltac:(change (bv_unsigned (21%bv : bv 5)) with 21; unfold acallee_saved; lia)), Q21 in F21, F12.
  rewrite (KP 22%bv ltac:(change (bv_unsigned (22%bv : bv 5)) with 22; unfold acallee_saved; lia)), Q22 in F22.
  rewrite (KP 23%bv ltac:(change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia)), Q23 in F23.
  apply (HNEXT cx fp (k + 1) (acc + mo_malloc MT RAW_SW) ly2 S2 W2 ms4 _ HB HJ2 (eq_trans Hfrs2 HFR)
    (mle_station MT (c_S cx) S3 S2 acc (mo_malloc MT RAW_SW) MTL HMO MLE2)).
  unfold GR_bs1I. exists t, s.
  split.
  { exact (rm_rcore cx fp GR_mal GR_bs1 t W3 ms3 W2 ms4 HRC L3 (proj2 L4) KF Pc Prv Psv Pro Pfr Pfc
      F2 F3 F4 F8 F9 F19 F21 F22 F23). }
  split; [lia|]. split; [lia|].
  split; [unfold gblk2; rewrite Eab2, Hbl, <- app_assoc; reflexivity|].
  split.
  { apply (rm_gtab B cx ly3 S3 ly2 S2 W3 ms3 W2 ms4 t _ HTAB).
    - rewrite Eab2. apply in_or_app. left. exact HtIn.
    - intros a Ha. apply KF. right; right; right; right. exact Ha. }
  split; [exact Hs4096|].
  split; [rewrite F20; exact R20|].
  split; [rewrite F18; exact Ha02|].
  split; [rewrite F10; exact Ha02|].
  split; [rewrite F11; reflexivity|].
  split; [rewrite F12; exact R21|].
  rewrite F13. exact R20.
Qed.

End c.
End b.
End a.
