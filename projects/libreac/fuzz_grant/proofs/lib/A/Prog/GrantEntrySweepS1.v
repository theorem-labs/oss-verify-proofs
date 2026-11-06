(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS1), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Segment 1 of the sweep phase of fuzz_grant's entry function on the ASan build:
   0x81298 .. 0x812ac — free(sweep) at 0x8129c and the three spill slots the code
   reads back (the shadow offset, the bytes of input left and the address of `raw`),
   which is the state 0x812ac asks for. The ground this walk stands on is
   GrantEntrySweepS1c.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo
GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySweepS1c.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the walk of 0x81298 .. 0x812ac ---- *)

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gs_free1 :
  ge_from B MT (ge_post B MT) (GI_raw B MT) -> ge_from B MT (ge_post B MT) (GIS_free1 B MT).
Proof.
intros HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & s & HBODY & Hk & Hacc & HBLK & R22).
destruct HBLK as (Eab & Hsin & HTAB & HWAS & HSET & HREL & HI1 & SLATE & SL88 & SL120 & SL96 & SL64 & R20 & Hn26 & Ht0 & Hs0 & HAB).
pose proof SLATE as (SMID & SL8 & SL32 & SL40 & SL72 & SL80 & SL104 & SL112 & SL128).
pose proof SMID as (SL16 & SL24 & SL48 & SL56 & SL136 & SL144 & SL152 & SL176).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HREGS & HSAVED & HSH & HFL & HLEN & HINP).
pose proof HREGS as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032 & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk0 & JK1 & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hsp288 : 0 <= spZ (c_regs cx) + -288) by lia.
assert (Hmod288 : (spZ (c_regs cx) + -288) mod 16 = 0)
  by (rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity).
destruct (sp1_facts (spZ (c_regs cx) + -288) Hsp288 Hmod288) as (Hsp1r & Hsp1al32 & Hsp1al16).
rewrite <- Hsp1d in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1lo : alloc_ceiling <= c_sp1 cx) by lia.
assert (Hsp1hi : c_sp1 cx + 192 <= 2 ^ 64) by lia.
destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly3 HAR0 Hly3) as (Eabl & Efa & Eown).
assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp) by (unfold gF; rewrite Efa; reflexivity).
assert (HtIn : In (t, 460) (ablocks B ly3 S3)) by (destruct HTAB as (H & _); exact H).
assert (HpIn : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hn. rewrite Eab. apply in_or_app. left.
  destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
assert (HfrIn : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (gs_mbytes_range (c_pl cx)) as Hswr.
assert (Hnotin : ~ In (s, sw_mbytes (c_pl cx)) (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)])).
{ apply (gs_blocks_tail B ly3 S3 W3 (ms_mem ms3) md3 (ablocks B (c_ly cx) (c_S cx)) (t, 460)
    (s, sw_mbytes (c_pl cx)) LAWS HAR3 ltac:(cbn [snd]; lia)).
  rewrite Eab. reflexivity. }
assert (Htne : (t, 460) <> (s, sw_mbytes (c_pl cx))).
{ intros Heq. apply Hnotin. apply in_or_app. right. left. exact Heq. }
assert (Hpne : 0 < c_n cx -> (c_p cx, c_n cx) <> (s, sw_mbytes (c_pl cx))).
{ intros Hn Heq. apply Hnotin. apply in_or_app. left. rewrite <- Heq.
  destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
assert (GEO : gs_geo cx fp t s (sw_mbytes (c_pl cx))).
{ apply (gs_geo_of B cx fp t s (sw_mbytes (c_pl cx)) ly3 S3 W3 (ms_mem ms3) md3 LAWS HAR3 HtIn Htne
    ltac:(intros Hn; split; [exact (HpIn Hn) | exact (Hpne Hn)]) Hsin HfrIn EFA Hsp1lo Hsp1hi). }
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_free1)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms3; cbn in *; subst; reflexivity. }
assert (U9 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) (gsf_extra s (gF cx fp + GO_RAW)
               (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) 9%nat) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 9%nat 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (HEX : forall j, (j < 4)%nat ->
  ew (Eimg (Ereg (ms_regs ms3) (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) (32 + j)
  = nth j (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Hrs : Forall (YP09.region_ok SEGS (Eimg (Ereg (ms_regs ms3) (gsf_extra s (gF cx fp + GO_RAW)
                 (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) (mrestrict (w_H W3) (ms_mem ms3))) gsf_regions).
{ apply Forall_cons; [|apply Forall_nil].
  apply (gs_slotreg_ok W3 _ (ms_mem ms3) _ (c_sp1 cx) 0 0 U9 ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (gs_slot_chunk W3 _ (ms_mem ms3) 64 32%nat s (c_sp1 cx) (HEX 0%nat ltac:(lia)) U9 SL64).
  - apply (gs_slot_chunk W3 _ (ms_mem ms3) 72 33%nat (gF cx fp + GO_RAW) (c_sp1 cx) (HEX 1%nat ltac:(lia)) U9 SL72).
  - apply (gs_slot_chunk W3 _ (ms_mem ms3) 120 34%nat (c_n cx - Z.of_nat (pos_end (c_pl cx))) (c_sp1 cx)
      (HEX 2%nat ltac:(lia)) U9 SL120).
  - apply (gs_slot_chunk W3 _ (ms_mem ms3) 152 35%nat SHADOW_OFF (c_sp1 cx) (HEX 3%nat ltac:(lia)) U9 SL152). }
pose proof (gs_seat W3 (ms_regs ms3) (ms_mem ms3)
   (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))) GPS_free1 gsf_regions []
   ltac:(vm_compute; reflexivity) Hrs ltac:(cbn; tauto) I) as HS.
rewrite <- Ems3 in HS.
remember (Eimg (Ereg (ms_regs ms3) (gsf_extra s (gF cx fp + GO_RAW)
   (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (HEX 0%nat ltac:(lia)) as E32. pose proof (HEX 1%nat ltac:(lia)) as E33.
pose proof (HEX 2%nat ltac:(lia)) as E34. pose proof (HEX 3%nat ltac:(lia)) as E35.
cbn [gsf_extra nth Nat.add] in E32, E33, E34, E35.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly3 c p) by reflexivity.
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the memory the engine's run left: the regions it ran over are read-only *)
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end.
clear HF HFr HG.
assert (QSP : getr (ms_regs ms) 2 = w64 (c_sp1 cx))
  by (prreg HS (2%bv : bv 5) RR; rewrite RR, (EE 2%nat 2%bv eq_refl); exact R2).
assert (QGP : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (prreg HS (3%bv : bv 5) RR; rewrite RR, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (QTP : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (prreg HS (4%bv : bv 5) RR; rewrite RR, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (QS0 : getr (ms_regs ms) 8 = w64 (spZ (c_regs cx)))
  by (prreg HS (8%bv : bv 5) RR; rewrite RR, (EE 8%nat 8%bv eq_refl); exact R8).
assert (QS1 : getr (ms_regs ms) 9 = w64 (c_sp1 cx))
  by (prreg HS (9%bv : bv 5) RR; rewrite RR, (EE 9%nat 9%bv eq_refl); exact R9).
assert (QA0 : getr (ms_regs ms) 10 = w64 s)
  by (prreg HS (10%bv : bv 5) RR; rewrite RR; exact E32).
assert (QRA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0xbf0))
  by (prreg HS (1%bv : bv 5) RR; exact RR).
assert (Q20 : getr (ms_regs ms) 20 = w64 t)
  by (prreg HS (20%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q22 : getr (ms_regs ms) 22 = w64 (gSH cx fp))
  by (prreg HS (22%bv : bv 5) RR; rewrite RR, (EE 22%nat 22%bv eq_refl); exact R22).
assert (HEV : EV_MAX = 11776) by reflexivity.
assert (HGEV : GE_EV = 2000) by reflexivity.
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
(* the chain this call hands to the wrapper *)
assert (HCP : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) (gch cx)).
{ assert (Hrd : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia. }
  assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
    by (rewrite HM; exact (proj1 HSAVED)).
  assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { rewrite HM. pose proof (proj2 HSAVED 0 ltac:(lia)) as Hj0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
    cbn [Z.ltb Z.compare] in Hj0. exact Hj0. }
  pose proof (ge_achain B MT cx HB (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) Hrd H8 H16 ltac:(lia)) as HCH.
  apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx) (ms_regs ms)).
  - exact (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop HCH).
  - unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite QS0. unfold w64. apply unsigned_lit_small. lia.
  - unfold raZ. rewrite QRA. rewrite unsigned_lit_small by lia. lia. }
pmkst HS. rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (AFREE4 W3 (ms_regs ms) (ms_mem ms) GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k s (sw_mbytes (c_pl cx))
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 0xbf0)) (gch cx) HJ).
  - exact Hsin.
  - exact QA0.
  - unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - pose proof (proj1 (Z.mod_divide (c_sp1 cx) 16 ltac:(lia)) Hsp1al16) as [q1 Hq1].
    pose proof (proj1 (Z.mod_divide (spZ (c_regs cx)) 16 ltac:(lia)) Hal16) as [q2 Hq2].
    rewrite Hq1, Hq2. replace (q1 * 16 - q2 * 16) with ((q1 - q2) * 16) by lia. apply Z_mod_mult.
  - lia.
  - lia.
  - exact QGP.
  - exact QTP.
  - exact QRA.
  - apply (ret_ok_codeptr_v 0xbf0 ltac:(lia) ltac:(reflexivity)).
  - lia.
  - exact HCP.
  - apply HTR. right. split; [reflexivity|].
    unfold raZ. rewrite QRA, unsigned_lit_small by lia.
    replace (BASE + 3056 - BASE) with 3056 by lia. unfold GE_FSITES. cbn [In]. auto.
  - intros Hin i Hi. exfalso. apply Hnotin. apply in_or_app. left. exact Hin.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMO (mo_free_nonneg MT MTL)).
    unfold GE_NEED, GE_A3, GE_A2, GE_A1 in *.
    pose proof (mo_malloc_nonneg MT MTL 460 ltac:(lia)) as M1.
    pose proof (mo_malloc_nonneg MT MTL 8670 ltac:(lia)) as M2.
    pose proof (mo_malloc_nonneg MT MTL 4352 ltac:(lia)) as M3.
    pose proof (mo_free_nonneg MT MTL) as M4. lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Eb1 & Eb2) & Hfrs2 & HK & HMLE).
(* the blocks: the sweep block is gone, the table is what is left *)
assert (Eab2 : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]).
{ assert (Esplit : (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)]) ++ [(s, sw_mbytes (c_pl cx))]
    = l1 ++ (s, sw_mbytes (c_pl cx)) :: l2) by (rewrite <- Eb1, Eab, <- app_assoc; reflexivity).
  destruct (split_last_unique (s, sw_mbytes (c_pl cx)) _ _ _ Esplit Hnotin) as [-> ->].
  rewrite Eb2, app_nil_r. reflexivity. }
(* every byte this phase still speaks about is outside the block that was freed *)
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK by lia.
assert (KEEP : gs_keepW cx fp t W3 W2 (ms_mem ms) mem2).
{ apply (gs_keep_of_call B cx fp t s (sw_mbytes (c_pl cx)) ly3 S3 W3 (ms_mem ms) W2 mem2
    (fun a => s <= a < s + req_size (sw_mbytes (c_pl cx))) HK ltac:(intros a Ha; exact Ha)
    HtIn HpIn HFR EFA GEO). }
assert (KEEP3 : gs_keepW cx fp t W3 W2 (ms_mem ms3) mem2)
  by (rewrite <- HM; exact KEEP).
(* the three reloads of 0x812a0 .. 0x812a8, from the slots the call kept *)
assert (SL64b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 64) = Some s)
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL64]).
assert (SL72b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 72) = Some (gF cx fp + GO_RAW))
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL72]).
assert (SL120b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 120)
                 = Some (c_n cx - Z.of_nat (pos_end (c_pl cx))))
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL120]).
assert (SL152b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 152) = Some SHADOW_OFF)
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL152]).
assert (Q9b : getr regs2 9 = w64 (c_sp1 cx))
  by (rewrite (gs_kept_reg (ms_regs ms) regs2 (9%bv : bv 5) HP2
        ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
              unfold acallee_saved; rewrite HX; lia)); exact QS1).
assert (U9b : bv_unsigned (ew (Eimg (Ereg regs2 (gsf_extra s (gF cx fp + GO_RAW)
               (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) 9%nat) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat 9%bv eq_refl), Q9b. apply unsigned_lit_small. lia. }
assert (HEXb : forall j, (j < 4)%nat ->
  ew (Eimg (Ereg regs2 (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) (32 + j)
  = nth j (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Hrs2 : Forall (YP09.region_ok SEGS (Eimg (Ereg regs2 (gsf_extra s (gF cx fp + GO_RAW)
                 (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) (mrestrict (w_H W2) mem2)) gsf_regions).
{ apply Forall_cons; [|apply Forall_nil].
  apply (gs_slotreg_ok W2 _ mem2 _ (c_sp1 cx) 0 0 U9b ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (gs_slot_chunk W2 _ mem2 64 32%nat s (c_sp1 cx) (HEXb 0%nat ltac:(lia)) U9b SL64b).
  - apply (gs_slot_chunk W2 _ mem2 72 33%nat (gF cx fp + GO_RAW) (c_sp1 cx) (HEXb 1%nat ltac:(lia)) U9b SL72b).
  - apply (gs_slot_chunk W2 _ mem2 120 34%nat (c_n cx - Z.of_nat (pos_end (c_pl cx))) (c_sp1 cx)
      (HEXb 2%nat ltac:(lia)) U9b SL120b).
  - apply (gs_slot_chunk W2 _ mem2 152 35%nat SHADOW_OFF (c_sp1 cx) (HEXb 3%nat ltac:(lia)) U9b SL152b). }
pose proof (gs_seat W2 regs2 mem2
   (gsf_extra s (gF cx fp + GO_RAW) (c_n cx - Z.of_nat (pos_end (c_pl cx)))) 0xbf0 gsf_regions []
   ltac:(vm_compute; reflexivity) Hrs2 ltac:(cbn; tauto) I) as HS2.
remember (Eimg (Ereg regs2 (gsf_extra s (gF cx fp + GO_RAW)
   (c_n cx - Z.of_nat (pos_end (c_pl cx)))))) as E2 eqn:HE2.
clear HS HEI EE E32 E33 E34 E35 AG.
assert (HEI : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (HEXb 0%nat ltac:(lia)) as F32. pose proof (HEXb 1%nat ltac:(lia)) as F33.
pose proof (HEXb 2%nat ltac:(lia)) as F34. pose proof (HEXb 3%nat ltac:(lia)) as F35.
cbn [gsf_extra nth Nat.add] in F32, F33, F34, F35.
paj_run_to_sh RUNTOP HS2 HJ2 GP_raw.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the three loads wrote nothing, so the memory is the one the call left *)
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM2 end.
clear HF HFr HG.
assert (KEEPF : gs_keepW cx fp t W3 W2 (ms_mem ms3) (ms_mem ms0)) by (rewrite HM2; exact KEEP3).
assert (Hpn64 : c_p cx + c_n cx <= 2 ^ 64).
{ destruct Hpn as [(Hz & Hemp) | (Hn & Hin)].
  - rewrite Hz, Hemp. unfold GE_EMPTY. lia.
  - destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
      as (_ & _ & Hce & _). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
(* the registers the next cut names *)
assert (G2 : getr (ms_regs ms0) 2 = w64 (c_sp1 cx)).
{ prreg HS2 (2%bv : bv 5) RR. rewrite RR, (EE2 2%nat 2%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (2%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (2%bv : bv 5) = 2) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  exact QSP. }
assert (G8 : getr (ms_regs ms0) 8 = w64 (spZ (c_regs cx))).
{ prreg HS2 (8%bv : bv 5) RR. rewrite RR, (EE2 8%nat 8%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (8%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (8%bv : bv 5) = 8) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  exact QS0. }
assert (G9 : getr (ms_regs ms0) 9 = w64 (c_sp1 cx)).
{ prreg HS2 (9%bv : bv 5) RR. rewrite RR, (EE2 9%nat 9%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (9%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  exact QS1. }
assert (G3 : getr (ms_regs ms0) 3 = getr (c_regs cx) 3).
{ prreg HS2 (3%bv : bv 5) RR. rewrite RR, (EE2 3%nat 3%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (3%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (3%bv : bv 5) = 3) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  rewrite QGP. symmetry. exact Hgp. }
assert (G4 : getr (ms_regs ms0) 4 = getr (c_regs cx) 4).
{ prreg HS2 (4%bv : bv 5) RR. rewrite RR, (EE2 4%nat 4%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (4%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (4%bv : bv 5) = 4) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  rewrite QTP. symmetry. exact Htp. }
assert (G20 : getr (ms_regs ms0) 20 = w64 t).
{ prreg HS2 (20%bv : bv 5) RR. rewrite RR, (EE2 20%nat 20%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (20%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (20%bv : bv 5) = 20) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  exact Q20. }
assert (G22 : getr (ms_regs ms0) 22 = w64 (gSH cx fp)).
{ prreg HS2 (22%bv : bv 5) RR. rewrite RR, (EE2 22%nat 22%bv eq_refl),
    (gs_kept_reg (ms_regs ms) regs2 (22%bv : bv 5) HP2
      ltac:(assert (HX : bv_unsigned (22%bv : bv 5) = 22) by (vm_compute; reflexivity);
            unfold acallee_saved; rewrite HX; lia)).
  exact Q22. }
assert (G21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
  by (prreg HS2 (21%bv : bv 5) RR; rewrite RR; exact F35).
assert (G24 : getr (ms_regs ms0) 24 = w64 (c_n cx - Z.of_nat (pos_end (c_pl cx))))
  by (prreg HS2 (24%bv : bv 5) RR; rewrite RR; exact F34).
assert (G25 : getr (ms_regs ms0) 25 = w64 (gF cx fp + GO_RAW))
  by (prreg HS2 (25%bv : bv 5) RR; rewrite RR; exact F33).
(* the lengths of the frame's two arrays *)
destruct (SegSetModel.tables_end_inv (c_pl cx)) as (_ & HwsL & HstL & _).
pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
  in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 ms0).
- exact HB.
- exact HJ2.
- rewrite Hfrs2. exact HFR.
- exact (mle_station MT (c_S cx) S3 S2 acc (mo_free MT) MTL HMO HMLE).
- exists t.
  split.
  { apply (gs_keep_body cx fp t GPS_free1 GP_raw W3 W2 ms3 ms0 GSH_a KEEPF ltac:(lia) ltac:(lia) ltac:(lia) Hpn64
      Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0
      ltac:(unfold gregs; split; [exact G2|]; split; [exact G8|]; split; [exact G9|];
            split; [exact G3 | exact G4]) HBODY). }
  split; [lia|]. split; [lia|].
  split; [exact Eab2|]. split; [exact Hn26|].
  split; [exact G20|]. split; [exact G21|]. split; [exact G22|]. split; [exact G24|]. split; [exact G25|].
  split.
  { apply (gs_keep_gslot cx fp t W3 W2 ms3 ms0 88 (c_p cx + Z.of_nat (pos_end (c_pl cx))) KEEPF
      ltac:(lia) ltac:(lia) SL88). }
  split.
  { apply (gs_keep_gslot cx fp t W3 W2 ms3 ms0 96 (gF cx fp + GO_LIT) KEEPF ltac:(lia) ltac:(lia) SL96). }
  split.
  { apply (gs_keep_gslots_late cx fp t W3 W2 ms3 ms0 KEEPF ltac:(lia) SLATE). }
  split.
  { destruct (gs_keep_gtab B cx fp ly3 S3 W3 W2 ms3 ms0 t (T_end (c_pl cx)) KEEPF HTAB)
      as (_ & Ht0' & Hlen' & Hbytes').
    split; [rewrite Eab2; apply in_or_app; right; left; reflexivity|].
    split; [exact Ht0'|]. split; [exact Hlen' | exact Hbytes']. }
  split.
  { apply (gs_keep_gfarr cx fp t W3 W2 ms3 ms0 GO_WAS (ws_end (c_pl cx)) KEEPF ltac:(unfold GO_WAS; lia)
      ltac:(rewrite HwsL; unfold GO_WAS; vm_compute (fs_frame_bytes GE_CID); lia) HWAS). }
  split.
  { apply (gs_keep_gfarr cx fp t W3 W2 ms3 ms0 GO_SET (st_end (c_pl cx)) KEEPF ltac:(unfold GO_SET; lia)
      ltac:(rewrite HstL; unfold GO_SET; vm_compute (fs_frame_bytes GE_CID); lia) HSET). }
  split; [exact HREL | exact HI1].
Qed.


End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

Lemma gsw_seg_free1 : forall (B : asyms) (MT : ameter_ops), @SEG_free1 fx rc SK PI B MT.
Proof.
intros B MT RT NEXT.
destruct RT as (LAWS & TL & MTL & MTF & AMALLOC4 & AFREE4 & AFREEN4 & ABCMP & HIMG & ML & TLF).
exact (gs_free1 B MT LAWS TL MTL AFREE4 NEXT).
Qed.

End zb.
End z.

