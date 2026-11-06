(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_seg_ent.v, with its module paths and module names changed; 611 of its 706 lines of code are new or changed and 571 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk (lib/A/Prog/S6PjFree.v), the ENTRY segment.
   rule 24: proves no function (kind: segment lemma of pj_free's walk).
   pf_seg_entry (pfs_entry): from pj_free's entry, the prologue (the twelve saves, sp -= 96) and `beqz a0`; v = NULL:
   the epilogue and the ret, to the walk's post; v <> NULL (slots 13-26): s0 := v, the shadow base through the GOT
   word into s4, s2 := v+40, s5 := its cell, the ASan check of v+40 (v's 56 bytes addressable), n := v->n, s3 := v+24,
   s1 := v+32, `beqz n`; n = 0: to the cut after the loop PF_LX (+228); n <> 0: s6 = s7 = s8 = 0, s9 / s10 := the cells
   of v+24 / v+32, to the loop head PF_LH (+136) at slot 0. Both cuts are premises (KLX, KLH); the facts they ask of the
   entry are pfe_frame_ok / pfe_ledger_ok / pfe_vnode_ok / pfe_items_ok below (image B's pj_free_seg_ent.v pfn_* over
   A's cuts: the entry stretches write only the frame [sp0 - 96, sp0), above alloc_ceiling).
   THE RE-HIDING MOVE: the continuations (the cuts after the loop and at the loop head) cross frees, so the segment
   concludes SRr' SEGS RZ_cf (YA0nH) and runs over R := wle' SEGS RZ_cf: the entry's journal starts at wle'
   (YCbqGcallW.ajournal_x_init_WR, every wle step is a wle' step), the _invR runners (YC1fPx), paj_branchR (YSRrG),
   the ret's SRr step lifted by SRr_SRr', and the cuts' frame at wle' (pfe_frame_ok over any R). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure S6PjFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeGlue.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

Section e.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_A: the entry (DERIVED: slot * 4, PAImg_prog A_entry_pj_free), the GOT word of
   the shadow base and the shadow cell lie in the image's segments, the image start, alloc.c's statics are image bytes
   (lib/A/Prog/S1ImgA.v pst_in_img_A) *)
Hypothesis Hent : SIGMA AS_pj_free = BASE + AF_pf.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
Hypothesis pal_pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Variable CTX0 : list (list Z).
Variable PB : astate -> Prop.
Variable FX : pf_obs.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* ---- what the cuts after the prologue take of the entry (v <> NULL) ---- *)
(* D's order: the slots' blocks, then the node's own (image B's pfn_perm) *)
Lemma pfe_perm : forall (D Ds Dk Dy Di : list (Z * Z)),
  Permutation D (Ds ++ Dk ++ Dy ++ Di) -> Permutation D ([] ++ Di ++ (Dk ++ Dy ++ Ds)).
Proof.
intros D Ds Dk Dy Di H. cbn [app]. eapply Permutation_trans; [exact H|].
eapply Permutation_trans; [apply Permutation_app_comm|].
rewrite !app_assoc. apply Permutation_app_tail. rewrite <- (app_assoc Di Dk Dy). apply Permutation_app_comm.
Qed.

(* glue another loop segment can use *)
(* the ASan cell of an atom plus an offset, (x + c) >> 3 + the shadow offset (S6PjFree.v pft_seat's Hcell) *)
Lemma pfe_U_cell : forall (E : env) (nv nb : nat) v c, ew E nv = Z_to_bv 64 v -> ew E nb = Z_to_bv 64 SHADOW_OFF ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nv c) (SLit 3)) (SOff nb 0)) = (v + c) / 8 + SHADOW_OFF.
Proof.
intros E nv nb v c Hv Hb H0 Hc Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (U_atom_off E nv v c Hv) by lia. rewrite (U_atom E nb SHADOW_OFF Hb) by (unfold SHADOW_OFF; lia).
assert (Hq : 0 <= (v + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold zcanon, M64, SHADOW_OFF in *. apply Z.mod_small. lia.
Qed.

(* pj_free's frame at a cut of the entry run (no call yet: the entry's ly, S, Hp, W), its journal at any world
   relation R *)
Lemma pfe_frame_ok : forall (R : world SEGS -> world SEGS -> Prop) en rg mm dd,
  pf_pre B ARx CTX0 PB FX en ->
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en)
    mm dd 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - 96 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  spZ rg = fe_sp0 en - 96 ->
  (forall o r, In (o, r) pf_saves1 ->
     val_mem SEGS (mrestrict (w_H (fe_W en)) mm) (fe_sp0 en - 96 + o) 8
       (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 (Z.of_nat r))))) ->
  getr rg 3 = getr (fe_regs en) 3 -> getr rg 4 = getr (fe_regs en) 4 -> getr rg 27 = getr (fe_regs en) 27 ->
  (Pm (fe_mem en) -> Pm mm) ->
  pf_frameR SK B ARx Pm R en (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) rg mm dd 0.
Proof.
intros R en rg mm dd HPRE HJ KALL Hsp HSV G3 G4 G27 HPM.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as ([HAFN [HROD _]] & _ & _ & _ & HWIN & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (ajxR_pres HJ) as HpresJ.
unfold pf_frameR. unfold fe_sp0 in *.
split; [exact HJ|].
split; [intros a Ha _; apply KALL; lia|].
split; [exact Hsp|].
split; [exact HSV|].
split; [intros a Ha; apply HpresJ; lia|].
split; [exact G3|]. split; [exact G4|]. split; [exact G27|].
split; [|exact HPM].
apply (gs_rod_kept B (fe_W en) (fe_W en) (fe_mem en) mm HROD).
intros a Ha. apply KALL; lia.
Qed.

(* the ledger at a cut of the entry run: the statics and the heads lie below the frame *)
Lemma pfe_ledger_ok : forall en mm,
  pf_pre B ARx CTX0 PB FX en ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - 96 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  prh_ledger (PA := PA) B (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) mm (fe_Lam en)
    (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en).
Proof.
intros en mm HPRE KALL.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as ([[HAR _] _] & _ & _ & _ & _ & _ & _ & HLED).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
apply (prh_ledger_kept_aview B (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en)
  (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) mm (fe_Lam en) (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en)
  (fe_most en) (fe_own en) HLED).
- intros a Ha. pose proof (Hsegs a (pal_pst_img a Ha)). apply KALL; [unfold kLowMemEnd in *; lia|].
  unfold kLowMemEnd, YM05.alloc_ceiling in *. lia.
- intros a k0 i Hin Hi. change (@cf_head CP) with 16 in *.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED Hin) as (Hk0 & Hab & _).
  change (@cf_head CP) with 16 in *.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (k0 + 16) ltac:(lia)) as Rq.
  apply KALL; unfold YM05.alloc_ceiling in *; lia.
- intros a k0 _ H. exact H.
- apply Permutation_refl.
Qed.

(* v's node at a cut of the entry run: the header words read, its place, its shadow, as at the entry *)
Lemma pfe_vnode_ok : forall en nd mm,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd -> fe_v en <> 0 -> fe_v en + 56 <= YM05.alloc_ceiling ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - 96 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  mem_grows (mrestrict (w_H (fe_W en)) (fe_mem en)) (mrestrict (w_H (fe_W en)) mm) ->
  pf_vnode B en nd (fe_ly en) (fe_S en) (fe_Lam en) (fe_W en) mm.
Proof.
intros en nd mm HPRE HND Hv0 Hv56 KALL MG.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (_ & _ & _ & _ & _ & HV & _).
destruct HV as [(Hv & _) | (_ & HCEIL & _ & HSLOT)]; [contradiction|].
pose proof HSLOT as (H4096 & HAT & HRWs & HAMR & HWIN & HRA & HHU).
pose proof HRWs as (Hv8 & Hrw56).
pose proof HND as (_ & HAP & HHDR & _).
pose proof HHDR as (_ & _ & _ & Hstr & Hkids & Hkeys & Hnn & _).
assert (Kv : forall x, fe_v en <= x < fe_v en + 56 ->
  mbyte SEGS (mrestrict (w_H (fe_W en)) mm) x = mbyte SEGS (mrestrict (w_H (fe_W en)) (fe_mem en)) x).
{ intros x Hx. apply (mbyte_of_aview SEGS). apply KALL; lia. }
unfold pf_vnode. cbv zeta.
split; [exact H4096|]. split; [exact Hv56|]. split; [exact Hv8|]. split; [exact HAMR|].
split; [apply (rd_u64_frame SEGS _ _ _ _ Hstr); intros y Hy; apply Kv; lia|].
split; [apply (rd_u64_frame SEGS _ _ _ _ Hkids); intros y Hy; apply Kv; lia|].
split; [apply (rd_u64_frame SEGS _ _ _ _ Hkeys); intros y Hy; apply Kv; lia|].
split; [apply (rd_u64_frame SEGS _ _ _ _ Hnn); intros y Hy; apply Kv; lia|].
split; [split; [exact Hv8 | intros x Hx; exact (writable_at_grows SEGS _ _ x MG (Hrw56 x Hx))]|].
split; [intros a Ha; exact (proj1 (HWIN a Ha))|].
split.
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)).
  apply KALL; lia. }
split.
{ intros s Hs. pose proof (gs_hull_low (fe_v en) 56 s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
  rewrite KALL by lia. exact (HHU s Hs). }
destruct HAT as [(a & k & Hin & Ha & Hk) | [Hb | [Hf | (Hw1 & Hw2)]]].
- left. exists a, k. split; [exact Hin|]. split; [|lia].
  intros HinD. apply (HAP (a, k) (fe_v en) HinD); [unfold pj_holdsR; cbn [fst snd]; lia | lia].
- right; left. exact Hb.
- right; right. exact Hf.
- exfalso. unfold fe_sp0 in *. lia.
Qed.

(* the slots still to free at slot 0 of a cut of the entry run: their bytes lie in the entry's harness blocks *)
Lemma pfe_items_ok : forall en nd d' mm,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd -> fe_n en = Datatypes.S d' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - 96 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  mem_grows (mrestrict (w_H (fe_W en)) (fe_mem en)) (mrestrict (w_H (fe_W en)) mm) ->
  pf_oitemsR SEGS (mrestrict (w_H (fe_W en)) mm) (prh_lin (fe_Lam en))
    (pj_foR SEGS (mrestrict (w_H (fe_W en)) mm) (prh_lin (fe_Lam en)) d')
    (fn_ks nd) (fn_kids nd + 56 * 0) (fn_keys nd + 8 * 0) (Z.to_nat (fn_n nd - 0)) (fn_Di nd) (fn_Fi nd).
Proof.
intros en nd d' mm HPRE HND Hn KALL MG.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as ([[HAR _] _] & _ & _ & _ & _ & _ & _ & HLED).
pose proof HND as (_ & _ & HHDR & _ & HKIDS & HKEYS & _ & _ & HITEMS).
rewrite Hn in HITEMS.
pose proof HHDR as (_ & _ & _ & _ & _ & _ & Hnn & _).
replace (fn_kids nd + 56 * 0) with (fn_kids nd) by lia. replace (fn_keys nd + 8 * 0) with (fn_keys nd) by lia.
replace (fn_n nd - 0) with (fn_n nd) by lia.
assert (Hlow : forall a k x, In (a, k) (fe_Lam en) -> a <= x < a + k ->
  aview SEGS (w_H (fe_W en)) mm x = aview SEGS (w_H (fe_W en)) (fe_mem en) x).
{ intros a k x Hin Hx. change (@cf_head CP) with 16 in *.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk0 & Hab & _).
  change (@cf_head CP) with 16 in *.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (k + 16) ltac:(lia)) as Rq.
  apply KALL; unfold YM05.alloc_ceiling in *; lia. }
apply (pf_oitemsR_frame SEGS d' _ _ (prh_lin (fe_Lam en)) (prh_lin (fe_Lam en)) _ _ _ _ _ _ HITEMS).
- intros x k Hin. exact (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HITEMS x k Hin).
- intros x Hx.
  assert (Hxk : aview SEGS (w_H (fe_W en)) mm x = aview SEGS (w_H (fe_W en)) (fe_mem en) x).
  { destruct Hx as [Hx | [(Hks & Hx) | ((a & k) & Hin & Hh)]].
    - destruct HKIDS as [(Hk0 & Hn0 & _) | (kk & Hkk & Hkn & _)].
      + rewrite Hn0 in Hx. cbn in Hx. lia.
      + apply (Hlow (fn_kids nd) kk x Hkk). pose proof (proj1 Hnn). lia.
    - destruct HKEYS as [(_ & Hks' & _) | (_ & ky & Hky & Hkn & _)]; [congruence|].
      apply (Hlow (fn_keys nd) ky x Hky). pose proof (proj1 Hnn). lia.
    - apply (Hlow a k x (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HITEMS a k Hin)). unfold pj_holdsR in Hh. cbn in Hh. lia. }
  split; [apply (mbyte_of_aview SEGS); exact Hxk | intros Hw; exact (writable_at_grows SEGS _ _ x MG Hw)].
Qed.

(* glue another loop segment can use *)


Theorem pf_seg_entry : pfs_entry SK B ARx Pm CTX0 PB FX.
Proof.
intros en HPRE KLX KLH.
pose proof HPRE as HPRE0.
destruct en as [ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran n most own].
unfold pf_pre in HPRE.
cbn [fe_ly fe_S fe_Hp fe_W fe_regs fe_mem fe_md fe_ch fe_d fe_v fe_D fe_F fe_Lam fe_peak fe_cnt fe_fail fe_ran fe_n
  fe_most fe_own] in HPRE.
destruct HPRE as ([HPRE [HROD [HTOP [HRAZ HFRM]]]] & HUNIV & HROOM & H10 & HFWIN & HV & HSAFE & HLED).
unfold pf_FIN, fe_FP.
cbn [fe_ly fe_S fe_Hp fe_W fe_regs fe_mem fe_md fe_ch fe_d fe_v fe_D fe_F fe_Lam fe_peak fe_cnt fe_fail fe_ran fe_n
  fe_most fe_own].
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pf_stk0 n) as [FS FS2]. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct (pf_entry B ARx LAWS TL Hobj ly S Hp W regs mem md ch n HPRE) as [HS SHOK].
pose proof (ajournal_x_init_WR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
  (STK_pj_free (PI := prh_img_A) n) d
  (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl D))
  ly S Hp W regs mem md ch HPRE HFWIN) as HJ.
assert (HPM : Pm mem -> Pm mem) by (intros h; exact h).
remember (pf_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pf_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n0 Hn; subst E; unfold pf_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (Hv64 : 0 <= v < 2 ^ 64).
{ destruct HV as [(-> & _) | (_ & Hvc & _ & (H4 & _))]; [lia | unfold YM05.alloc_ceiling in *; lia]. }
assert (U10 : U E (SOff 10 0) = v) by (apply (U_atom E 10 v); [rewrite E10, H10; reflexivity | exact Hv64]).
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_pf)) with (Z_to_bv 64 (BASE + AF_pf)).
(* ---- slots 0-13: the frame (ra, s0 .. s10), beqz a0 ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr regs Usp|].
gs_keep HFr Usp (spZ regs - 96) (spZ regs) KO1. clear HF. rename HG into HG1.
pose proof HFr as HFr1. clear HFr.
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
  by (rewrite HE; split; [intros n0 Hn; unfold pf_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
psrr_branch_tok RUN BR HS SHOK PF_Bspan.
- (* v = 0: the epilogue (slots 80-93) and the ret *)
  rewrite branch_eq_U, U_SLit, U10 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. clear U10. subst v.
  destruct HV as [(_ & -> & ->) | (Hn & _)]; [|lia].
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr regs Usp|].
  gs_keep HFr Usp (spZ regs - 96) (spZ regs) KO2. clear HF HG HFr.
  (* the ret keeps the world: its SRr step is lifted to SRr' *)
  apply (SRr_SRr' SEGS RZ_cf).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  prreg HS (1%bv : bv 5) G1. prreg HS (2%bv : bv 5) G2.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs [Z_to_bv 64 SHADOW_OFF]
    [3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAE0
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a) by (intros a Ha Hn; rewrite KO2 by lia; apply KO1; lia).
  unfold fpostWR.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?rr _ ?mm _) ?dd = _ /\ _ =>
    exists ly, S, Hp, rr, mm, dd end.
  eexists.
  split.
  { rewrite G1. rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl).
    unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS RZ_cf)); exact HJ|].
  split; [intros a Ha _; apply KM; lia|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G2. exact E2.
    - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
    - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
    - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
    - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
    - apply KR. cbn [In].
      assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
        by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        repeat (first [left; apply bv_eq; reflexivity | right]). }
  unfold pf_Q. cbn [fe_ly fe_S fe_Hp fe_W fe_regs fe_mem fe_md fe_ch fe_d fe_v fe_D fe_F fe_Lam fe_peak fe_cnt fe_fail
    fe_ran fe_n fe_most fe_own].
  split; [|exact HPM].
  split; [|apply pfr_refl].
  unfold pf_K0post.
  split; [exact HROOM|].
  exists Lam. split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
  split.
  { apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W (ms_mem ms0) Lam peak cnt fail ran most own HLED).
    - intros a Ha. pose proof (Hsegs a (pal_pst_img a Ha)). apply KM; [unfold kLowMemEnd in *; lia|].
      unfold kLowMemEnd, YM05.alloc_ceiling in *. lia.
    - intros a k0 i Hin Hi. change (@cf_head CP) with 16 in *.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED Hin) as (Hk0 & Hab & _).
      change (@cf_head CP) with 16 in *.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
      pose proof (req_size_pos (k0 + 16) ltac:(lia)) as Rq.
      apply KM; unfold YM05.alloc_ceiling in *; lia.
    - intros a k0 _ H. exact H.
    - apply Permutation_refl. }
  split; [intros _; split; [reflexivity | split; reflexivity]|].
  intros Hn; lia.
- (* v <> 0 *)
  rewrite branch_eq_U, U_SLit, U10 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc.
  destruct HV as [(Hv0 & _) | (_ & HCEIL & HFD & HSLOT)]; [contradiction|].
  destruct (pf_oshape _ _ _ _ _ _ HFD) as (HND & HAP & ty & num & str & kids & keys & nn & cap & ks & Ds & Dk & Dy & Di & Fi &
    HHDR & HDs & HDk & HDy & HPD & HFF & HI0 & HIS).
  pose proof HHDR as (HRW & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
  pose proof HSLOT as (H4096 & HAT & HRWs & HAMR & HWIN & HRA & HHU).
  assert (Hv47 : v + 56 <= YM05.alloc_ceiling).
  { destruct HAT as [(a0 & k0 & Hin & Ha0 & Hk0) | [(b & m & Hin & _ & Hb & Hm) | [(cid & pos & Hin & Hf & Hfm) | (Hs & _)]]].
    - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin) as (Hk & Hab & _).
      change (@cf_head CP) with 16 in *.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hcb & _).
      pose proof (req_size_pos (k0 + 16) ltac:(lia)). lia.
    - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & Hcb & _).
      pose proof (req_size_pos m ltac:(lia)). lia.
    - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hcb & _). lia.
    - unfold YM05.alloc_ceiling in *. lia. }
  assert (HRW8 : v mod 8 = 0) by (destruct HRWs as [H8 _]; exact H8).
  (* ---- the seat at slot 13 (AF_pf + 52) ---- *)
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs [Z_to_bv 64 SHADOW_OFF]
    [1%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAE0
    ltac:(vm_compute; reflexivity)) as KR1. cbn [ms_regs restrict] in KR1.
  assert (Sp1 : spZ (ms_regs ms) = spZ regs - 96).
  { unfold spZ at 1. rewrite Rsp, Usp. rewrite unsigned_lit_small by lia. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    pose proof (st_ok_region_nth SEGS E (abs_ss VAL ss) _ 0 _ HS eq_refl) as RG0 end.
  cbn [nth_error abs_ss ss_mem] in RG0.
  assert (VSL : forall od r, In (YP09.mkChunk od (CVal 8 (SOff (Z.to_nat (bv_unsigned r)) 0)))
      (YP09.r_chunks (YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0
        (map (fun c => YP09.mkChunk (fst c - 96) (CVal 8 (SOff (snd c) 0))) pf_saves1))) ->
    (Z.to_nat (bv_unsigned r) < 32)%nat ->
    val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
  { intros od r Hin Hr.
    pose proof (slot_of_region SEGS E _ (spZ regs) _ _ _ _ _ od (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (getr regs r))
      RG0 Usp) as V0.
    cbn [ms_mem restrict] in V0. apply V0.
    - vm_compute in Hin |- *. exact Hin.
    - cbn [sv_denot]. rewrite EL by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat regs _ _ r) by (rewrite Z2Nat.id by (apply bv_unsigned_in_range); reflexivity).
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - apply bv_unsigned_in_range. }
  assert (VF26 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 0) 8 (bv_unsigned (getr regs 26%bv)))
    by (replace (spZ regs - 96 + 0) with (spZ regs + (0 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF25 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 8) 8 (bv_unsigned (getr regs 25%bv)))
    by (replace (spZ regs - 96 + 8) with (spZ regs + (8 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF24 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 16) 8 (bv_unsigned (getr regs 24%bv)))
    by (replace (spZ regs - 96 + 16) with (spZ regs + (16 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF23 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 24) 8 (bv_unsigned (getr regs 23%bv)))
    by (replace (spZ regs - 96 + 24) with (spZ regs + (24 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF22 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 32) 8 (bv_unsigned (getr regs 22%bv)))
    by (replace (spZ regs - 96 + 32) with (spZ regs + (32 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF21 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 40) 8 (bv_unsigned (getr regs 21%bv)))
    by (replace (spZ regs - 96 + 40) with (spZ regs + (40 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF20 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 48) 8 (bv_unsigned (getr regs 20%bv)))
    by (replace (spZ regs - 96 + 48) with (spZ regs + (48 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF19 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 56) 8 (bv_unsigned (getr regs 19%bv)))
    by (replace (spZ regs - 96 + 56) with (spZ regs + (56 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF18 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 64) 8 (bv_unsigned (getr regs 18%bv)))
    by (replace (spZ regs - 96 + 64) with (spZ regs + (64 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF9 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 72) 8 (bv_unsigned (getr regs 9%bv)))
    by (replace (spZ regs - 96 + 72) with (spZ regs + (72 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 80) 8 (bv_unsigned (getr regs 8%bv)))
    by (replace (spZ regs - 96 + 80) with (spZ regs + (80 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  assert (VF1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + 88) 8 (bv_unsigned (getr regs 1%bv)))
    by (replace (spZ regs - 96 + 88) with (spZ regs + (88 - 96)) by lia; apply VSL; [vm_compute; tauto | vm_compute; lia]).
  (* v's node at the branch state: untouched (the frame is above alloc_ceiling) *)
  assert (KN1 : forall x, v <= x < v + 56 -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) x = mbyte SEGS (mrestrict (w_H W) mem) x).
  { intros x Hx. apply (mbyte_of_aview SEGS). apply KO1; [lia|]. unfold YM05.alloc_ceiling in *. lia. }
  assert (RD1 : forall o x, 0 <= o -> o + 8 <= 56 -> rd_u64 SEGS (mrestrict (w_H W) mem) (v + o) x ->
    rd_u64 SEGS (mrestrict (w_H W) (ms_mem ms)) (v + o) x)
    by (intros o x Ho Ho8 Hx; apply (rd_u64_frame SEGS _ _ _ _ Hx); intros y Hy; apply KN1; lia).
  pose proof (RD1 16 str ltac:(lia) ltac:(lia) Hstr) as Hstr1. pose proof (RD1 24 kids ltac:(lia) ltac:(lia) Hkids) as Hkids1.
  pose proof (RD1 32 keys ltac:(lia) ltac:(lia) Hkeys) as Hkeys1. pose proof (RD1 40 nn ltac:(lia) ltac:(lia) Hnn) as Hnn1.
  pose proof (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
  pose proof (pal_got_cell B TL) as HgcD.
  assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
  { intros i Hi. destruct (Hobj i Hi) as [Hg1 Hg2]. split; apply Hsegs; assumption. }
  assert (KG1 : forall a, 0 <= a < kLowMemEnd -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KO1; [unfold kLowMemEnd in *; lia | unfold kLowMemEnd, YM05.alloc_ceiling in *; lia]).
  assert (Kgot1 : rdword (aview SEGS (w_H W) (ms_mem ms)) (VAL (A_OBJ 0)) = Some (VAL (A_OBJ 12))).
  { rewrite <- Kgot. apply rdword_ext. intros i Hi. apply KG1. destruct (HgL i ltac:(lia)). lia. }
  assert (Kcell1 : rdword (aview SEGS (w_H W) (ms_mem ms)) (VAL (A_OBJ 12)) = Some SHADOW_OFF).
  { rewrite <- Kcell. apply rdword_ext. intros i Hi. apply KG1. destruct (HgL i ltac:(lia)). lia. }
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pc)) _ _) _) _ =>
    assert (EPC : pc = AF_pf + 52) by (vm_compute; reflexivity); rewrite EPC end.
  pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
  set (E1 := pf_E1 (ms_regs ms) [str; kids; keys; nn]).
  assert (EL1 : forall i, (i < A_TEXT)%nat -> ew E1 i = ew (Ereg (ms_regs ms) (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) [str; kids; keys; nn])) i)
    by (intros i Hi; subst E1; unfold pf_E1; apply Eimg_low; exact Hi).
  assert (EG1 : ew E1 1 = getr regs 1%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 1 1%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG3 : ew E1 3 = getr regs 3%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG4 : ew E1 4 = getr regs 4%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG8 : ew E1 8 = getr regs 8%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG9 : ew E1 9 = getr regs 9%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG10 : ew E1 10 = getr regs 10%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG18 : ew E1 18 = getr regs 18%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG19 : ew E1 19 = getr regs 19%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 19 19%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG20 : ew E1 20 = getr regs 20%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 20 20%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG21 : ew E1 21 = getr regs 21%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 21 21%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG22 : ew E1 22 = getr regs 22%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 22 22%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG23 : ew E1 23 = getr regs 23%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 23 23%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG24 : ew E1 24 = getr regs 24%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 24 24%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG25 : ew E1 25 = getr regs 25%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 25 25%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG26 : ew E1 26 = getr regs 26%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 26 26%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG27 : ew E1 27 = getr regs 27%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 27 27%bv eq_refl); apply KR1; cbn; tauto).
  assert (EG2 : ew E1 2 = getr (ms_regs ms) 2%bv)
    by (rewrite EL1 by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl)).
  assert (EX1 : forall j, (j < 5)%nat -> ew E1 (32 + j) = nth j (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) [str; kids; keys; nn]) (Z_to_bv 64 0)).
  { intros j Hj. rewrite EL1 by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. reflexivity. }
  assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs - 96) by (rewrite EG2; exact Sp1).
  assert (Uv1 : bv_unsigned (ew E1 10) = v) by (rewrite EG10, H10; unfold w64; apply unsigned_lit_small; lia).
  assert (Eo0 : ew E1 (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
    by (subst E1; unfold pf_E1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : ew E1 (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
    by (subst E1; unfold pf_E1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall i x, ew E1 i = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> base_val E1 (Some i) = x).
  { intros i x Hi Hx. cbn [base_val]. rewrite Hi. apply unsigned_lit_small. exact Hx. }
  destruct Hstr1 as (Rstr & Vstr). destruct Hkids1 as (Rkids & Vkids). destruct Hkeys1 as (Rkeys & Vkeys). destruct Hnn1 as (Rnn & Vnn).
  destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
  pose proof (pf_vplace B ARx LAWS _ ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSLOT HCEIL
    ltac:(lia)) as VPL.
  assert (DJ : forall o, (forall i, 0 <= i < 8 -> in_img SEGS (o + i)) -> o + 8 <= v \/ v + 56 <= o).
  { intros o Ho. destruct (Z_le_gt_dec (o + 8) v); [left; lia|]. destruct (Z_le_gt_dec (v + 56) o); [right; lia|].
    exfalso. destruct (Z_le_gt_dec v o).
    - pose proof (Ho 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact (proj2 (VPL o ltac:(lia)) H0).
    - apply (proj2 (VPL v ltac:(lia))). replace v with (o + (v - o)) by lia. apply Ho. lia. }
  assert (DJ0 : VAL (A_OBJ 0) + 8 <= v \/ v + 56 <= VAL (A_OBJ 0)) by (apply DJ; intros i Hi; exact (proj1 (Hobj i Hi))).
  assert (DJ12 : VAL (A_OBJ 12) + 8 <= v \/ v + 56 <= VAL (A_OBJ 12)) by (apply DJ; intros i Hi; exact (proj2 (Hobj i Hi))).
  assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; unfold pf_E1; apply Eimg_env).
  assert (HS1 : st_ok_pi SEGS VAL E1 ss_pf1
    (restrict (w_H W) (mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_pf + 52))) (ms_mem ms) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_pf1. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold pf_frame1, pf_node1, got_regionP, bcell_regionP, pf_saves1.
      cbn [map fst snd].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      + cbn [base_val]. rewrite Usp1. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 0 8 (SOff 26 0) (bv_unsigned (getr regs 26%bv)));
            [cbn [sv_denot]; rewrite EG26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF26].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 8 8 (SOff 25 0) (bv_unsigned (getr regs 25%bv)));
            [cbn [sv_denot]; rewrite EG25, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF25].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 16 8 (SOff 24 0) (bv_unsigned (getr regs 24%bv)));
            [cbn [sv_denot]; rewrite EG24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF24].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 24 8 (SOff 23 0) (bv_unsigned (getr regs 23%bv)));
            [cbn [sv_denot]; rewrite EG23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF23].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 32 8 (SOff 22 0) (bv_unsigned (getr regs 22%bv)));
            [cbn [sv_denot]; rewrite EG22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF22].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 40 8 (SOff 21 0) (bv_unsigned (getr regs 21%bv)));
            [cbn [sv_denot]; rewrite EG21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF21].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 48 8 (SOff 20 0) (bv_unsigned (getr regs 20%bv)));
            [cbn [sv_denot]; rewrite EG20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF20].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 56 8 (SOff 19 0) (bv_unsigned (getr regs 19%bv)));
            [cbn [sv_denot]; rewrite EG19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF19].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 64 8 (SOff 18 0) (bv_unsigned (getr regs 18%bv)));
            [cbn [sv_denot]; rewrite EG18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF18].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 72 8 (SOff 9 0) (bv_unsigned (getr regs 9%bv)));
            [cbn [sv_denot]; rewrite EG9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF9].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 80 8 (SOff 8 0) (bv_unsigned (getr regs 8%bv)));
            [cbn [sv_denot]; rewrite EG8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF8].
        * apply (chunk_ok_val SEGS E1 _ (spZ regs - 96) 88 8 (SOff 1 0) (bv_unsigned (getr regs 1%bv)));
            [cbn [sv_denot]; rewrite EG1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | apply bv_unsigned_in_range | lia | exact VF1].
      + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E1 _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) (ms_mem ms) _ _ Kgot1).
      + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E1 _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; change (ew E1 32) with (ew E1 (32 + 0)); rewrite (EX1 0%nat) by lia; cbn [nth];
           rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) (ms_mem ms) _ _ Kcell1).
      + cbn [base_val]. rewrite Uv1. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
        * apply (chunk_ok_val SEGS E1 _ v 16 8 (SOff 33 0) str);
            [cbn [sv_denot]; change (ew E1 33) with (ew E1 (32 + 1)); rewrite (EX1 1%nat) by lia; cbn [nth map];
               rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia | lia | exact Vstr].
        * apply (chunk_ok_val SEGS E1 _ v 24 8 (SOff 34 0) kids);
            [cbn [sv_denot]; change (ew E1 34) with (ew E1 (32 + 2)); rewrite (EX1 2%nat) by lia; cbn [nth map];
               rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia | lia | exact Vkids].
        * apply (chunk_ok_val SEGS E1 _ v 32 8 (SOff 35 0) keys);
            [cbn [sv_denot]; change (ew E1 35) with (ew E1 (32 + 3)); rewrite (EX1 3%nat) by lia; cbn [nth map];
               rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia | lia | exact Vkeys].
        * apply (chunk_ok_val SEGS E1 _ v 40 8 (SOff 36 0) nn);
            [cbn [sv_denot]; change (ew E1 36) with (ew E1 (32 + 4)); rewrite (EX1 4%nat) by lia; cbn [nth map];
               rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity | lia | lia | exact Vnn].
    - apply pairwise_disjoint_of_extents. unfold pf_frame1, pf_node1, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
      cbn [base_val]. rewrite Usp1, Uv1.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS FS2 Hes Hv47 H4096 DJ0 DJ12.
      unfold kLowMemEnd, YM05.alloc_ceiling. clear. intros.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - split; [|split; [exact I | exact I]].
      cbn [pf_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp1, Uv1. change 32%nat with (32 + 0)%nat. rewrite (EX1 0%nat) by lia. cbn [nth].
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; unfold YM05.alloc_ceiling in *; lia. }
  assert (SHOK1 : sh_ok SEGS PF_Bx PF_SH1 E1 (mrestrict (w_H W) (ms_mem ms))).
  { unfold sh_ok, PF_SH1. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (UB : U E1 PF_Bx = SHADOW_OFF).
    { unfold PF_Bx. apply (U_atom E1 32 SHADOW_OFF);
        [change 32%nat with (32 + 0)%nat; rewrite (EX1 0%nat) by lia; reflexivity | unfold SHADOW_OFF; lia]. }
    assert (UV : U E1 (SOff 10 0) = v) by (apply (U_atom E1 10 v); [rewrite EG10, H10; reflexivity | lia]).
    rewrite UB, UV. split.
    - replace (v + 0) with v by lia. replace (56 - 0) with 56 by lia.
      eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)).
      apply KO1; [unfold shadow_of_addr, SHADOW_OFF in *; lia | unfold YM05.alloc_ceiling in *; lia].
    - intros a Ha. unfold amem_range in HAMR. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  clear HS SHOK HEI.
  (* ---- slots 13-26: beqz a0 (v <> 0 by the fact on atom 10), s0 = v, the shadow base, the n word, beqz ---- *)
  paj_run_tok_x_inv RUN HS1 HJ SHOK1 HPM PF_Bspan; [gs_awr0|].
  gs_memeq HF EM2. clear HF HG HFr.
  pose (RUNTO := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
    (srr_inv_laws_imp SEGS Pm mem PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
  (* v's node record (pf_oshape's witnesses) and what both cuts take of the seat at slot 13 *)
  pose (nd := MkPfNode ty num str kids keys nn cap ks Ds Dk Dy Di Fi).
  assert (HNODE : pf_node (MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran n most own) nd).
  { unfold pf_node. cbn [nd fe_W fe_mem fe_Lam fe_D fe_v fe_F fe_n fn_ty fn_num fn_str fn_kids fn_keys fn_n fn_cap fn_ks
      fn_Ds fn_Dk fn_Dy fn_Di fn_Fi fn_own].
    split; [exact HND|]. split; [exact HAP|]. split; [exact HHDR|]. split; [exact HDs|].
    split; [exact HDk|]. split; [exact HDy|]. split; [exact HPD|]. split; [exact HFF|].
    destruct n as [|d']; [exact (HI0 eq_refl) | exact (HIS d' eq_refl)]. }
  assert (E36 : ew E1 36 = Z_to_bv 64 nn)
    by (change (ew E1 36) with (ew E1 (32 + 4)); rewrite (EX1 4%nat) by lia; reflexivity).
  assert (E32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF)
    by (change (ew E1 32) with (ew E1 (32 + 0)); rewrite (EX1 0%nat) by lia; reflexivity).
  assert (E10v : ew E1 10 = Z_to_bv 64 v) by (rewrite EG10, H10; reflexivity).
  assert (HAE1 : env_agree 32 (Ereg (ms_regs ms) (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) [str; kids; keys; nn])) E1)
    by (split; [intros n0 Hn0; exact (EL1 n0 ltac:(unfold A_TEXT; lia)) | reflexivity]).
  assert (HSV : forall o r, In (o, r) pf_saves1 ->
    val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 96 + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))).
  { intros o r Hro. replace (spZ regs - 96 + o) with (spZ regs + (o - 96)) by lia.
    unfold pf_saves1 in Hro.
    repeat (destruct Hro as [Hro | Hro]; [injection Hro as <- <-; apply VSL; [vm_compute; tauto | vm_compute; lia] |]).
    destruct Hro. }
  rename Hc into Hvne.
  psrr_branch_tok RUN BR HS1 SHOK1 PF_Bspan.
  + (* beqz taken: n = 0, no slot; to the cut after the loop (offset 228) *)
    rewrite branch_eq_U, U_SLit, (U_atom E1 36 nn E36 Rnn) in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_eq in Hc.
    assert (HDF : Di = [] /\ Fi = []).
    { destruct n as [|d'].
      - destruct (HI0 eq_refl) as (_ & HDi & HFi). exact (conj HDi HFi).
      - pose proof (HIS d' eq_refl) as Hit. rewrite Hc in Hit. exact Hit. }
    destruct HDF as [EDi EFi].
    paj_run_to_tok_x_inv RUNTO HS1 HJ SHOK1 HPM PF_Bspan (AF_pf + PF_LX).
    all: try gs_awr0.
    gs_memeq HF EM3. clear HF HG HFr.
    repeat rewrite wvb_collapse in HJ.
    lazymatch type of HS1 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into msX end.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E1 _ _ (ms_regs ms) _ [2%bv; 3%bv; 4%bv; 27%bv] HS1 HAE1
      ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hn; rewrite EM3, EM2; exact (KO1 a Ha Hn)).
    assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msX)))
      by (intros x Hx; rewrite EM3, EM2; exact (HG1 x Hx)).
    assert (HSVq : forall o r, In (o, r) pf_saves1 -> val_mem SEGS (mrestrict (w_H W) (ms_mem msX)) (spZ regs - 96 + o) 8
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))) by (intros o r Hro; rewrite EM3, EM2; exact (HSV o r Hro)).
    assert (Sp2 : spZ (ms_regs msX) = spZ regs - 96)
      by (unfold spZ at 1; rewrite (KR2 2%bv) by (cbn; tauto); exact Sp1).
    assert (G3 : getr (ms_regs msX) 3 = getr regs 3) by (rewrite (KR2 3%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    assert (G4 : getr (ms_regs msX) 4 = getr regs 4) by (rewrite (KR2 4%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    assert (G27 : getr (ms_regs msX) 27 = getr regs 27) by (rewrite (KR2 27%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    pfa_reg HS1 (8%bv : bv 5) R8. pfa_reg HS1 (9%bv : bv 5) R9. pfa_reg HS1 (18%bv : bv 5) R18.
    pfa_reg HS1 (19%bv : bv 5) R19. pfa_reg HS1 (20%bv : bv 5) R20. pfa_reg HS1 (21%bv : bv 5) R21.
    pmkst HS1.
    lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pc)) _ _) _) _ =>
      assert (EPX : pc = AF_pf + PF_LX) by (vm_compute; reflexivity); rewrite EPX end.
    apply (KLX nd ly S Hp W (ms_regs msX) (ms_mem msX) _ 0 HNODE).
    unfold pf_LX.
    split; [exact (pfe_frame_ok (wle' SEGS RZ_cf) _ (ms_regs msX) (ms_mem msX) _ HPRE0 HJ KALL Sp2 HSVq G3 G4 G27 HPM)|].
    split.
    { unfold pf_vregs. cbn [fe_v]. unfold w64.
      split; [rewrite R8, denot_lit_U, (U_atom E1 10 v E10v Hv64); reflexivity|].
      split; [rewrite R9, denot_lit_U, (U_atom_off E1 10 v 32 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R18, denot_lit_U, (U_atom_off E1 10 v 40 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R19, denot_lit_U, (U_atom_off E1 10 v 24 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R20, denot_lit_U, (U_atom E1 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia); reflexivity|].
      rewrite R21, denot_lit_U, (pfe_U_cell E1 10 32 v 40 E10v E32) by lia; reflexivity. }
    exists [], Lam. split.
    { split; [exact HROOM|].
      split; [exact (pfe_ledger_ok _ (ms_mem msX) HPRE0 KALL)|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
      cbn [fe_F fe_ly fe_S nd fn_own fn_Dk fn_Dy fn_Ds app]. rewrite HFF, EFi. cbn [app].
      split; [reflexivity | apply pfr_refl]. }
    split; [exact (pfe_vnode_ok _ nd (ms_mem msX) HPRE0 HNODE Hvne Hv47 KALL MG)|].
    rewrite EDi in HPD. exact (pfe_perm _ _ _ _ _ HPD).
  + (* beqz not taken: n <> 0; s6 = s7 = s8 = 0, s9 / s10 := the cells of v+24 / v+32; to the loop head at slot 0
       (offset 136) *)
    rewrite branch_eq_U, U_SLit, (U_atom E1 36 nn E36 Rnn) in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
    apply Z.eqb_neq in Hc.
    assert (Hd' : exists d', n = Datatypes.S d').
    { destruct n as [|d']; [exfalso; exact (Hc (proj1 (HI0 eq_refl))) | exists d'; reflexivity]. }
    destruct Hd' as [d' En].
    paj_run_to_tok_x_inv RUNTO HS1 HJ SHOK1 HPM PF_Bspan (AF_pf + PF_LH).
    all: try gs_awr0.
    gs_memeq HF EM3. clear HF HG HFr.
    repeat rewrite wvb_collapse in HJ.
    lazymatch type of HS1 with st_ok_pi _ _ _ _ (restrict _ ?msq) => rename msq into msX end.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E1 _ _ (ms_regs ms) _ [2%bv; 3%bv; 4%bv; 27%bv] HS1 HAE1
      ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem a)
      by (intros a Ha Hn; rewrite EM3, EM2; exact (KO1 a Ha Hn)).
    assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem msX)))
      by (intros x Hx; rewrite EM3, EM2; exact (HG1 x Hx)).
    assert (HSVq : forall o r, In (o, r) pf_saves1 -> val_mem SEGS (mrestrict (w_H W) (ms_mem msX)) (spZ regs - 96 + o) 8
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r))))) by (intros o r Hro; rewrite EM3, EM2; exact (HSV o r Hro)).
    assert (Sp2 : spZ (ms_regs msX) = spZ regs - 96)
      by (unfold spZ at 1; rewrite (KR2 2%bv) by (cbn; tauto); exact Sp1).
    assert (G3 : getr (ms_regs msX) 3 = getr regs 3) by (rewrite (KR2 3%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    assert (G4 : getr (ms_regs msX) 4 = getr regs 4) by (rewrite (KR2 4%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    assert (G27 : getr (ms_regs msX) 27 = getr regs 27) by (rewrite (KR2 27%bv) by (cbn; tauto); apply KR1; cbn; tauto).
    pfa_reg HS1 (8%bv : bv 5) R8. pfa_reg HS1 (9%bv : bv 5) R9. pfa_reg HS1 (18%bv : bv 5) R18.
    pfa_reg HS1 (19%bv : bv 5) R19. pfa_reg HS1 (20%bv : bv 5) R20. pfa_reg HS1 (21%bv : bv 5) R21.
    pfa_reg HS1 (22%bv : bv 5) R22. pfa_reg HS1 (23%bv : bv 5) R23. pfa_reg HS1 (24%bv : bv 5) R24.
    pfa_reg HS1 (25%bv : bv 5) R25. pfa_reg HS1 (26%bv : bv 5) R26.
    pmkst HS1.
    lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pc)) _ _) _) _ =>
      assert (EPH : pc = AF_pf + PF_LH) by (vm_compute; reflexivity); rewrite EPH end.
    apply (KLH nd d' ly S Hp W (ms_regs msX) (ms_mem msX) _ 0 HNODE).
    unfold pf_LH.
    split; [exact En|].
    split; [cbn [nd fn_n]; lia|].
    split; [exact (pfe_frame_ok (wle' SEGS RZ_cf) _ (ms_regs msX) (ms_mem msX) _ HPRE0 HJ KALL Sp2 HSVq G3 G4 G27 HPM)|].
    split.
    { unfold pf_vregs. cbn [fe_v]. unfold w64.
      split; [rewrite R8, denot_lit_U, (U_atom E1 10 v E10v Hv64); reflexivity|].
      split; [rewrite R9, denot_lit_U, (U_atom_off E1 10 v 32 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R18, denot_lit_U, (U_atom_off E1 10 v 40 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R19, denot_lit_U, (U_atom_off E1 10 v 24 E10v Hv64) by lia; reflexivity|].
      split; [rewrite R20, denot_lit_U, (U_atom E1 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia); reflexivity|].
      rewrite R21, denot_lit_U, (pfe_U_cell E1 10 32 v 40 E10v E32) by lia; reflexivity. }
    split.
    { unfold pf_lregs. cbn [fe_v]. unfold w64.
      split; [rewrite R22, denot_lit_U, U_SLit; reflexivity|].
      split; [rewrite R23, denot_lit_U, U_SLit; reflexivity|].
      split; [rewrite R24, denot_lit_U, U_SLit; reflexivity|].
      split; [rewrite R25, denot_lit_U, (pfe_U_cell E1 10 32 v 24 E10v E32) by lia; reflexivity|].
      rewrite R26, denot_lit_U, (pfe_U_cell E1 10 32 v 32 E10v E32) by lia; reflexivity. }
    exists [], Lam, Di, Fi. split.
    { split; [exact HROOM|].
      split; [exact (pfe_ledger_ok _ (ms_mem msX) HPRE0 KALL)|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
      cbn [fe_F fe_ly fe_S nd fn_own fn_Dk fn_Dy fn_Ds app]. rewrite HFF.
      split; [reflexivity | apply pfr_refl]. }
    split; [exact (pfe_vnode_ok _ nd (ms_mem msX) HPRE0 HNODE Hvne Hv47 KALL MG)|].
    split; [exact (pfe_perm _ _ _ _ _ HPD)|].
    exact (pfe_items_ok _ nd d' (ms_mem msX) HPRE0 HNODE En KALL MG).
Qed.

End e.
End d.

Print Assumptions pf_seg_entry.
