(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_seg_loop.v, with its module paths, module names and numbers changed; 305 of its 480 lines of code are new or changed and 324 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk (lib/A/Prog/S6PjFree.v), the LOOP HEAD segment.
   rule 24: proves no function (kind: segment lemma of pj_free's walk).
   pf_seg_LH (pfs_LH d'): from the cut pf_LH at slot i (AF_pf + 136, slot 34 of pj_free) to the return site of the
   recursive call pf_LK (AF_pf + 156, slot 39), the continuation at pf_LK a premise:
     +136 lbu a0, 0(s9); +140 bnez a0   the ASan check of v + 24 (decided: shadow entry mkSHE 8 0 56, s9 = its cell)
     +144 ld a0, 0(s3)                  kids (v's header chunk 24, atom 33)
     +148 add a0, a0, s6                a0 = kids + 56 i
     +152 jal pj_free                   the RECURSIVE CALL, by the depth-d' text tpj_free_specOP .. d' (a PREMISE of
                                        the lemma, never this file's claim): at the callee window e1 = 0 (YCbqGcallW.v
                                        aj_call_xW), v' = kids + 56 i (never 0: slot i of the kids block), D1 / F1 =
                                        slot i's subtree (pf_oitemsR's head), Lam = the current ledger, the slot in the
                                        kids block (prhReader_at's first place), PB along F1 from pf_pre's pf_safe and
                                        pf_acct's pf_reach (pf_safe_after, pf_safe_prefix; pf_pre's pf_safe under
                                        fe_v en <> 0), fpre's raZ bound from the return slot (closed slot lemma
                                        pflh_slot_lk, PRW_StepKit.v pa_slot_lt_ceil_b), fpre's frm_zero from the
                                        caller's own fpre (same fx).
   After the call (S6PjFreeKeep.v): the accounts (pfk_acct_rec, order Fd ++ F1), v's node (pfk_vnode), the slots
   i + 1 .. n - 1 (pfk_items), slot i's key (PjFreeCommon.v pfk_hblk), the frame (pfk_frame); the callee-saved
   registers by the post's aregs_preserved. Image B's lib/B/Prog/pj_free_seg_loop.v (h-rw-pre-5 s6/ref7) is the model.
   Section hypotheses: AR_laws_x at cf_head (LAWS); YGcfFsVis.ARx_frame_hull_vis (VISF, a MARKED kit fact the instance
   discharges by ARx_frame_hull_vis_cf_ok); pal_pst_ro (image fact, discharged at PI_prog_A by S1ImgA.v pst_not_ro_A);
   the memory invariant's laws srr_inv_laws (PLAW). Texts S6PjFreeKeep.v / S6PjFree.v uses verbatim.
   GLUE another loop segment can use: pflh_sregs / ss_pflh / pflh_seat (the loop seat: pft's seat
   with s9 / s10 the cells of v + 24 / v + 32), (pfa_lam_blk B ARx LAWS), (pfa_hb_vis B ARx LAWS), (pfa_hb_apart B ARx LAWS), (pfa_v_apart B ARx LAWS),
   (pfa_frame_same SK B ARx Pm), the NoDup / footprint bookkeeping pflh_nd_* / pfa_lam_now / pfa_inFP_hbl*.
   Numerals: 136 / 156 (DERIVED: S6PjFree.v PF_LH / PF_LK), 20384 (DERIVED: AF_pf + PF_LK by computation, pflh_af_lk;
   the engine's return value SOff 240 20384 at atom 240 = A_TEXT), 96 (LENGTH: pj_free's frame), 56 / 8 / 24 / 32 / 40
   (LENGTH: struct pj, its fields, a slot), 16 (cf_head at CfParams_preset). No ADDRESS.
   THE RE-HIDING MOVE: the recursive pj_free crosses frees, so the segment concludes SRr' SEGS RZ_cf (YA0nH) and runs
   over R := wle' SEGS RZ_cf: the _invR runner (YC1fPx), the call by YCbqGcallW.aj_call_xWR with the depth-d' text at
   SRr' / fpostWR (wle' ..), the frame's journal at wle' (pf_LH / pf_LK), and what the call keeps by the R forms
   (pfa_frame_sameR, pfk_frameR, pfk_vnodeR, pfk_itemsR, PjFreeCommon.pfk_hblkR). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure S6PjFree S6PjFreeKeep S6PjFreeGlue.
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

(* ---- the loop seat (glue another loop segment can use): S6PjFree.v's tail seat ss_pft with s9 / s10 the ASan cells of v + 24 / v + 32
   (pf_lregs), so the engine decides the loop's checks of kids / keys by the shadow entry of v's 56 bytes ---- *)
Definition pflh_sregs : list sv :=
  Eval vm_compute in sr_set (sr_set pft_sregs 25%bv (pft_cell (SOff 8 24))) 26%bv (pft_cell (SOff 8 32)).
Lemma pflh_sregs_eq : pflh_sregs = sr_set (sr_set pft_sregs 25%bv (pft_cell (SOff 8 24))) 26%bv (pft_cell (SOff 8 32)).
Proof. vm_compute. reflexivity. Qed.
Definition ss_pflh (pc : Z) : sstate := mkSS pc pflh_sregs [pft_vhdr] None pft_facts.

(* the recursive call's return slot: its offset, and that it is a slot of the listing (CLOSED goals) *)
Lemma pflh_af_lk : AF_pf + PF_LK = 20384.
Proof. vm_compute. reflexivity. Qed.
Lemma pflh_slot_lk : match plookup (@pl_tpi _ PL_prog_A) (AF_pf + PF_LK) with Some _ => true | None => false end = true.
Proof. vm_compute. reflexivity. Qed.




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


(* ---- seating the loop's symbolic state at any pc of the loop (glue another loop segment can use) ---- *)
Lemma pflh_seat : forall en nd i (W : world SEGS) regs mem pc,
  pf_vregs en regs -> pf_lregs en regs i -> 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= fe_v en <= 2 ^ 47 - 64 -> fe_v en mod 8 = 0 ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 16) (fn_str nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 24) (fn_kids nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 32) (fn_keys nd) ->
  rd_u64 SEGS (mrestrict (w_H W) mem) (fe_v en + 40) (fn_n nd) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fe_v en) 56 -> amem_range (fe_v en) 56 ->
  st_ok_pi SEGS VAL (PFT_E regs nd) (ss_pflh pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PFT_Bx PFT_SH (PFT_E regs nd) (mrestrict (w_H W) mem).
Proof.
intros en nd i W regs mem pc HVR HLR Hsp Hal Hv Hv8 Hstr Hkids Hkeys Hnn Hra Hamr.
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HLR as (R22 & R23 & R24 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v := fe_v en) in *.
set (E := PFT_E regs nd).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = v + c).
{ intros c Hc. apply (U_atom_off E 8 v c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply (U_atom E 20 SHADOW_OFF); [rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]); exact R20 | unfold SHADOW_OFF; lia]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Er 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v).
{ rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]). rewrite R8. apply unsigned_lit_small. lia. }
assert (DU : forall e, sv_denot E e = Z_to_bv 64 (U E e)) by (intros e; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hcell : forall c, 0 <= c <= 56 -> U E (pft_cell (SOff 8 c)) = (v + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pft_cell. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
  replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite U8 by lia. rewrite U20.
  assert (Hq : 0 <= (v + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  unfold zcanon, M64, SHADOW_OFF in *. apply Z.mod_small. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_pflh. apply pa_entry_st_ok_full.
  + rewrite pflh_sregs_eq.
    apply regs_ok_pin; [|pft_regne|rewrite R26, DU, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R25, DU, Hcell by lia; reflexivity].
    rewrite pft_sregs_eq.
    apply regs_ok_pin; [|pft_regne|rewrite R21, DU, Hcell by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R19, DU, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R18, DU, U8 by lia; reflexivity].
    apply regs_ok_pin; [|pft_regne|rewrite R9, DU, U8 by lia; reflexivity].
    unfold E, PFT_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pft_vhdr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 32 0) (fn_str nd));
        [rewrite DU, (U_atom E 32 (fn_str nd)); [reflexivity | exact (EX 0%nat ltac:(lia)) | exact (proj1 Hstr)]
        | cbn; exact (proj1 Hstr) | cbn; lia | exact (proj2 Hstr)].
    * apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 33 0) (fn_kids nd));
        [rewrite DU, (U_atom E 33 (fn_kids nd)); [reflexivity | exact (EX 1%nat ltac:(lia)) | exact (proj1 Hkids)]
        | cbn; exact (proj1 Hkids) | cbn; lia | exact (proj2 Hkids)].
    * apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 34 0) (fn_keys nd));
        [rewrite DU, (U_atom E 34 (fn_keys nd)); [reflexivity | exact (EX 2%nat ltac:(lia)) | exact (proj1 Hkeys)]
        | cbn; exact (proj1 Hkeys) | cbn; lia | exact (proj2 Hkeys)].
    * apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 35 0) (fn_n nd));
        [rewrite DU, (U_atom E 35 (fn_n nd)); [reflexivity | exact (EX 3%nat ltac:(lia)) | exact (proj1 Hnn)]
        | cbn; exact (proj1 Hnn) | cbn; lia | exact (proj2 Hnn)].
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    unfold pft_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uv. rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]). rewrite R20. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal; try exact Hv8; try lia.
- unfold sh_ok, PFT_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E PFT_Bx 8 v 56 v 0 56 Hra).
  + unfold PFT_Bx. exact U20.
  + rewrite U8 by lia. lia.
  + lia. + lia.
  + intros x Hx. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia.
Qed.

Section e.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis VISF : YGcfFsVis.ARx_frame_hull_vis SEGS B ARx.
(* image fact, discharged at PI_prog_A by S1ImgA.v pst_not_ro_A: alloc.c's statics are no read-only bytes *)
Hypothesis pal_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Variable CTX0 : list (list Z).
Variable PB : astate -> Prop.
Variable FX : pf_obs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).






(* ======== THE LOOP HEAD SEGMENT ======== *)
Theorem pf_seg_LH : forall d', tpj_free_specOP (PA := PA) B ARx SK Pm PB FX CTX0 d' ->
  pfs_LH SK B ARx Pm CTX0 PB FX d'.
Proof.
intros d' IH en nd i ly S Hp W regs mem md k HPRE HND Hvne HLH KLK.
pose proof HLH as (En & Hi & HFR & HVR & HLR & Fd & Lam & Dr & Fr & HAC & HVN & HPD & HIT).
pose proof HFR as (HJ & HWINF & Hsp & HSV & HPRES & G3 & G4 & G27 & HROD & HPM).
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HLR as (R22 & R23 & R24 & R25 & R26).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HAC as (HROOM & HLED & HPL & HPA & HFF & HRC).
pose proof HPRE as (HFPRE0 & HUNIV & HROOM0 & H100 & HWIN0 & HCASE0 & HSAFE & HLED0).
pose proof HFPRE0 as (HAFN0 & HROD0 & HSTKHI0 & HRAZ0 & HFRM0).
pose proof HAFN0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HND as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk d') as ESTK. rewrite <- En in ESTK.
pose proof (pf_stk0 d') as [FS FS2].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* ---- the kids block: it holds the n slots ---- *)
destruct HKIDSn as [(_ & Hn0 & _) | (kk & Hkkin & Hkkn & HDk)]; [lia|].
change (In (fn_kids nd, kk) (fe_Lam en)) in Hkkin.
(* ---- slot i: its key Dk, its subtree D1 / F1, the slots after it ---- *)
replace (Z.to_nat (fn_n nd - i)) with (Datatypes.S (Z.to_nat (fn_n nd - (i + 1)))) in HIT by lia.
destruct HIT as (Dk & D1 & F1 & D2 & F2 & EDr & EFr & HKEY & HFO1 & HIT2).
subst Dr Fr.
replace (fn_kids nd + 56 * i + 56) with (fn_kids nd + 56 * (i + 1)) in HIT2 by lia.
replace (fn_keys nd + 8 * i + 8) with (fn_keys nd + 8 * (i + 1)) in HIT2 by lia.
set (v' := fn_kids nd + 56 * i) in *.
assert (Ev' : v' = fn_kids nd + 56 * i) by reflexivity. clearbody v'.
assert (ND : NoDup (Fd ++ (Dk ++ D1 ++ D2) ++ fn_own nd)) by exact (pfa_nd_perm _ _ HPD HNDD).
assert (Hown_k : In (fn_kids nd, kk) (fn_own nd)) by (unfold fn_own; rewrite HDk; left; reflexivity).
assert (HkLam : In (fn_kids nd, kk) Lam).
{ apply (pfa_lam_now (fe_Lam en) Fd Lam _ HPL Hkkin). intros Hf.
  apply (pfa_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_k. }
assert (Hk_notD1 : ~ In (fn_kids nd, kk) D1).
{ intros H1. apply (pfa_nd_app (Dk ++ D1 ++ D2) (fn_own nd) (fn_kids nd, kk) (pfa_ndr _ _ ND));
  [apply in_or_app; right; apply in_or_app; left; exact H1 | exact Hown_k]. }
assert (HinD : forall b, In b (Fd ++ (Dk ++ D1 ++ D2) ++ fn_own nd) -> In b (fe_D en))
  by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPD) Hb)).
assert (Hk_inD : In (fn_kids nd, kk) (fe_D en)) by (apply HinD; apply in_or_app; right; apply in_or_app; right; exact Hown_k).
assert (HD1D : forall b, In b D1 -> In b (fe_D en)).
{ intros b Hb. apply HinD. apply in_or_app; right; apply in_or_app; left; apply in_or_app; right;
  apply in_or_app; left; exact Hb. }
assert (HFD1 : pj_fdR SEGS (rdW W mem) (prh_lin Lam) d' v' D1 /\ Permutation F1 D1)
  by exact (pj_foR_fdR SEGS _ _ _ _ _ _ HFO1).
assert (HD1L : forall a k0, In (a, k0) D1 -> In (a, k0) Lam)
  by (intros a k0 H; exact (pj_foR_lblk SEGS _ _ _ _ _ _ HFO1 a k0 H)).
assert (Hv'rw : pj_rwR SEGS (rdW W mem) v').
{ destruct d' as [|d'']; cbn [pj_foR] in HFO1;
  destruct HFO1 as (_ & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk' & Dy & Di & Fi & Hhdr & _);
  exact (proj1 Hhdr). }
destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ _ _ HAR HLED HkLam) as (Hkk0 & Hkka & Hkkc & Hkk16 & Hkab & Hkhp).
change (@cf_head CP) with 16 in Hkka, Hkab, Hkhp.
pose proof (req_size_pos (kk + 16) ltac:(lia)) as [_ Hkreq].
assert (Hi42 : 0 <= i < 2 ^ 42) by lia.
destruct ((pfa_hb_vis B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ (fn_kids nd) kk v' 56 HAR HLED HkLam ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hv'ra & Hv'hull & Hv'amr & Hv'own).
(* the order along F1: PB at every state the child reaches *)
assert (HSAFE1 : pf_safe FX PB F1 ly S).
{ pose proof (pf_safe_after FX PB _ _ _ _ _ _ (HSAFE Hvne) HRC) as H.
  rewrite <- !app_assoc in H. exact (pf_safe_prefix FX PB F1 _ ly S H). }
(* ---- +136 .. +152: the engine to the recursive call ---- *)
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite Hsp; lia).
assert (Hal : spZ regs mod 16 = 0) by (rewrite Hsp; revert S16; clear; intros; lia).
destruct (pflh_seat en nd i W regs mem (AF_pf + PF_LH) HVR HLR Hspr Hal ltac:(lia) Hv8 Hstr Hkids Hkeys Hnn Hvra Hamr)
  as [HS SHOK].
set (E := PFT_E regs nd) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, PFT_E; apply Eimg_env).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (DU : forall e, sv_denot E e = Z_to_bv 64 (U E e)) by (intros e; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
assert (EV : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> sv_denot E (SOff n0 0) = getr regs r).
{ intros n0 r Hn Hr. rewrite DU. rewrite (U_atom E n0 (bv_unsigned (getr regs r))).
  - apply Z_to_bv_bv_unsigned.
  - rewrite (Er n0 r Hn Hr). symmetry. apply Z_to_bv_bv_unsigned.
  - apply bv_unsigned_in_range. }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = fe_v en + c).
{ intros c Hc. apply (U_atom_off E 8 (fe_v en) c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply (U_atom E 20 SHADOW_OFF); [rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]); exact R20 | unfold SHADOW_OFF; lia]. }
assert (U22 : U E (SOff 22 0) = 56 * i).
{ apply (U_atom E 22 (56 * i)); [rewrite (Er 22%nat 22%bv) by (first [lia | reflexivity]); exact R22 | lia]. }
assert (Ukids : U E (SOff 33 0) = fn_kids nd).
{ pose proof (EX 1%nat ltac:(lia)) as X1. change (32 + 1)%nat with 33%nat in X1. cbn [nth] in X1.
  apply (U_atom E 33 (fn_kids nd)); [exact X1 | exact (proj1 Hkids)]. }
assert (Hcell : forall c, 0 <= c <= 56 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 c) (SLit 3)) (SOff 20 0)) = (fe_v en + c) / 8 + SHADOW_OFF).
{ intros c Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
  replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite U8 by lia. rewrite U20.
  assert (Hq : 0 <= (fe_v en + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (zcanon_id ((fe_v en + c) / 8)) by (unfold M64; lia).
  unfold zcanon, M64, SHADOW_OFF in *. apply Z.mod_small. lia. }
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
(* the stretch writes nothing *)
gs_memeq HF HMEQ. clear HF HFr HG.
(* ---- the call state's registers ---- *)
pfa_reg HS (1%bv : bv 5) Q1. pfa_reg HS (2%bv : bv 5) Q2. pfa_reg HS (3%bv : bv 5) Q3.
pfa_reg HS (4%bv : bv 5) Q4. pfa_reg HS (8%bv : bv 5) Q8. pfa_reg HS (9%bv : bv 5) Q9.
pfa_reg HS (10%bv : bv 5) Q10. pfa_reg HS (18%bv : bv 5) Q18. pfa_reg HS (19%bv : bv 5) Q19.
pfa_reg HS (20%bv : bv 5) Q20. pfa_reg HS (21%bv : bv 5) Q21. pfa_reg HS (22%bv : bv 5) Q22.
pfa_reg HS (23%bv : bv 5) Q23. pfa_reg HS (24%bv : bv 5) Q24. pfa_reg HS (25%bv : bv 5) Q25.
pfa_reg HS (26%bv : bv 5) Q26. pfa_reg HS (27%bv : bv 5) Q27.
rewrite (EV 2%nat 2%bv) in Q2 by (first [lia | reflexivity]).
rewrite (EV 3%nat 3%bv) in Q3 by (first [lia | reflexivity]).
rewrite (EV 4%nat 4%bv) in Q4 by (first [lia | reflexivity]).
rewrite (EV 8%nat 8%bv) in Q8 by (first [lia | reflexivity]).
rewrite (EV 20%nat 20%bv) in Q20 by (first [lia | reflexivity]).
rewrite (EV 22%nat 22%bv) in Q22 by (first [lia | reflexivity]).
rewrite (EV 23%nat 23%bv) in Q23 by (first [lia | reflexivity]).
rewrite (EV 24%nat 24%bv) in Q24 by (first [lia | reflexivity]).
rewrite (EV 27%nat 27%bv) in Q27 by (first [lia | reflexivity]).
rewrite DU, U8 in Q9 by lia. rewrite DU, U8 in Q18 by lia. rewrite DU, U8 in Q19 by lia.
rewrite DU, Hcell in Q21 by lia. rewrite DU, Hcell in Q25 by lia. rewrite DU, Hcell in Q26 by lia.
rewrite DU, pfa_U_add, U22, Ukids in Q10. rewrite Z.mod_small in Q10 by lia.
pose proof (@pa_B_ok _ _ PA) as HB.
assert (ET : ew E A_TEXT = Z_to_bv 64 BASE) by (unfold E, PFT_E; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
change (SOff 240 20384) with (SOff A_TEXT 20384) in Q1.
rewrite DU, (U_atom_off E A_TEXT BASE 20384 ET ltac:(lia) ltac:(lia)) in Q1.
pmkst HS. rewrite HMEQ in HJ, HPM |- *.
lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsc := r) in *; set (mdc := m) in * end.
pose proof (ajxR_ar HJ) as HARc.
(* ---- the call's premises ---- *)
assert (HSPC : spZ regsc = fe_sp0 en - 96) by (unfold spZ at 1; rewrite Q2; exact Hsp).
assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite Q3, G3; exact Hgp0).
assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite Q4, G4; exact Htp0).
assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (AF_pf + PF_LK))) by (rewrite Q1, pflh_af_lk; reflexivity).
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (AF_pf + PF_LK))))
  by (rewrite pflh_af_lk; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (AF_pf + PF_LK))))
  by (rewrite pflh_af_lk, unsigned_lit_small by lia; lia).
(* fpre's raZ bound: the return pc is a listing slot (closed slot lemma pflh_slot_lk) *)
assert (HRAZ1 : raZ regsc < YM05.alloc_ceiling).
{ unfold raZ. rewrite HRA1. rewrite unsigned_lit_small by (rewrite pflh_af_lk; lia).
  apply (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA)); [rewrite pflh_af_lk; lia | exact pflh_slot_lk]. }
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold s0Z. rewrite Q8, R8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HSTKHI1 : spZ regsc + 64 <= ly_stk_hi ly) by (rewrite HSPC, Eshi; unfold fe_sp0; lia).
assert (HSPO : spZ regsc = fe_sp0 en + fe_d en + (-96 - fe_d en)) by (rewrite HSPC; lia).
assert (Hal' : (-96 - fe_d en) mod 16 = 0) by (revert Hd16; clear; intros; lia).
assert (Hneg : -96 - fe_d en <= 0) by lia.
assert (HSTKF : 0 <= STK_pj_free d') by lia.
assert (Hbud : STK_pj_free d' - (-96 - fe_d en) <= STK_pj_free (fe_n en) + fe_d en) by lia.
assert (He0 : 0 <= 0) by lia.
assert (Hetop : -96 - fe_d en + 0 <= 0) by lia.
assert (HA10 : getr regsc 10 = w64 v') by (rewrite Q10; unfold w64; rewrite Ev'; f_equal; lia).
assert (Hv'n0 : v' <> 0) by lia.
assert (Hv'ceil : v' < YM05.alloc_ceiling) by lia.
(* the child's slot: in the kids block *)
assert (HSLOT : prhPj_slot (PA := PA) B (STK_pj_free d') 0 ly S Lam W regsc mem v').
{ split; [lia|]. split; [left; exists (fn_kids nd), kk; split; [exact HkLam | lia]|].
  split; [exact Hv'rw|]. split; [exact Hv'amr|].
  split; [intros a Ha; split; [exact (Hv'own a Ha) | rewrite HSPC; lia]|].
  split; [exact Hv'ra | exact Hv'hull]. }
assert (Hv'ne : (v' =? 0) = false) by (apply Z.eqb_neq; lia).
set (FP1 := if v' =? 0 then [] else (v', v' + 56) :: ablocks_fp (prhPj_hbl D1)).
assert (HFP1 : forall a, inFP FP1 a -> (v' <= a < v' + 56) \/
  exists a' k', In (a', k') D1 /\ a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. unfold FP1 in Ha. rewrite Hv'ne in Ha. apply inFP_cons in Ha.
  destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact (pfa_inFP_hbl_inv D1 a Ha)]. }
assert (Hv0 : (fe_v en =? 0) = false) by (apply Z.eqb_neq; exact Hvne).
(* every byte of FP1 is a byte of a harness block of D, live in Lam *)
assert (HFPD : forall a, inFP FP1 a -> exists a' k', In (a', k') (fe_D en) /\ In (a', k') Lam /\
  a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. destruct (HFP1 a Ha) as [Ho | (a' & k' & Hin & Hr)].
  - exists (fn_kids nd), kk. split; [exact Hk_inD|]. split; [exact HkLam|]. change (@cf_head CP) with 16. lia.
  - exists a', k'. split; [exact (HD1D _ Hin)|]. split; [exact (HD1L _ _ Hin) | exact Hr]. }
(* ======== the recursive call: the depth-d' text at the callee window 0 ======== *)
eapply (SRr'_bind SEGS RZ_cf).
{ eapply (aj_call_xWR (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
    W regsc mem (SIGMA AS_pj_free)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_pj_free d') 0 FP1 (-96 - fe_d en) (Z_to_bv 64 (BASE + (AF_pf + PF_LK))) []
    (fun ly' S' Hp' W' regs' mem' md' =>
       (pf_K0post (PA := PA) B D1 v' ly S Hp Lam (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en)
          (fe_own en) ly' S' Hp' W' regs' mem' md' /\ pf_reach FX F1 ly S [] ly' S') /\ (Pm mem -> Pm mem'))
    HJ HSPO Hal' Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
  - intros HPRE1 HWIN1.
    exact (IH (fe_most en) (fe_own en) ly S Hp W regsc mem mdc [] 0 v' D1 F1 Lam (fe_peak en) (fe_cnt en) (fe_fail en)
      (fe_ran en) (conj HPRE1 (conj HROD (conj HSTKHI1 (conj HRAZ1 HFRM0)))) HUNIV HROOM HA10 HWIN1
      (or_intror (conj Hv'n0 (conj Hv'ceil (conj HFO1 HSLOT)))) (fun _ => HSAFE1) HLED).
  - (* the footprint: within the caller's (D's blocks) *)
    intros a Ha. left. destruct (HFPD a Ha) as (a' & k' & HinD' & _ & Hr).
    unfold fe_FP. rewrite Hv0. apply inFP_cons. right. exact (pfa_inFP_hbl _ a' k' a HinD' Hr). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP2 & HK).
destruct HK as [(HK0 & HREACH) HMNc]. unfold pf_K0post in HK0.
destruct HK0 as (HROOM2 & Lam' & HpL & HpA & HLED2 & _ & _).
apply (KLK ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
(* ---- what the call kept ---- *)
replace (fe_sp0 en + fe_d en + (-96 - fe_d en) + 0) with (fe_sp0 en - 96) in HJc by lia.
replace (STK_pj_free d' + 0) with (STK_pj_free d') in HJc by lia.
assert (HFRc : pf_frameR SK B ARx Pm (wle' SEGS RZ_cf) en ly S Hp W regsc mem mdc k)
  by exact ((pfa_frame_sameR SK B ARx Pm (wle' SEGS RZ_cf)) en ly S Hp W regs regsc mem md mdc k HFR HJ Q2 Q3 Q4 Q27).
assert (Hcs : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv;
  25%bv; 26%bv; 27%bv] -> getr regs2 r = getr regsc r).
{ intros r Hr. apply pfa_pres; [exact HP2|]. cbn [In] in Hr. unfold acallee_saved.
  repeat (destruct Hr as [<- | Hr];
    [ vm_compute; first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
      | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
      | right; right; right; right; right; split; intro Hc; discriminate Hc ] |]); destruct Hr. }
assert (HL' : forall b, In b Lam -> ~ In b D1 -> In b Lam').
{ intros b Hb Hn. pose proof (Permutation_in _ HpL Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
assert (HL'L : forall b, In b Lam' -> In b Lam).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HpL)). apply in_or_app; right; exact Hb. }
assert (NDr : NoDup ((Dk ++ D1 ++ D2) ++ fn_own nd)) by exact (pfa_ndr _ _ ND).
assert (NDl : NoDup (Dk ++ D1 ++ D2)) by exact (pfa_ndl _ _ NDr).
assert (Nown_D1 : forall b, In b (fn_own nd) -> ~ In b D1).
{ intros b Ho H1. apply (pfa_nd_app _ _ b NDr); [apply in_or_app; right; apply in_or_app; left; exact H1 | exact Ho]. }
assert (Nown_D2 : forall b, In b (fn_own nd) -> ~ In b D2).
{ intros b Ho H2. apply (pfa_nd_app _ _ b NDr); [apply in_or_app; right; apply in_or_app; right; exact H2 | exact Ho]. }
assert (ND2_D1 : forall b, In b D2 -> ~ In b D1).
{ intros b H2 H1. exact (pfa_nd_app D1 D2 b (pfa_ndr _ _ NDl) H1 H2). }
assert (NDk_D1 : forall b, In b Dk -> ~ In b D1).
{ intros b Hk H1. apply (pfa_nd_app Dk (D1 ++ D2) b NDl Hk). apply in_or_app; left; exact H1. }
(* a harness block of Lam other than the kids block and D1's: its user bytes miss FP1 *)
assert (HNFP : forall a0 k0 y, In (a0, k0) Lam -> (a0, k0) <> (fn_kids nd, kk) -> ~ In (a0, k0) D1 ->
  a0 <= y < a0 + k0 -> ~ inFP FP1 y).
{ intros a0 k0 y Hin Hne HnD1 Hy Hfp. destruct (HFP1 y Hfp) as [Hv | (a' & k' & Hin' & Hr)].
  - apply ((pfa_hb_apart B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 (fn_kids nd) kk y HAR HLED Hin HkLam Hne Hy).
    change (@cf_head CP) with 16. lia.
  - assert (Hne' : (a0, k0) <> (a', k')) by (intros Ee; rewrite Ee in HnD1; exact (HnD1 Hin')).
    exact ((pfa_hb_apart B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 a' k' y HAR HLED Hin (HD1L _ _ Hin') Hne' Hy Hr). }
(* the kids block's bytes after slot i miss FP1 *)
assert (HNFPk : forall y, v' + 56 <= y < fn_kids nd + kk -> ~ inFP FP1 y).
{ intros y Hy Hfp. destruct (HFP1 y Hfp) as [Hv | (a' & k' & Hin' & Hr)]; [lia|].
  assert (Hne' : (fn_kids nd, kk) <> (a', k')) by (intros Ee; rewrite Ee in Hk_notD1; exact (Hk_notD1 Hin')).
  exact ((pfa_hb_apart B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ (fn_kids nd) kk a' k' y HAR HLED HkLam (HD1L _ _ Hin') Hne'
    ltac:(lia) Hr). }
assert (HSINK : ~ YI16.sink_open_fp FP1).
{ unfold FP1. rewrite Hv'ne. apply sink_closed_cons; [cbn [fst]; lia|]. apply sink_closed_ablocks_fp.
  apply Forall_forall. intros b Hb. unfold prhPj_hbl in Hb. apply in_map_iff in Hb as ((a' & k') & <- & Hin).
  cbn [fst]. destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ _ _ HAR HLED (HD1L _ _ Hin)) as (_ & Ha' & _).
  change (@cf_head CP) with 16 in *. lia. }
assert (HFPblk : forall x, inFP FP1 x -> exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m).
{ intros x Hx. destruct (HFPD x Hx) as (a' & k' & _ & Hin & Hr).
  destruct ((pfa_lam_blk B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ _ _ HAR HLED Hin) as (_ & _ & _ & _ & Hab & _).
  exists (a' - cf_head), (k' + cf_head). split; [exact Hab | exact Hr]. }
assert (Esp2 : spZ regs2 = spZ regsc) by (unfold spZ; f_equal; apply Hcs; cbn [In]; tauto).
pose proof (pfk_frameR SK B ARx pal_pst_ro Pm CTX0 PB FX (wle' SEGS RZ_cf) en ly S Hp W regsc mem mdc k (STK_pj_free d') FP1
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HFRc HJc HJ2 HSINK Esp2 (Hcs 3%bv ltac:(cbn [In]; tauto))
  (Hcs 4%bv ltac:(cbn [In]; tauto)) (Hcs 27%bv ltac:(cbn [In]; tauto)) HMNc) as HFR2.
(* ======== pf_LK at the return site ======== *)
split; [exact En|]. split; [exact Hi|]. split; [exact HFR2|].
split.
{ unfold pf_vregs. cbv zeta.
  split; [rewrite (Hcs 8%bv), Q8 by (cbn [In]; tauto); exact R8|].
  split; [rewrite (Hcs 9%bv), Q9 by (cbn [In]; tauto); reflexivity|].
  split; [rewrite (Hcs 18%bv), Q18 by (cbn [In]; tauto); reflexivity|].
  split; [rewrite (Hcs 19%bv), Q19 by (cbn [In]; tauto); reflexivity|].
  split; [rewrite (Hcs 20%bv), Q20 by (cbn [In]; tauto); exact R20|].
  rewrite (Hcs 21%bv), Q21 by (cbn [In]; tauto); reflexivity. }
split.
{ unfold pf_lregs. cbv zeta.
  split; [rewrite (Hcs 22%bv), Q22 by (cbn [In]; tauto); exact R22|].
  split; [rewrite (Hcs 23%bv), Q23 by (cbn [In]; tauto); exact R23|].
  split; [rewrite (Hcs 24%bv), Q24 by (cbn [In]; tauto); exact R24|].
  split; [rewrite (Hcs 25%bv), Q25 by (cbn [In]; tauto); reflexivity|].
  rewrite (Hcs 26%bv), Q26 by (cbn [In]; tauto); reflexivity. }
exists (Fd ++ F1), Lam', Dk, D2, F2.
split.
{ apply (pfk_acct_rec B FX en ly S Hp W mem Fd F1 (Dk ++ F2 ++ fn_own nd) Lam D1 ly2 S2 Hp2 W2 mem2 Lam');
  [| exact HROOM2 | exact HpL | exact HpA | exact HLED2 | exact HREACH | exact (proj2 HFD1)].
  rewrite <- !app_assoc in HAC. exact HAC. }
split.
{ apply (pfk_vnodeR SK B ARx LAWS VISF (wle' SEGS RZ_cf) en nd ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d')
    (fe_sp0 en - 96) FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
    (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) HVN HARc HLED HJc HLED2).
  - intros x Hx. destruct (HFPD x Hx) as (a' & k' & HinD' & Hin & Hr).
    exact ((pfa_v_apart B ARx LAWS) en nd ly S Hp W mem md Lam _ _ _ _ _ _ a' k' x HVN HAR HLED Hin HinD' Hr).
  - intros b Hb Hnb. pose proof (Permutation_in _ HpA Hb) as H. apply in_app_or in H as [H|H]; [|contradiction].
    unfold prhPj_hbl in H. apply in_map_iff in H as ((a' & k') & <- & Hin).
    exists a', k'. split; [exact (HD1D _ Hin)|]. split; [exact (HD1L _ _ Hin) | reflexivity].
  - intros a0 k0 Hin Hn. apply HL'; [exact Hin|]. intros H1. exact (Hn (HD1D _ H1)).
  - intros a0 k0 Hin. exact (HL'L _ Hin).
  - exact HFPblk. }
split.
{ eapply Permutation_trans; [exact HPD|]. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_tail.
  apply Permutation_sym. exact (proj2 HFD1). }
split.
{ (* slot i's key: its word in the keys block, live before and after, outside FP1 *)
  unfold pj_keyR in HKEY |- *. destruct (fn_ks nd) eqn:Eks; [|exact HKEY].
  destruct HKEYSn as [(_ & Hks & _) | (_ & ky & Hky & Hkyn & HDy)]; [congruence|].
  assert (Hown_y : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite HDy; apply in_or_app; right; left; reflexivity).
  assert (HyLam : In (fn_keys nd, ky) Lam).
  { apply (pfa_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
    apply (pfa_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_y. }
  assert (Hyk : (fn_keys nd, ky) <> (fn_kids nd, kk)).
  { intros Ee. assert (NDo : NoDup (fn_own nd)) by exact (pfa_ndr _ _ NDr).
    unfold fn_own in NDo. rewrite HDk, HDy in NDo. rewrite Ee in NDo.
    apply (pfa_nd_app [(fn_kids nd, kk)] ([(fn_kids nd, kk)] ++ fn_Ds nd) (fn_kids nd, kk) NDo); left; reflexivity. }
  destruct HKEY as (x & Hrd & Hx). exists x. split.
  - apply (rd_u64_frame SEGS _ _ _ _ Hrd). intros y Hy. apply (mbyte_of_aview SEGS).
    destruct (pfk_hblkR (SK := SK) B ARx LAWS (wle' SEGS RZ_cf) ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d')
      (fe_sp0 en - 96) FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fn_keys nd) ky y HARc HLED HJc HLED2 HyLam (HL' _ HyLam (Nown_D1 _ Hown_y)) ltac:(lia)
      (HNFP _ _ y HyLam Hyk (Nown_D1 _ Hown_y) ltac:(lia))) as [Hv _].
    exact Hv.
  - destruct Hx as [Hx | (kx & Hkx & ->)]; [left; exact Hx|]. right. exists kx. split; [|reflexivity].
    apply HL'; [exact Hkx|]. apply NDk_D1. left; reflexivity. }
(* the slots i + 1 .. n - 1 *)
apply (pfk_itemsR SK B ARx LAWS (wle' SEGS RZ_cf) d' ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam' (STK_pj_free d') (fe_sp0 en - 96)
  FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
  (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
  _ _ _ _ D2 F2 HARc HLED HJc HLED2 HIT2).
- intros x Hx. unfold pf_ofoot in Hx. rewrite Z2Nat.id in Hx by lia.
  destruct Hx as [Hx | [(Hks & Hx) | ((bx & bk) & Hb & Hh)]].
  + split; [apply HNFPk; lia|].
    exists (fn_kids nd), kk. split; [exact HkLam|]. split; [exact (HL' _ HkLam Hk_notD1) | lia].
  + destruct HKEYSn as [(_ & Hks' & _) | (_ & ky & Hky & Hkyn & HDy)]; [congruence|].
    assert (Hown_y : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite HDy; apply in_or_app; right; left; reflexivity).
    assert (HyLam : In (fn_keys nd, ky) Lam).
    { apply (pfa_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
      apply (pfa_nd_app Fd _ _ ND Hf). apply in_or_app; right; exact Hown_y. }
    assert (Hyk : (fn_keys nd, ky) <> (fn_kids nd, kk)).
    { intros Ee. assert (NDo : NoDup (fn_own nd)) by exact (pfa_ndr _ _ NDr).
      unfold fn_own in NDo. rewrite HDk, HDy in NDo. rewrite Ee in NDo.
      apply (pfa_nd_app [(fn_kids nd, kk)] ([(fn_kids nd, kk)] ++ fn_Ds nd) (fn_kids nd, kk) NDo); left; reflexivity. }
    split; [exact (HNFP _ _ x HyLam Hyk (Nown_D1 _ Hown_y) ltac:(lia))|].
    exists (fn_keys nd), ky. split; [exact HyLam|]. split; [exact (HL' _ HyLam (Nown_D1 _ Hown_y)) | lia].
  + unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
    pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT2 bx bk Hb) as HbL. unfold prh_lin in HbL.
    assert (Hbk : (bx, bk) <> (fn_kids nd, kk)).
    { intros Ee. rewrite Ee in Hb. exact (Nown_D2 _ Hown_k Hb). }
    split; [exact (HNFP _ _ x HbL Hbk (ND2_D1 _ Hb) Hh)|].
    exists bx, bk. split; [exact HbL|]. split; [exact (HL' _ HbL (ND2_D1 _ Hb)) | exact Hh].
- intros x k0 Hin. pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT2 x k0 Hin) as HbL. unfold prh_lin in HbL.
  exact (HL' _ HbL (ND2_D1 _ Hin)).
Qed.

End e.
End d.

Print Assumptions pf_seg_LH.
Print Assumptions pflh_seat.
