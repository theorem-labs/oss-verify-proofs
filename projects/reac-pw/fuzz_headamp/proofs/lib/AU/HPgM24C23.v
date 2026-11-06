(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM24Mal.v at be048d930b4 (image A's
   malloc(first) step C6 -> C7) for image B's malloc(pod) step C2 -> C3: lib/AU/HPgSegM.v hqu_S_C23_stmt at
   lib/AU/Img0U.v rsegs, the jal 0x83740 -> 0x82efc, ra 0x83744 -> 0x82f00, malloc's entry 0x53060 -> 0x530e0, the
   real frame 0x1e0 -> 0x220, the request 3 max(rc, 0) + (it == 0) -> len + (len == 0) = len, k = 3 -> 1 event, the
   blocks pp / pod / out -> pp, image B's cut lists (hi_L2 -> hi_L3) and call-site lemmas (lib/AU/HPgSiteB.v), four
   float saves in place of three, the post hqu_cut_C3 (the record's pp bytes kept, the new pod block 16-aligned,
   its shadow and its hull, amem_range of len + 8 from AR's in_app); the step-independent lemmas in
   lib/AU/HPgM24MalKit.v (prefix hk_ -> hkb_). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): THE malloc(pod) STEP of the
   walk of LLVMFuzzerTestOneInput, C2 = 0x82efc -> C3 = 0x82f00, i.e. lib/AU/HPgSegM.v hqu_S_C23_stmt at the
   concrete segments lib/AU/Img0U.v rsegs. Proves no function (kind: segment lemma).

   THE CODE. At C2 a0 = len + (len == 0) (HPgImgB hi_L2: (LReg 10, XLenNZ)) = len, as 8 <= len <= 5440
   (hqu_cut_C2). 0x82efc is `jal 0x530e0`: ra := 0x82f00, pc := 0x530e0, the runtime's malloc entry of image B.
   C3 = 0x82f00 is the return address.

   THE ROUTE (lib/AU/HPgM24C67.v's): one engine step over the `jal`; YCbq.aj_malloc_at04 at hqu_j (k = 1,
   o = R - S, -0x230 <= o <= -0x220) with the caller chain from hqu_kept's ra / s0 cells; the rule's post turned into
   hqu_at_C3: the block list C2's ++ [(pod, len)] (pod fresh by sep_blocks_pos), sp / gp / tp and the callee-saved
   registers kept, hi_L3 by headamp_B_site_cut3, frame shadow / flag cell / thirteen saves / four float saves / pp
   bytes by acall_kept, and for the new block: 16-aligned (AR_blocks_law), its shadow and hull (hm_blk_ra), and
   pod + len + 8 inside the application range (AR_blocks_law's in_app).

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     forall fx', amalloc_realizes rsegs B   the runtime's malloc, at every float state
     errno_low   api_env rsegs B                        errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)             the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x530e0   malloc's entry is the jal's target
     HSTK_C23    ASTACK + HQU_RSZ + 16 <= LLVMF_STK     the call's stack budget
     HEV_C23     2 <= EV_LIB                            room for this event (the second)
     HLIVE_C23   Layout.PP_SIZE + 5440 <= LIVE_LIB      room for pod after pp
     HTRACE_C23  the malloc trace at ra = 0x82f00 is in the universe.
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YK07.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgSteps HPgSiteB HPgM24MalKit HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the one instruction word the engine runs: the `jal` at C2 ---- *)
Definition hkb_tbl : ctable := build_table rsegs HQU_C2 1 TEmpty.
Lemma hkb_tbl_ok : table_ok rsegs hkb_tbl.
Proof. apply build_table_ok0. unfold HQU_C2. lia. Qed.

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x530e0.
Hypothesis HSTK_C23 : ASTACK + HQU_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C23 : 2 <= EV_LIB.
Hypothesis HLIVE_C23 : Layout.PP_SIZE + 5440 <= LIVE_LIB.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : hqu_hcx rsegs),
raZ (hu_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQU_C3 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hkb_ch hx)) (as_universe B).

Theorem hqu_B_S_C23 : hqu_S_C23_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C23 HEV_C23 HLIVE_C23 HTRACE_C23.
unfold hqu_S_C23_stmt. intros hx fx2 pos e r ly6 S6 W6 regs6 mem6 md6 HB HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & Hfr0 & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HAC & Hfrm & Hwf & Hlen & Hlenb & Hpp & Hcap & Hnull).
destruct HAC as (HJ6 & Hperm6 & Hfresh6 & Hsp6 & Hgp6 & Htp6 & Hgeo & HL6 & Hfsh6 & Hkept6).
pose proof Hgeo as (HeS & HeR & HeF).
unfold hqu_j in HJ6.
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & Hnev & _ & F1 & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & EF6 & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HSTK_C23 as HSTK. unfold ASTACK, HQU_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 0x220 = 32 q + r, 0 <= r < 32, so S - R is 0x220 or 0x230 *)
rewrite HeS in HeR. unfold HQU_RSZ in HeR.
pose proof (Z.div_mod (spZ (hu_regs rsegs hx) - 0x220) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (hu_regs rsegs hx) - 0x220) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (hu_regs rsegs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 0x220 <= spZ (hu_regs rsegs hx) /\
  spZ (hu_regs rsegs hx) - e_R e <= 0x230) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by lia.
assert (HS64 : 0 <= spZ (hu_regs rsegs hx) < 2 ^ 64) by lia.
assert (HAL : (e_R e - spZ (hu_regs rsegs hx)) mod 16 = 0).
{ replace (e_R e - spZ (hu_regs rsegs hx))
    with ((2 * ((spZ (hu_regs rsegs hx) - 0x220) / 32) - spZ (hu_regs rsegs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (hu_regs rsegs hx) mod 8 = 0).
{ replace (spZ (hu_regs rsegs hx)) with ((2 * (spZ (hu_regs rsegs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C2 values a0 = the request and s0 = S *)
pose proof HL6 as HL6c. unfold hd_cut in HL6c. cbn [hi_L2 headamp_himg_B] in HL6c. unfold headamp_B_L23 in HL6c.
apply Forall_cons_iff in HL6c as [C10 HL6c]. apply Forall_cons_iff in HL6c as [C8 _].
cbn [fst snd hd_at] in C10, C8. cbn [hd_xv] in C8. rewrite HeS in C8.
(* the request: len + (len == 0) = len, as 8 <= len <= 5440 *)
assert (HXv' : hd_xv e XLenNZ = e_len e) by (cbn [hd_xv]; destruct (Z.eqb_spec (e_len e) 0); lia).
rewrite HXv' in C10.
assert (HN : 0 <= e_len e < MALLOC_MAX) by (change MALLOC_MAX with 268435456; lia).
assert (Hrq : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
destruct Hkept6 as (Hcl6 & Hfs6).
pose proof Hcl6 as Hcl6c.
unfold hqu_cells, hqu_saves_L in Hcl6c. cbn [seq map app] in Hcl6c.
apply Forall_cons_iff in Hcl6c as [K0 Hcl6c]. apply Forall_cons_iff in Hcl6c as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (hkb_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (hkb_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [hd_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W6) mem6) (spZ (hu_regs rsegs hx) - 8) = Some (raZ (hu_regs rsegs hx))).
{ replace (spZ (hu_regs rsegs hx) - 8) with (spZ (hu_regs rsegs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W6) mem6) (spZ (hu_regs rsegs hx) - 16) = Some (s0Z (hu_regs rsegs hx))).
{ replace (spZ (hu_regs rsegs hx) - 16) with (spZ (hu_regs rsegs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x530e0 *)
pose proof (hkb_entry HQU_C2 fx2 W6 regs6 mem6) as HS.
assert (SHOK : sh_ok rsegs RTBx [] (Ereg regs6 rt_extra) (mrestrict (w_H W6) mem6)) by constructor.
assert (HAE : env_agree 32 (Ereg regs6 rt_extra) (Ereg regs6 rt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 HQU_C2) with (Z_to_bv 64 HQU_C2).
aj_run_tok hkb_tbl_ok HS HJ6 SHOK RTBspan; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x82f00 *)
assert (Hm : ms_mem ms = mem6).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 1] -> getr (ms_regs ms) rr = getr regs6 rr).
{ eapply (regs_kept_of_st_ok rsegs _ _ ms regs6 rt_extra (w_H W6) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x82f00).
{ rewrite (hkb_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  rewrite (st_ok_restrict_reg rsegs (w_H W6) _ _ ms (Z_to_bv 5 1) HS).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    replace (sr_get (ss_regs ss) (Z_to_bv 5 1)) with (SLit 0x82f00) by (vm_compute; reflexivity) end.
  reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (e_len e)).
{ rewrite RK by hkb_rk. rewrite (hkb_getr_eq regs6 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HLV : blocks_bytes S6 + e_len e <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly6 S6), (bsum_perm _ _ Hperm6), bsum_app,
    <- (blocks_bytes_bsum B (hu_ly rsegs hx) (hu_S rsegs hx)).
  unfold hqu_blocks1, bsum. cbn [app fold_right snd]. change Layout.PP_SIZE with 19744 in *. lia. }
assert (HSP : spZ (ms_regs ms) = spZ (hu_regs rsegs hx) + (e_R e - spZ (hu_regs rsegs hx))).
{ unfold spZ at 1. rewrite RK by hkb_rk. rewrite Hsp6. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (hu_regs rsegs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (hu_regs rsegs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by hkb_rk; exact Hgp6).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by hkb_rk; exact Htp6).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x82f00)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S6 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x82f00) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
assert (HCH : chain_pre ly6 (aview rsegs (w_H W6) mem6) (ms_regs ms) (hkb_ch hx)).
{ apply (achain_chain_pre ly6 _ (e_R e) (spZ (hu_regs rsegs hx))).
  - apply (achain_ly_top (hu_ly rsegs hx) ly6 _ _ _ _ Etop). unfold hkb_ch.
    apply (hkb_chain (hu_ly rsegs hx) (aview rsegs (w_H (hu_W rsegs hx)) (hu_mem rsegs hx))).
    + exact Hch0.
    + lia.
    + intros a Ha. apply F1; lia.
    + exact R8.
    + exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by hkb_rk. rewrite (hkb_getr_eq regs6 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) (hkb_ch hx)) (as_universe B)).
{ apply HTRACE_C23; [exact Hra0 | rewrite HRAZ; reflexivity]. }
(* the machine state at 0x530e0 = pc_wrap_malloc *)
rewrite (st_ok_restrict_mkst rsegs (w_H W6) _ _ ms HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
rewrite Hm. rewrite Hm in HJ6.
eapply SRr_mono.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML (AMALLOC fx2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ6 HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the post at C3 *)
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & pod & Ec7 & HJ7 & Hpres7 & H107 & Hfr7 & Hpod & Hab7 & Hkept7).
replace (spZ (hu_regs rsegs hx) + (e_R e - spZ (hu_regs rsegs hx))) with (e_R e) in Hkept7 by lia.
pose proof Hkept7 as (KK1 & KK2 & _ & KK4 & _ & _).
pose proof HJ7 as (HAR7 & Hly7 & _).
pose proof Hly7 as (_ & _ & _ & _ & _ & EF7 & _).
(* the callee-saved registers of C2 *)
assert (KR : forall rr, acallee_saved rr -> getr regs7 (Z_to_bv 5 rr) = getr regs6 (Z_to_bv 5 rr)).
{ intros rr Hr. rewrite (Hpres7 rr Hr). apply RK.
  - rewrite (cb_cs_bv rr Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (cb_cs_bv rr Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
(* the blocks: pp live at C2, pod appended, apart from pod *)
assert (Hin6 : forall b, In b (hqu_blocks1 e) -> In b (ablocks B ly6 S6)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm6)). apply in_or_app. right. exact Hb. }
assert (Hin7 : forall b, In b (ablocks B ly6 S6) -> In b (ablocks B ly7 S7)).
{ intros b Hb. rewrite Hab7. apply in_or_app. left. exact Hb. }
assert (Hpp6 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly6 S6)) by (apply Hin6; cbn; left; reflexivity).
assert (Hpod7 : In (pod, e_len e) (ablocks B ly7 S7))
  by (rewrite Hab7; apply in_or_app; right; left; reflexivity).
assert (Hapart : forall p m, In (p, m) (ablocks B ly6 S6) ->
  p + req_size m <= pod \/ pod + req_size (e_len e) <= p).
{ intros p m Hb. apply in_split in Hb as (l1 & l2 & El).
  pose proof (sep_blocks_pos rsegs B LAWS ly7 S7 W7 mem7 md7 (p, m) (pod, e_len e) l1 l2 [] HAR7
    ltac:(rewrite Hab7, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
assert (Hfresh : ~ In (pod, e_len e) (ablocks B (hu_ly rsegs hx) (hu_S rsegs hx))).
{ intros Hx. assert (Hx6 : In (pod, e_len e) (ablocks B ly6 S6))
    by (apply (Permutation_in _ (Permutation_sym Hperm6)); apply in_or_app; left; exact Hx).
  pose proof (Hapart _ _ Hx6) as Hd. rewrite Hrq in Hd. lia. }
(* the frame for locals: at F in both layouts, apart from pod and from pod's range in the shadow *)
assert (HinF6 : In (HQU_CID, pos) (frames S6)) by (rewrite Hfrs6; left; reflexivity).
assert (HinF7 : In (HQU_CID, pos) (frames S7)) by (rewrite Hfr7; exact HinF6).
assert (FA6 : frame_addr ly6 HQU_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF6; reflexivity).
assert (FA7 : frame_addr ly7 HQU_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF7; reflexivity).
assert (Hfb : fs_frame_bytes HQU_CID = 1024) by reflexivity.
pose proof (sep_block_frame rsegs B LAWS ly7 S7 W7 mem7 md7 pod (e_len e) HQU_CID pos HAR7 Hpod7 HinF7)
  as HdF.
rewrite FA7, Hfb in HdF. unfold zdisjoint in HdF. cbn [fst snd] in HdF.
destruct (al_frames _ _ LAWS ly6 S6 W6 mem6 md6 HQU_CID pos HAR6 HinF6) as (HF32 & HFapp & _).
rewrite FA6, Hfb in HFapp.
destruct (al_blocks _ _ LAWS ly7 S7 W7 mem7 md7 pod (e_len e) HAR7 Hpod7) as (Pm16 & _ & Pce & Papp & _).
assert (HshF : forall i, 0 <= i < 128 ->
  ~ (pod <= shadow_addr (e_F e) + i < pod + req_size (e_len e))).
{ intros i Hi. pose proof C1 as [_ C1h]. exact (hkb_shadow_apart _ _ _ _ HFapp Papp C1h Hi). }
(* the live block's bytes: kept by the call when they lie apart from pod *)
assert (Hkb : forall p m i, In (p, m) (ablocks B ly6 S6) -> 0 <= i < req_size m ->
  aview rsegs (w_H W7) mem7 (p + i) = aview rsegs (w_H W6) mem6 (p + i)).
{ intros p m i Hb Hi. apply (KK2 p m i Hb Hi). pose proof (Hapart p m Hb). cbv beta. lia. }
(* the real frame above R: kept by the call *)
assert (Hkr : forall a, e_R e <= a < spZ (hu_regs rsegs hx) -> aview rsegs (w_H W7) mem7 a = aview rsegs (w_H W6) mem6 a).
{ intros a Ha. apply KK1; lia. }
(* ===== hqu_at_C3 ===== *)
unfold hqu_at_C3. exists pod, ly7, S7, regs7, mem7, md7.
split; [rewrite Ec7; reflexivity|].
split; [exact Hpod|].
split; [exact H107|].
split; [exact KR|].
split; [exact Hfr7|].
split; [exact Hab7|].
split; [exact Hkept7|].
(* ===== hqu_cut_C3 at the env with pod ===== *)
unfold hqu_cut_C3, hqu_at_cut.
split.
{ split; [exact HJ7|].
  split.
  { change (hqu_blocks3 (hqu_env_pod e pod)) with (hqu_blocks1 e ++ [(pod, e_len e)]).
    rewrite Hab7, app_assoc. apply Permutation_app_tail. exact Hperm6. }
  split.
  { change (hqu_blocks3 (hqu_env_pod e pod)) with (hqu_blocks1 e ++ [(pod, e_len e)]).
    apply Forall_app. split; [exact Hfresh6|].
    apply Forall_cons; [|apply Forall_nil]. cbv beta. cbn [fst]. split; [exact Hfresh | lia]. }
  split.
  { rewrite (hkb_getr_eq regs7 2 (Z_to_bv 5 2)) by reflexivity. rewrite (KR 2) by (unfold acallee_saved; lia).
    rewrite (hkb_getr_eq regs6 (Z_to_bv 5 2) 2) by reflexivity. exact Hsp6. }
  split.
  { rewrite (hkb_getr_eq regs7 3 (Z_to_bv 5 3)) by reflexivity. rewrite (KR 3) by (unfold acallee_saved; lia).
    rewrite (hkb_getr_eq regs6 (Z_to_bv 5 3) 3) by reflexivity. exact Hgp6. }
  split.
  { rewrite (hkb_getr_eq regs7 4 (Z_to_bv 5 4)) by reflexivity. rewrite (KR 4) by (unfold acallee_saved; lia).
    rewrite (hkb_getr_eq regs6 (Z_to_bv 5 4) 4) by reflexivity. exact Htp6. }
  split; [exact Hgeo|].
  split.
  { (* hi_L3: hi_L2 kept (its cells lie above R), then a0 = pod *)
    assert (HcutA : hd_cut rsegs (w_H W7) mem7 regs6 e (hi_L2 headamp_himg_B)).
    { apply (hm_cut_kept rsegs (w_H W6) mem6 (w_H W7) mem7 regs6 regs6 e _ HL6).
      intros f Hf. cbn [hi_L2 headamp_himg_B] in Hf. unfold headamp_B_L23 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv]; first [reflexivity | (intros i Hi; apply Hkr; lia)] |]).
      destruct Hf. }
    assert (HcutA' : hd_cut rsegs (w_H W7) mem7 regs6 (hqu_env_pod e pod) (hi_L2 headamp_himg_B)).
    { unfold hd_cut in HcutA |- *. apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) HcutA f Hf) as Hx.
      cbn [hi_L2 headamp_himg_B] in Hf. unfold headamp_B_L23 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [exact Hx|]). destruct Hf. }
    apply (headamp_B_site_cut3 rsegs (w_H W7) mem7 mem7 regs6 regs7 (hqu_env_pod e pod) HcutA').
    - rewrite (hkb_getr_eq regs7 (Z_to_bv 5 10) 10) by reflexivity. exact H107.
    - intros rr _ Hrr. apply KR. cbn [In] in Hrr. unfold acallee_saved. lia.
    - intros o _ i _. reflexivity. }
  split.
  { (* the frame's shadow, kept by the call's frame clause *)
    apply (hm_fsh_kept rsegs (w_H W6) mem6 (w_H W7) mem7 (e_F e) _ Hfsh6).
    intros i Hi. assert (Hl : length (hi_shA headamp_himg_B) = 116%nat) by (vm_compute; reflexivity).
    rewrite Hl in Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi.
    apply (KK4 HQU_CID pos); [exact HinF6 | right | cbv beta; apply HshF; lia].
    unfold in_zr. cbn [fst snd]. rewrite FA6, Hfb. change (1024 / 8) with 128. lia. }
  { (* the thirteen saves and the flag cell, and the four float saves *)
    split.
    - assert (Hcl7 : Forall (fun f => hd_at rsegs (w_H W7) mem7 regs7 e (fst f) (snd f))
        (hqu_cells (hu_regs rsegs hx) (flag_addr (hu_ly rsegs hx) HQU_CID pos))).
      { apply (hm_atl_kept rsegs (w_H W6) mem6 (w_H W7) mem7 regs6 regs7 e _ Hcl6).
        intros f Hf. unfold hqu_cells, hqu_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
        + apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn [fst hm_keeps hd_xv].
          intros i Hi. apply Hkr. lia.
        + destruct Hf as [<-|[]]. cbn [fst hm_keeps hd_xv]. intros i Hi. unfold HQU_FLAG.
          apply (KK4 HQU_CID pos); [exact HinF6 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA6, Hfb; lia
          | cbv beta; lia]. }
      apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) Hcl7 f Hf) as Hx.
      unfold hqu_cells, hqu_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
      + apply in_map_iff in Hf as (j & <- & _). exact Hx.
      + destruct Hf as [<-|[]]. exact Hx.
    - destruct Hfs6 as (v0 & v1 & v2 & v3 & G0 & G1 & G2 & G3). exists v0, v1, v2, v3.
      cbn [hd_at hd_xv hqu_env_pod e_S] in G0, G1, G2, G3 |- *.
      split; [|split; [|split]];
      (eapply (hd_val_mem_kept rsegs (w_H W6) (w_H W7) mem6 mem7); [|eassumption]);
      intros i Hi; apply Hkr; lia. } }
split; [exact Hfrm|].
split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlenb|].
split.
{ apply (hd_garr8_kept rsegs (w_H W6) (w_H W7) mem6 mem7 (e_pp e)); [|exact Hpp].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
  pose proof (Layout.length_pp_bytes r Hwf) as HLp.
  apply (Hkb _ _ _ Hpp6). change (req_size Layout.PP_SIZE) with 19744. change Layout.PP_SIZE with 19744 in HLp. lia. }
split; [exact Pm16|].
split.
{ exact (proj2 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 pod (e_len e) pod (e_len e) HAR7 Hpod7
    ltac:(lia) ltac:(rewrite Hrq; lia)) ltac:(lia)). }
split.
{ (* pod + len + 8 stays in the application range: the block lies in it (AR_blocks_law's in_app) *)
  rewrite Hrq in Papp, Pce. pose proof C1 as [_ C1h].
  cbn [hqu_env_pod e_pod e_len]. unfold in_app in Papp. destruct Papp as (_ & Hpap).
  unfold amem_range.
  destruct Hpap as [Pl | (Ph1 & Ph2)].
  - left. unfold kLowShadowBeg in Pl. unfold kLowMemEnd. lia.
  - right. unfold ASAN_CEIL in Ph2. split; [exact Ph1|]. unfold kHighMemEnd. lia. }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 pod (e_len e) pod (e_len e) HAR7 Hpod7
    ltac:(lia) ltac:(rewrite Hrq; lia))). }
split; [exact Hcap | exact Hnull].
Qed.
(* inside the Section: the kernel's axioms and the Section hypotheses named in the header *)
Print Assumptions hqu_B_S_C23.
End d.
End b.
Print Assumptions hqu_B_S_C23.
