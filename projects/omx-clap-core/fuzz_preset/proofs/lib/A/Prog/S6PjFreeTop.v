(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 97 of its 134 lines of code are new or changed and 741 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk COMPOSED (rule 24: proves pj_free (kind: walk composition;
   the segment files carry the instructions: S6PjFreeEnt.v, S6PjFreeLH.v, S6PjFreeLKC.v, S6PjFreeTail.v).
   RULE-24 CONFIRM (lead 18:00Z, checker PjFreeR24): no released and no unreleased proof of pj_free on image A, old
   pin (entry 0x85fa8, lib/A/PAImg_prog.v:452 A_entry_pj_free): the released lib/Prog/pj_free.v pj_free_holds is the
   PLAIN image (0x156c0); the unreleased lib/A walks at 0x85df4 are a different asan binary (harness pins asan
   1288455872ab, not d83eb25d). The census-1 sweep covered 14,805 cold heads twice (17:44-17:47Z, 17:56-17:59Z;
   positive control: S6PjFreeEnt.v 4f0dc65c26fd); classification a Theorem Labs lane's worker record, the internal file pjfree-r24.tsv.
   - pj_free_walkP: the instrumented walk text tpj_free_specOP (S6PjFree.v; generic memory invariant Pm, any observer
     FX / PB with fuzz_free's instrumented text) at EVERY depth n, by induction on n (the recursive call at slot 38
     cites the text at n - 1 through pf_seg_LH) and, inside a node, by induction on the slots left (pf_seg_LH,
     pf_seg_LK, pf_seg_LC), entered by pf_seg_entry and left by pf_seg_LX / pf_seg_EP.
   - pj_free_holds: the kit's tpj_free_specX (lib/A/PRH_FnPj.v 5aca5cbe2cfb on the kit's cut 7cdbb61b5fa0: the
     order list F (PRH_PjOrder.pj_foR), (v <> 0 -> class-24 bound) at entry, no position at entry, and the
     POST-IMPLICATION position transfer for every model run with the exact advance i + length (prhPj_free_evs F)) at
     every depth, from pj_free_walkP at P := memnorm (tpj_free_specO_of_P) by PjFreeCommon.v's generic
     pf_specX_of_walk (observer pf_FXk / pf_PBk; one copy with image B).
   SECTION HYPOTHESES: LAWS (AR_laws_x at cf_head) and TL (PALib), witnessed at the A' instance by lib/A/PALibA.v
   (88c72c8175cf on the kit's cut 7cdbb61b5fa0) palib_laws_A / palib_A; VISF (YGcfFsVis.ARx_frame_hull_vis, the instance's
   ARx_frame_hull_vis_cf_ok); the image facts Hent, Hobj, PAB, pal_pst_img, pal_pst_ro, pal_ret_free, each witnessed by
   vm_compute at PI_prog_A in lib/A/Prog/S6ImgWit.v; the memset row AIM (YGcallMxmn.v aintrin_realizes_xm, a callee
   text; A' row of a Theorem Labs lane, PRowSet.v prow_asan_memset_xm_A); and the fuzz_free text FREE (PRH_FnAlloc.v
   4d8aeba047e5 on the cut). The old-pin FREEFIX premise (the open text tfuzz_free_specX_FIX) is GONE since f97c:
   the kit's tfuzz_free_specX takes no position at entry and moves a bulk sub-position in its post, which is all pj_free's
   frees need.
   RELOCATED A -> A' (asan d83eb25d -> 1be0f53d) from donor cold/h-hpreset-7-walk-S6 b4d577c07502; the old-pin CONFIRM
   above quotes old-pin addresses (A' entry: the listing's A_entry_pj_free).
   THE RE-HIDING MOVE: the kit's texts tfuzz_free_specX and tpj_free_specX conclude SRr' segs RZ_cf with their posts at
   wle', and so do the walk's texts and segments; the composition's cut assertions are at SRr' SEGS RZ_cf. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeGlue S6PjFreeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeEnt S6PjFreeLH S6PjFreeLKC S6PjFreeTail.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
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

Section top.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
Hypothesis VISF : YGcfFsVis.ARx_frame_hull_vis SEGS B ARx.
(* image facts, witnessed at PI_prog_A by lib/A/Prog/S6ImgWit.v *)
Hypothesis Hent : SIGMA AS_pj_free = BASE + AF_pf.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
Hypothesis pal_pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Hypothesis pal_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Hypothesis pal_ret_free : forall off, In off [200; 252; 276; 304] ->
  In (BASE + AF_pf + off) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free).
(* the memset row (c-omx-alloc's m-form intrinsic text) *)
Hypothesis AIM : aintrin_realizes_xm SEGS B ARx OSet (SIGMA AS___asan_memset).

(* the cuts' v <> NULL facts *)
Lemma pft_LX_vne : forall Pm FX en nd ly S Hp W regs mem md k,
  pf_LX SK B ARx Pm FX en nd ly S Hp W regs mem md k -> fe_v en <> 0.
Proof.
intros Pm FX en nd ly S Hp W regs mem md k (_ & _ & Fd & Lam & _ & HVN & _).
destruct HVN as (H4096 & _). lia.
Qed.
Lemma pft_LH_vne : forall Pm FX en nd d' i ly S Hp W regs mem md k,
  pf_LH SK B ARx Pm FX en nd d' i ly S Hp W regs mem md k -> fe_v en <> 0.
Proof.
intros Pm FX en nd d' i ly S Hp W regs mem md k (_ & _ & _ & _ & _ & Fd & Lam & Dr & Fr & _ & HVN & _).
destruct HVN as (H4096 & _). lia.
Qed.

(* ======== the instrumented walk text at every depth (generic memory invariant, any observer) ======== *)
Theorem pj_free_walkP : forall Pm, srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm ->
  forall PB FX CTX0, tfuzz_free_specO (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK PB FX ->
  forall n, tpj_free_specOP (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK Pm PB FX CTX0 n.
Proof.
intros Pm PLAW PCALL PB FX CTX0 FREE n.
induction n as [|d' IH];
  intros most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran HFP HU HR H10 HW HC HSF HL;
  [set (en := MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran O most own)
  |set (en := MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran (Datatypes.S d') most own)];
  (assert (HPRE : pf_pre B ARx CTX0 PB FX en)
     by exact (conj HFP (conj HU (conj HR (conj H10 (conj HW (conj HC (conj HSF HL))))))));
  (assert (KLX : forall nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1, pf_node en nd ->
      pf_LX SK B ARx Pm FX en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 ->
      SRr' SEGS RZ_cf W1 (pf_cfg PF_LX regs1 mem1 md1) (pf_FIN SK B ARx Pm FX en))
     by (intros nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HND HLX;
         exact (pf_seg_LX SK B ARx LAWS Pm PLAW CTX0 PB FX VISF pal_pst_img pal_pst_ro pal_ret_free FREE AIM PCALL
           en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HPRE HND
           (pft_LX_vne Pm FX en nd ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HLX) HLX))).
- (* depth 0: no loop (the node has no slots) *)
  apply (pf_seg_entry SK B ARx LAWS TL Hent Hobj pal_pst_img Pm PLAW CTX0 PB FX en HPRE KLX).
  intros nd d'' ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HND HLH. destruct HLH as (En & _). discriminate En.
- (* depth S d': the loop, by induction on the slots left; the recursive call cites the depth-d' text IH *)
  apply (pf_seg_entry SK B ARx LAWS TL Hent Hobj pal_pst_img Pm PLAW CTX0 PB FX en HPRE KLX).
  intros nd d'' ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HND HLH.
  assert (Ed : d'' = d') by (destruct HLH as (En & _); cbn [en fe_n] in En; injection En; auto). subst d''.
  assert (LOOP : forall m i ly2 S2 Hp2 W2 regs2 mem2 md2 k2, Z.to_nat (fn_n nd - i) = m ->
     pf_LH SK B ARx Pm FX en nd d' i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 ->
     SRr' SEGS RZ_cf W2 (pf_cfg PF_LH regs2 mem2 md2) (pf_FIN SK B ARx Pm FX en)).
  { induction m as [|m IHm]; intros i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Hm HLH2.
    - exfalso. destruct HLH2 as (_ & Hi & _). lia.
    - pose proof (pft_LH_vne Pm FX en nd d' i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HLH2) as Hvne.
      apply (pf_seg_LH SK B ARx LAWS VISF pal_pst_ro Pm PLAW CTX0 PB FX d' IH en nd i ly2 S2 Hp2 W2 regs2 mem2 md2 k2
        HPRE HND Hvne HLH2).
      intros ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HLK3.
      apply (pf_seg_LK SK B ARx LAWS VISF PAB pal_pst_ro pal_ret_free Pm PLAW PCALL CTX0 PB FX FREE d' en nd i
        ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HPRE HND Hvne HLK3).
      intros ly4 S4 Hp4 W4 regs4 mem4 md4 k4 HLC4.
      apply (pf_seg_LC SK B ARx LAWS Pm PLAW CTX0 PB FX d' en nd i ly4 S4 Hp4 W4 regs4 mem4 md4 k4 HPRE HND Hvne HLC4).
      + intros ly5 S5 Hp5 W5 regs5 mem5 md5 k5 HLH5.
        apply (IHm (i + 1) ly5 S5 Hp5 W5 regs5 mem5 md5 k5); [lia | exact HLH5].
      + intros ly5 S5 Hp5 W5 regs5 mem5 md5 k5 HLX5. exact (KLX nd ly5 S5 Hp5 W5 regs5 mem5 md5 k5 HND HLX5). }
  exact (LOOP _ 0 ly1 S1 Hp1 W1 regs1 mem1 md1 k1 eq_refl HLH).
Qed.

(* The kit's fuzz_free text, a callee text (PRH_FnAlloc.v 4d8aeba047e5 on the kit's cut 7cdbb61b5fa0: admits at the call and
   the budgeted post, which PjFreeCommon.pf_ff_of_kit absorbs; the hull budget at a non-NULL free and the hull use in
   the post, which pf_ff_of_kit carries in the observer pf_PBk / pf_FXk) *)
Hypothesis FREE : PRH_FnAlloc.tfuzz_free_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK.

(* ======== The kit's tpj_free_specX (PRH_FnPj.v 5aca5cbe2cfb on the kit's cut 7cdbb61b5fa0: no run words DW, the premise
   prh_head_wide, which pf_specX_of_walk hands the walk; the hull budget at entry (v <> 0) and the hull use in the
   post, which pf_specX_of_walk gives through the observer: pfk_safe, pfk_reach_hull) at every depth ======== *)
Theorem pj_free_holds : forall CTX0 n, tpj_free_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK CTX0 n.
Proof.
intros CTX0 n. apply (pf_specX_of_walk B ARx SK CTX0 n); [|exact FREE].
(* the walk does not need the kit's prh_head_wide, which pf_specX_of_walk hands it *)
intros _ PB FX HFR. apply tpj_free_specO_of_P.
exact (pj_free_walkP (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) (fun m m' Hk H => Hk H)
  PB FX CTX0 HFR n).
Qed.
End top.
End d.

Print Assumptions pj_free_walkP.
Print Assumptions pj_free_holds.
