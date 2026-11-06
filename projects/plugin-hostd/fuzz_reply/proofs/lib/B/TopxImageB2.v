(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/TopxImage.v, with its module paths and module names changed; 78 of its 183 lines of code are new or changed and 71 lines of the source are left out. *)
(* Three image facts of image B's top_x (fuzz_reply.asan-ubsan), the image-B twins of lib/A/TopxImage.v's topx_GSHV_x,
   topx_FP_SINK and topx_HGOTG_x, each stated as image B's row at the instance ARX := top_x's relation
   (W_LLVMFuzzerTestOneInput_top_x.v Definition ARX: ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB /\ Hp = [] /\
   arodata_ok_cf), B := TfibB, CfParams_reply (lib/B/ReplyBTop.v Context rows GSHV_x, FP_SINK, HGOTG_x):
     topx_GSHV_x_B   GSHV_x    pro_G's shadow hulls are visible (pro_G is image B's op_add G: g_s, g_nfd, RA_G)
     topx_FP_SINK_B  FP_SINK   at fr_FP := YCfn_cf.fr_FP_b, the B driver's footprint
     topx_HGOTG_x_B  HGOTG_x   the GOT word 0x9ebd8 holds &__stack_chk_guard = 0x5f9a30
   What ARX gives: only its AR_laws_x, as top_x's ARX_laws builds them (restated here as topx_ARX_laws_B, with top_x's
   proof, since this file must not Require top_x, which takes these lemmas): alx_const_cells (every cell of
   as_const TfibB ly = YF0m.Tfib_const ly holds), alx_zshadow (every range of zero_shadow_ranges TfibB ly reads 0) and
   alx_blocks (a live block starts at or above 4096).
   GSHV_x: the shadow bytes of each pro_G range's hull are covered by YF0m's zero-shadow ranges or its value-bearing
   const cells (decided by vm_compute over pro_G), so each such byte reads Some; image A's
   W_LLVMFuzzerTestOneInput_addI.zz_GSHV is the same argument over A's tables.
   FP_SINK: the footprint is g_src's table (G, G + ATABLE) when g_src reads G <> 0 and g_out's buffer (o, o + c) when
   g_capout reads c <> 0; both are harness blocks (cut.v fr_hblks), which the pre's HB clause makes live blocks, so
   each range starts at or above 4096 and none holds address 0 (YI16.v sink_open_fp FP := in_fp FP 0).
   HGOTG_x: YF0m's const cell z8 0x9ebd8 0x5f9a30 (YE22.canary_cell_in), held by alx_const_cells. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v YI04 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_sites YE22 W_LLVMFuzzerTestOneInput_pro.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB YCfn_cf.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section topx_image_b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* lib/B/W_LLVMFuzzerTestOneInput_top_x.v Definition ARX, the same relation *)
#[local] Notation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
  @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem).

(* lib/B/W_LLVMFuzzerTestOneInput_top_x.v ARX_laws, restated (same proof) *)
Lemma topx_ARX_laws_B : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof.
  apply (AR_laws_x_iff segs TfibB (fun ly S Hp W mem md =>
           (ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) /\
           @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem)).
  { intros ly S Hp W mem md. split.
    - intros ((H1 & H2) & H3). exact (conj H1 (conj H2 H3)).
    - intros (H1 & H2 & H3). exact (conj (conj H1 H2) H3). }
  apply (AR_laws_x_and_mem segs TfibB _ (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB) ReplyKeptAroB.arodata_kept_B).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* ================================================================ GSHV_x *)
(* the bytes YF0m's tables make visible: a zero-shadow range's shadow bytes, or a value-bearing const cell's bytes *)
Definition zb_avcell (c : acell) : option (Z * nat) :=
  match c with ACell (ANum z) w (AV _) => Some (z, w) | _ => None end.
Lemma zb_avcell_ok : forall c z w, zb_avcell c = Some (z, w) -> exists e, c = ACell (ANum z) w (AV e).
Proof.
  intros [ca w cv] z w' H. destruct ca; try (simpl in H; discriminate H).
  destruct cv as [e|mk vk]; [|simpl in H; discriminate H]. simpl in H. injection H as -> ->. exists e. reflexivity.
Qed.
Definition zb_visb (s : Z) : bool :=
  existsb (fun r => (shadow_of_addr SHADOW_OFF (fst r) <=? s) && (s <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8))
    YF0m.Tfib_zero_shadow
  || existsb (fun c => match zb_avcell c with Some (z, w) => (z <=? s) && (s <? z + Z.of_nat w) | None => false end)
       (YF0m.Tfib_const_abs ++ YF0m.Tfib_const_shadow).
Definition zb_hlo (r : Z * Z) : Z := shadow_addr (fst r) / 8 * 8.
Definition zb_hhi (r : Z * Z) : Z := shadow_addr (fst r + snd r - 1) / 8 * 8 + 8.
Definition zb_hull_ok (r : Z * Z) : bool :=
  forallb (fun i => zb_visb (zb_hlo r + Z.of_nat i)) (seq 0 (Z.to_nat (zb_hhi r - zb_hlo r))).
Definition zb_inb (G : list (Z * Z)) (x : Z) : bool := existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) G.
Lemma zb_inb_ok : forall G x, inG G x -> zb_inb G x = true.
Proof.
  intros G x H. unfold inG in H. apply Exists_exists in H as (r & Hr & Hz). unfold zb_inb. apply existsb_exists.
  exists r. split; [exact Hr|]. unfold in_zr in Hz. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma topx_vis_sound_B : forall ly S Hp (W : world segs) mem md s, ARX ly S Hp W mem md ->
  zb_visb s = true -> aview segs (w_H W) mem s <> None.
Proof.
  intros ly S Hp W mem md s HAR Hv. unfold zb_visb in Hv.
  apply orb_prop in Hv as [Hv|Hv].
  - apply existsb_exists in Hv as (r & Hin & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    assert (Hz : In r (zero_shadow_ranges TfibB ly)) by (right; exact Hin).
    pose proof (alx_zshadow _ _ _ topx_ARX_laws_B ly S Hp W mem md r HAR Hz) as Hr. unfold zero_shadow in Hr.
    specialize (Hr (s - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)).
    replace (shadow_of_addr SHADOW_OFF (fst r) + (s - shadow_of_addr SHADOW_OFF (fst r))) with s in Hr by lia.
    rewrite Hr. discriminate.
  - apply existsb_exists in Hv as (c & Hin & Hb).
    destruct (zb_avcell c) as [[z w]|] eqn:Ec; [|discriminate Hb].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (zb_avcell_ok c z w Ec) as (e & ->).
    pose proof (alx_const_cells _ _ _ topx_ARX_laws_B ly S Hp W mem md HAR) as HCH.
    pose proof (proj1 (Forall_forall _ _) HCH (ACell (ANum z) w (AV e))
      ltac:(cbn [as_const TfibB]; unfold YF0m.Tfib_const; apply in_or_app; right; exact Hin)) as Hh.
    unfold cell_holds in Hh. cbn [c_at c_w c_val aeval] in Hh.
    specialize (Hh (Z.to_nat (s - z)) ltac:(lia)). rewrite Z2Nat.id in Hh by lia.
    replace (z + (s - z)) with s in Hh by lia. rewrite Hh. discriminate.
Qed.

Lemma topx_GSHV_x_B : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG W_LLVMFuzzerTestOneInput_pro.pro_G x) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
  intros ly S Hp W mem md a n HAR Hn Hx.
  pose proof (Hx a ltac:(lia)) as Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hend : a + n <= fst r + snd r).
  { destruct (Z_le_gt_dec (a + n) (fst r + snd r)) as [H|H]; [exact H|]. exfalso.
    pose proof (Hx (fst r + snd r) ltac:(lia)) as Hb.
    assert (Hgap : forallb (fun r => negb (zb_inb W_LLVMFuzzerTestOneInput_pro.pro_G (fst r + snd r)))
      W_LLVMFuzzerTestOneInput_pro.pro_G = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hgap. specialize (Hgap r Hr).
    rewrite (zb_inb_ok _ _ Hb) in Hgap. discriminate Hgap. }
  assert (Hhull : forallb zb_hull_ok W_LLVMFuzzerTestOneInput_pro.pro_G = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hhull. specialize (Hhull r Hr).
  unfold zb_hull_ok in Hhull. rewrite forallb_forall in Hhull.
  unfold shadow_hull_vis. intros s Hs.
  assert (Hlo : zb_hlo r <= s < zb_hhi r).
  { unfold zb_hlo, zb_hhi, shadow_addr in *.
    assert (D1 : fst r / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (a + n - 1) / 8 <= (fst r + snd r - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (M1 : (SHADOW_OFF + fst r / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (SHADOW_OFF + (a + n - 1) / 8) / 8 <= (SHADOW_OFF + (fst r + snd r - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia. }
  pose proof (Hhull (Z.to_nat (s - zb_hlo r)) ltac:(apply in_seq; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia.
  replace (zb_hlo r + (s - zb_hlo r)) with s in Hv by lia.
  exact (topx_vis_sound_B ly S Hp W mem md s HAR Hv).
Qed.

(* ================================================================ FP_SINK *)
Section fp.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Lemma topx_FP_SINK_B : forall cx Hp,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP (G_fr_c TfibB) ARX cx Hp ->
  ~ YI16.sink_open_fp (lf_FP YCfn_cf.fr_FP_b cx).
Proof.
  intros cx Hp [_ HPRE].
  destruct HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HINC) & _).
  destruct HAFN as (HAR & _).
  assert (HLIVE : forall p n, In (p, n) (fr_hblks (c_W cx) (c_mem cx)) -> 4096 <= p).
  { intros p n Hin. pose proof (HINC (p, n) Hin) as Hb.
    exact (proj1 (proj2 (alx_blocks _ _ _ topx_ARX_laws_B _ _ _ _ _ _ p n HAR Hb))). }
  (* fr_FP_b reads the globals by fr_globals_b, fr_hblks by fr_RG: the same addresses *)
  assert (ES : rg_src fr_globals_b = rg_src fr_RG) by reflexivity.
  assert (EO : rg_out fr_globals_b = rg_out fr_RG) by reflexivity.
  assert (EC : rg_capout fr_globals_b = rg_capout fr_RG) by reflexivity.
  unfold fr_hblks in HLIVE. cbv zeta in HLIVE.
  unfold YI16.sink_open_fp, YI16.in_fp, lf_FP, YCfn_cf.fr_FP_b. cbv beta zeta. rewrite ES, EO, EC.
  intros (r & Hr & Hlo & _). revert Hlo. apply in_app_or in Hr as [Hr|Hr]; revert Hr.
  - match goal with |- context [rdword ?v (rg_src fr_RG)] =>
      destruct (rdword v (rg_src fr_RG)) as [G|] eqn:EG end; cbv beta iota; [|cbn [In]; intros []].
    destruct (G =? 0) eqn:EG0; cbv beta iota; cbn [In]; [intros []|]. intros [<- | []]. cbn [fst]. intros Hlo.
    assert (H4 : 4096 <= G).
    { apply (HLIVE G ATABLE). apply in_or_app. left. cbv beta iota. try rewrite EG. try rewrite EG0. cbv beta iota.
      apply in_eq. }
    lia.
  - match goal with |- context [rdword ?v (rg_out fr_RG)] =>
      destruct (rdword v (rg_out fr_RG)) as [o|] eqn:EOo end; cbv beta iota; [|cbn [In]; intros []].
    match goal with |- context [rdword ?v (rg_capout fr_RG)] =>
      destruct (rdword v (rg_capout fr_RG)) as [c|] eqn:ECc end; cbv beta iota; [|cbn [In]; intros []].
    destruct (c =? 0) eqn:EC0; cbv beta iota; cbn [In]; [intros []|]. intros [<- | []]. cbn [fst]. intros Hlo.
    assert (H4 : 4096 <= o).
    { apply (HLIVE o c). apply in_or_app. right. cbv beta iota. try rewrite EOo. try rewrite ECc. try rewrite EC0.
      cbv beta iota. apply in_eq. }
    lia.
Qed.
End fp.

(* ================================================================ HGOTG_x *)
Lemma topx_HGOTG_x_B : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) W_sites.FR_GOT_GUARD = Some W_sites.FR_GUARD.
Proof.
  intros ly S Hp W mem md HAR.
  pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ topx_ARX_laws_B ly S Hp W mem md HAR) _
    (YE22.canary_cell_in TfibB TfibB_syms ly)) as C.
  unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
  unfold YE22.A_GOT_CANARY, YE22.V_GOT_CANARY in C.
  pose proof (C 0%nat ltac:(lia)) as C0. pose proof (C 1%nat ltac:(lia)) as C1.
  pose proof (C 2%nat ltac:(lia)) as C2. pose proof (C 3%nat ltac:(lia)) as C3.
  pose proof (C 4%nat ltac:(lia)) as C4. pose proof (C 5%nat ltac:(lia)) as C5.
  pose proof (C 6%nat ltac:(lia)) as C6. pose proof (C 7%nat ltac:(lia)) as C7.
  change (Z.of_nat 0) with 0 in C0. change (Z.of_nat 1) with 1 in C1. change (Z.of_nat 2) with 2 in C2.
  change (Z.of_nat 3) with 3 in C3. change (Z.of_nat 4) with 4 in C4. change (Z.of_nat 5) with 5 in C5.
  change (Z.of_nat 6) with 6 in C6. change (Z.of_nat 7) with 7 in C7.
  rewrite Z.add_0_r in C0.
  unfold rdword, W_sites.FR_GOT_GUARD, W_sites.FR_GUARD.
  rewrite C0, C1, C2, C3, C4, C5, C6, C7. vm_compute. reflexivity.
Qed.
End topx_image_b.

Print Assumptions topx_GSHV_x_B.
Print Assumptions topx_FP_SINK_B.
Print Assumptions topx_HGOTG_x_B.
