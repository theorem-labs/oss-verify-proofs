(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: group IMAGE of A top_x's hypotheses (TOPX-OWNERS.md (sha256 bb821fae800d; internal record);
   W_LLVMFuzzerTestOneInput_top_x.v, line numbers at integ b4343cabfa9): six image facts, each stated as the top_x
   Section hypothesis at the instance ARX := ARcf (cp := CfParams_reply) segs TfibB /\ Hp = [] (lib/A/W_LLVMFuzzerTestOneInput_top_x.v Definition
   ARX, written here as the same relation, as W_shadow_pin_x.v's ashp_str2_1_fr_cf does), B := TfibB, CfParams_reply:
     topx_GSHV_x     top_x.v:210 GSHV_x      ad_G's shadow hulls are visible (lib/A/W_LLVMFuzzerTestOneInput_addI.v zz_GSHV over ARX)
     topx_TLF        top_x.v:326 TLF         PALibF TfibB (W_frame.v:175), decided over TfibB (AD2l.v)
     topx_XE_LIT_S_x top_x.v:451 XE_LIT_S_x  "" (.str.2, AX_lit_empty = A_OBJ 28): W_shadow_pin_x.v ashp_str2_1_fr_cf
     topx_FP_SINK    top_x.v:475 FP_SINK     at fr_FP := ACfn_cf.fr_FP, the driver's footprint
     topx_HGOTG_x    top_x.v:561 HGOTG_x     the GOT word 0x9e658 holds &__stack_chk_guard = 0x5f94b0
     topx_GN_LITS_x  top_x.v:563 GN_LITS_x   snprintf's two literals (A_OBJ 20, 7 bytes; A_OBJ 21, 14 bytes)
   What ARX gives: only its AR_laws_x (YCbqG.v), as lib/A/W_LLVMFuzzerTestOneInput_top_x.v's ARX_laws builds them (AR_laws_x_and_hp over
   AR_laws_x_cf / AR_laws_ok_cf; restated here as topx_ARX_laws, since this file must not Require top_x, which takes
   these lemmas): alx_const_cells (every cell of as_const TfibB ly = AF0m.Tfib_const ly holds), alx_zshadow (every
   range of zero_shadow_ranges TfibB ly reads 0) and alx_blocks (a live block starts at or above 4096).
   FP_SINK: top_x keeps fr_FP a Variable; the driver instantiates it with ACfn_cf.v's fr_FP (a Theorem Labs lane's file; the
   COMPOSE-A file ReplyATopX.v states FP_SINK at `Local Notation fr_FP := ACfn_cf.fr_FP`), and this lemma names that
   definition.  The footprint is g_src's table (G, G + ATABLE) when g_src reads G <> 0 and g_out's buffer (o, o + c)
   when g_capout reads c <> 0; both are harness blocks (cut.v fr_hblks), which the pre's HB clause (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:103) makes
   live blocks, so each range starts at or above 4096 and none holds address 0 (YI16.v:71 sink_open_fp FP :=
   in_fp FP 0).
   SATISFIABILITY (VERIFY rule 10), at the real instance: ARX holds at the start-up hand-off state - the driver's
   AD1pcf.v:145-146 (tfib_drv_main; B := TfibB by ReplyTFIBcf.v:47, cp := CfParams_reply by ReplyDriverCf.v's
   reply_tfib_of_top_x_triv) proves ARcf TSEGS B ly init_state [] W1 FULL model by Reusable/YGcfNilInit.v:41
   ARcf_nil_init from the start-up AR, with Hp = [] - so the ARX premise of GSHV_x, XE_LIT_S_x (inside ashp_x),
   HGOTG_x and GN_LITS_x is met there; GSHV_x's other premises hold at a := 0x5d88e0 (g_s), n := 384, ad_G's first
   range, the use top_x.v:673 makes.  FP_SINK's BASEx is the driver's pre at every call at the driver's meter
   ameter_triv (mo_ok := True) (ReplyDriverCf.v fr_pre_bridge: the driver's pre is fr_lib_pre_cf_x at ARX, LIBROOM,
   NP, HB included), and at the first call fr_hblks = [] (cut.v:225 fr_hblks_nil: g_src and g_capout read 0).
   TLF has no premise.
   proves no function (kind: image facts of the instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v YI04 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0l AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites AE22 W_shadow_pin_x W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_addI W_LLVMFuzzerTestOneInput_exit.
(* the driver's footprint fr_FP (a Theorem Labs lane's ACfn_cf.v), cited qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
(* the zify flag as this file's proofs expect it, whatever a Required file leaves (YCbqG / W_contract_x Require
   FCiface; cut_x.v:55's form) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section topx_image.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* top_x.v:131 Definition ARX, the same relation *)
#[local] Notation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []).

(* top_x.v:133 ARX_laws, restated (same proof) *)
Lemma topx_ARX_laws : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof.
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* ================================================================ GSHV_x (top_x.v:210) *)
(* lib/A/W_LLVMFuzzerTestOneInput_addI.v:160 zz_vis_sound over ARX: AR's am_zshadow / am_const are the laws' alx_zshadow / alx_const_cells *)
Lemma topx_vis_sound : forall ly S Hp (W : world segs) mem md s, ARX ly S Hp W mem md ->
  W_LLVMFuzzerTestOneInput_addI.zz_visb s = true -> aview segs (w_H W) mem s <> None.
Proof.
  intros ly S Hp W mem md s HAR Hv. unfold W_LLVMFuzzerTestOneInput_addI.zz_visb in Hv.
  apply orb_prop in Hv as [Hv|Hv].
  - apply existsb_exists in Hv as (r & Hin & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    assert (Hz : In r (zero_shadow_ranges TfibB ly)) by (right; exact Hin).
    pose proof (alx_zshadow _ _ _ topx_ARX_laws ly S Hp W mem md r HAR Hz) as Hr. unfold zero_shadow in Hr.
    specialize (Hr (s - shadow_of_addr SHADOW_OFF (fst r)) ltac:(lia)).
    replace (shadow_of_addr SHADOW_OFF (fst r) + (s - shadow_of_addr SHADOW_OFF (fst r))) with s in Hr by lia.
    rewrite Hr. discriminate.
  - apply existsb_exists in Hv as (c & Hin & Hb).
    destruct (W_LLVMFuzzerTestOneInput_addI.zz_avcell c) as [[z w]|] eqn:Ec; [|discriminate Hb].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (W_LLVMFuzzerTestOneInput_addI.zz_avcell_ok c z w Ec) as (e & ->).
    pose proof (alx_const_cells _ _ _ topx_ARX_laws ly S Hp W mem md HAR) as HCH.
    pose proof (proj1 (Forall_forall _ _) HCH (ACell (ANum z) w (AV e))
      ltac:(cbn [as_const TfibB]; unfold AF0m.Tfib_const; apply in_or_app; right; exact Hin)) as Hh.
    unfold cell_holds in Hh. cbn [c_at c_w c_val aeval] in Hh.
    specialize (Hh (Z.to_nat (s - z)) ltac:(lia)). rewrite Z2Nat.id in Hh by lia.
    replace (z + (s - z)) with s in Hh by lia. rewrite Hh. discriminate.
Qed.

(* lib/A/W_LLVMFuzzerTestOneInput_addI.v:192 zz_GSHV over ARX, at top_x's ad_G (W_LLVMFuzzerTestOneInput_add_x.ad_G, the one top_x imports last;
   its text is _add.v's) *)
Lemma topx_GSHV_x : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG W_LLVMFuzzerTestOneInput_add_x.ad_G x) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
  intros ly S Hp W mem md a n HAR Hn Hx.
  pose proof (Hx a ltac:(lia)) as Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hend : a + n <= fst r + snd r).
  { destruct (Z_le_gt_dec (a + n) (fst r + snd r)) as [H|H]; [exact H|]. exfalso.
    pose proof (Hx (fst r + snd r) ltac:(lia)) as Hb.
    assert (Hgap : forallb (fun r => negb (W_LLVMFuzzerTestOneInput_addI.zz_inb W_LLVMFuzzerTestOneInput_add_x.ad_G
      (fst r + snd r))) W_LLVMFuzzerTestOneInput_add_x.ad_G = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hgap. specialize (Hgap r Hr).
    rewrite (W_LLVMFuzzerTestOneInput_addI.zz_inb_ok _ _ Hb) in Hgap. discriminate Hgap. }
  assert (Hhull : forallb W_LLVMFuzzerTestOneInput_addI.zz_hull_ok W_LLVMFuzzerTestOneInput_add_x.ad_G = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hhull. specialize (Hhull r Hr).
  unfold W_LLVMFuzzerTestOneInput_addI.zz_hull_ok in Hhull. rewrite forallb_forall in Hhull.
  unfold shadow_hull_vis. intros s Hs.
  assert (Hlo : W_LLVMFuzzerTestOneInput_addI.zz_hlo r <= s < W_LLVMFuzzerTestOneInput_addI.zz_hhi r).
  { unfold W_LLVMFuzzerTestOneInput_addI.zz_hlo, W_LLVMFuzzerTestOneInput_addI.zz_hhi, shadow_addr in *.
    assert (D1 : fst r / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (a + n - 1) / 8 <= (fst r + snd r - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (M1 : (SHADOW_OFF + fst r / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia).
    assert (M2 : (SHADOW_OFF + (a + n - 1) / 8) / 8 <= (SHADOW_OFF + (fst r + snd r - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia. }
  pose proof (Hhull (Z.to_nat (s - W_LLVMFuzzerTestOneInput_addI.zz_hlo r)) ltac:(apply in_seq; lia)) as Hv.
  rewrite Z2Nat.id in Hv by lia.
  replace (W_LLVMFuzzerTestOneInput_addI.zz_hlo r + (s - W_LLVMFuzzerTestOneInput_addI.zz_hlo r)) with s in Hv by lia.
  exact (topx_vis_sound ly S Hp W mem md s HAR Hv).
Qed.

(* ================================================================ TLF (top_x.v:326) *)
(* PALibF's six fields at TfibB (AD2l.v): the GOT slot of the use-after-return word is A_OBJ 1 = 0x9da28, the word
   0xa60c0 lies in [0x10000, 0x5fb000) and is 4-aligned, __asan_stack_malloc_0 / _1 are 0x3d168 / 0x3d2dc in both
   the placement (W_place.v) and Tfib_code (AF0l.v:13), and the four cells 0x9d9d0 / 0x9da28 / 0xa60b8 (8 bytes
   each) and 0xa60c0 (4 bytes) are pairwise apart *)
Lemma topx_TLF : PALibF TfibB.
Proof.
  constructor.
  - vm_compute. reflexivity.
  - cbn [as_uar_cell TfibB]. lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - cbn [zseps zseps_from fst snd].
    repeat split; first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.

(* ================================================================ XE_LIT_S_x (top_x.v:451) *)
(* AX_lit_empty is A_OBJ 28 (_exit.v:97), .str.2 "" at 0x20ee0: W_shadow_pin_x.v:139 at the same relation *)
Lemma topx_XE_LIT_S_x : ashp_x ARX (VAL W_LLVMFuzzerTestOneInput_exit.AX_lit_empty) 1.
Proof. exact W_shadow_pin_x.ashp_str2_1_fr_cf. Qed.

(* ================================================================ FP_SINK (top_x.v:475) *)
Section fp.
(* top_x.v:149-156's Variables that BASEx names; the lemma holds for each of them *)
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Lemma topx_FP_SINK : forall cx Hp,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP (G_fr_c TfibB) ARX cx Hp ->
  ~ YI16.sink_open_fp (lf_FP ACfn_cf.fr_FP cx).
Proof.
  intros cx Hp [_ HPRE].
  (* fr_lib_pre_cf_x's HB is its 21st conjunct; XCNT and CAPOUT follow it on the room line *)
  destruct HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HINC) & _).
  destruct HAFN as (HAR & _).
  (* a harness block starts at or above 4096 (alx_blocks) *)
  assert (HLIVE : forall p n, In (p, n) (fr_hblks (c_W cx) (c_mem cx)) -> 4096 <= p).
  { intros p n Hin. pose proof (HINC (p, n) Hin) as Hb.
    exact (proj1 (proj2 (alx_blocks _ _ _ topx_ARX_laws _ _ _ _ _ _ p n HAR Hb))). }
  unfold fr_hblks, fr_RG in HLIVE. cbv zeta in HLIVE.
  unfold YI16.sink_open_fp, YI16.in_fp, lf_FP, ACfn_cf.fr_FP. cbv beta zeta.
  intros (r & Hr & Hlo & _). revert Hlo. apply in_app_or in Hr as [Hr|Hr]; revert Hr.
  (* the reads are taken from the goal itself: fr_FP's view is at world tfibsegs, so its implicit arguments are not
     the ones a re-typed `aview .. (c_W cx) ..` would get *)
  - match goal with |- context [rdword ?v (rg_src fr_globals)] =>
      destruct (rdword v (rg_src fr_globals)) as [G|] eqn:EG end; cbv beta iota; [|cbn [In]; intros []].
    destruct (G =? 0) eqn:EG0; cbv beta iota; cbn [In]; [intros []|]. intros [<- | []]. cbn [fst]. intros Hlo.
    assert (H4 : 4096 <= G).
    { (* the destructs above also rewrote HLIVE's reads, which are the same terms *)
      apply (HLIVE G ATABLE). apply in_or_app. left. cbv beta iota. try rewrite EG0. cbv beta iota. apply in_eq. }
    lia.
  - match goal with |- context [rdword ?v (rg_out fr_globals)] =>
      destruct (rdword v (rg_out fr_globals)) as [o|] eqn:EO end; cbv beta iota; [|cbn [In]; intros []].
    match goal with |- context [rdword ?v (rg_capout fr_globals)] =>
      destruct (rdword v (rg_capout fr_globals)) as [c|] eqn:EC end; cbv beta iota; [|cbn [In]; intros []].
    destruct (c =? 0) eqn:EC0; cbv beta iota; cbn [In]; [intros []|]. intros [<- | []]. cbn [fst]. intros Hlo.
    assert (H4 : 4096 <= o).
    { apply (HLIVE o c). apply in_or_app. right. cbv beta iota. try rewrite EC0. cbv beta iota. apply in_eq. }
    lia.
Qed.
End fp.

(* ================================================================ HGOTG_x (top_x.v:561) *)
(* the const cell z8 0x9e658 0x5f94b0 of AF0m.Tfib_const_abs (AE22.v:34 canary_cell_in), held by alx_const_cells *)
Lemma topx_HGOTG_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) W_sites.FR_GOT_GUARD = Some W_sites.FR_GUARD.
Proof.
  intros ly S Hp W mem md HAR.
  pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ topx_ARX_laws ly S Hp W mem md HAR) _
    (AE22.canary_cell_in TfibB TfibB_syms ly)) as C.
  unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
  unfold AE22.A_GOT_CANARY, AE22.V_GOT_CANARY in C.
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

(* ================================================================ GN_LITS_x (top_x.v:563) *)
(* the two .rodata literals snprintf checks: .str.8 "%s %d " (A_OBJ 20, 0x20f80, 7 bytes with the NUL; shadow
   0x7fffc1f0 = 7) and .str.5 "param_gesture" (A_OBJ 21, 0x20f20, 14 bytes; shadow 0x7fffc1e4 = 0 in the zero-shadow
   range (0x20f20, 8), 0x7fffc1e5 = 6); both checks decided over AF0m's tables by W_shadow_pin_x.v:95 tfib_shp_x *)
Lemma topx_GN_LITS_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14.
Proof.
  intros ly S Hp W mem md HAR.
  assert (H20 : ashp_x ARX (VAL (A_OBJ 20)) 7).
  { apply (W_shadow_pin_x.tfib_shp_x TfibB TfibB_syms _ topx_ARX_laws). vm_compute. reflexivity. }
  assert (H21 : ashp_x ARX (VAL (A_OBJ 21)) 14).
  { apply (W_shadow_pin_x.tfib_shp_x TfibB TfibB_syms _ topx_ARX_laws). vm_compute. reflexivity. }
  destruct (H20 ly S Hp W mem md HAR) as [A20 V20]. destruct (H21 ly S Hp W mem md HAR) as [A21 V21].
  split; [exact A20|]. split; [apply V20; lia|]. split; [exact A21|]. apply V21; lia.
Qed.
End topx_image.
