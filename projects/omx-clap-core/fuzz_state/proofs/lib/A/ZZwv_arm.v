(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 32 of its 88 lines of code are new or changed and 1636 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_write_value.v, with its module paths and module names changed; 145 of its 176 lines of code are new or changed and 57 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the two arms wv_arr and wv_obj, with the
   statements a Theorem Labs lane takes as named hypotheses in write_value's closing theorem (FSW_write_value.v, Section W),
   agreed 2026-10-29 and unchanged since (the CTX binder removed by the statement change of 2026-10-29T05:05Z). One
   arm, wvc_arm, covers both containers: it builds the arm instance F from write_value's entry (ZZwv_cont.wvc_F,
   wvc_arm_facts), runs the entry and the opening put (ZZwv_cent.wvc_entry_step), then either the empty container's
   tail put (ZZwv_ctail.wvc_empty_tail) or the first indent (ZZwv_cent.wvc_open_ind_step) and the item loop
   (ZZwv_loop.wvc_loop_arr / _obj).
   Rule 24: proves write_value's two container arms (the lane's lookup for write_value, proof-index v5, CHECKER
   CONFIRM a Theorem Labs lane; record in (internal path)). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_step FSW_write_value
ZZwv_cps ZZwv_cwv ZZwv_ctail ZZwv_cind ZZwv_cput ZZwv_cont ZZwv_cent ZZwv_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
Hypothesis HIMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.

(* a container node's header and shape, out of pj_node *)
Lemma wvc_node_shape : forall (m : word -> option byte) (UL : list (Z * Z)) v t D,
  (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members) ->
  PjStruct.pj_node tfibsegs m (fun a k => In (a, k) UL) v t D ->
  exists num str kids keys n cap0,
    PjStruct.pj_hdr tfibsegs m v (PjTree.tag t) num str kids keys n cap0 /\
    ((exists items, t = PjTree.JArr items /\ n = Z.of_nat (length items) /\ keys = 0 /\ n <= cap0 /\
        (cap0 = 0 /\ kids = 0 \/ 0 < cap0 /\ In (kids, 56 * cap0) UL)) \/
     (exists members, t = PjTree.JObj members /\ n = Z.of_nat (length members) /\ n <= cap0 /\
        (cap0 = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap0 /\ In (kids, 56 * cap0) UL /\ In (keys, 8 * cap0) UL))).
Proof.
intros m UL v t D Ht HN.
destruct Ht as [(items & ->) | (members & ->)]; cbn [PjStruct.pj_node] in HN;
  destruct HN as (_ & _ & num & str & kids & keys & n & cap0 & HH & Hshape);
  exists num, str, kids, keys, n, cap0; split; [exact HH | | exact HH |].
- left. exists items. destruct Hshape as (_ & Ek & En & Hnc & Hcase & _).
  split; [reflexivity|]. split; [exact En|]. split; [exact Ek|]. split; [exact Hnc | exact Hcase].
- right. exists members. destruct Hshape as (_ & En & Hnc & Hcase & _).
  split; [reflexivity|]. split; [exact En|]. split; [exact Hnc | exact Hcase].
Qed.

Theorem wvc_arm : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on B (fun t => (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members)) k.
Proof.
intros k HREC. unfold wv_spec_on.
intros ly St U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail
  Ht Hdep HPRE HHD Hfrl R10 R11 R12 R13 Hp Hd Hdd Hs0 HOUT HGL HU0 Hspo Hoot Hot16 Hottop HCH HPRES HN HPO HUL HD
  HROOT Hplain Hfoot Hroom HcapW Hcapl HBUD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_ARU B _ ly St U W regs mem md ch (proj1 HPRE)) as HARU.
pose proof HPRE as ((HFN & _ & _) & _).
destruct HFN as (_ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (Hal16 & HSTK0 & Hceil & Hslo & _).
(* the node's header and container shape *)
destruct (wvc_node_shape (rdW W mem) UL v t D Ht HN) as (num & str & kids & keys & n & cap0 & HH & HT).
assert (Hty : PjTree.tag t = 5 \/ PjTree.tag t = 6)
  by (destruct Ht as [(items & ->) | (members & ->)]; [left | right]; reflexivity).
(* the word at o - 8 *)
assert (Hosp : spZ regs + 8 <= o)
  by (destruct HCH as [(E & _) | (L & _)]; lia).
destruct (wvc_rdword_present B ly St U W mem md (o - 8) HARU ltac:(intros x Hx; apply HPRES; lia) ltac:(lia)
  ltac:(pose proof HOUT as (_ & _ & Hotop & _); destruct (proj1 HPRE) as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ &
    H47 & _ & _ & Htop2) & _) & _ & _); lia)) as (ra8 & Hra8).
(* the arm instance and the entry facts *)
set (F := wvc_F k regs ot o v pretty d t str kids keys n buf cap failed text live peak cnt fail UL D ra8).
destruct (wvc_arm_facts B k ly St U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail
  num str kids keys n cap0 ra8 HPRE HARU HH HT HUL HOUT HGL Hp Hd Hdd Hspo Hoot Hot16 Hottop Hcapl Hplain Hfrl Hroom
  HBUD Hfoot)
  as (HE_sp16 & HE_ot16 & HE_oot & HE_o8 & HE_top & HE_top47 & HE_lo & HE_gp & HE_tp & HE_cap0 & HE_capl & HE_cnt0 &
      HE_p & HE_d & HE_dd & HE_room & HE_bud & HE_frl & HE_foot & HE_plain & HE_ty & HE_hdr & HE_n & HE_kk).
fold F in HE_sp16, HE_ot16, HE_oot, HE_o8, HE_top, HE_top47, HE_lo, HE_gp, HE_tp, HE_cap0, HE_capl, HE_cnt0,
  HE_p, HE_d, HE_dd, HE_room, HE_bud, HE_frl, HE_foot, HE_plain, HE_ty, HE_hdr, HE_n, HE_kk.
assert (HM : wf_m F = (2 - k)%nat) by reflexivity.
assert (HDEP : (PjTree.depth (wf_t F) <= 2 - k)%nat) by exact Hdep.
assert (HSP0 : spZ regs = wf_sp F) by reflexivity.
assert (HS00 : s0Z regs < alloc_ceiling \/ s0Z regs = wf_o F \/ wf_o F + 48 <= s0Z regs) by exact Hs0.
assert (HPRE0 : fpreU tfibsegs B (STK_write_value (wf_m F)) ly St U W regs mem md ch) by exact HPRE.
(* the post the arm proves is the arm's own wvc_POST *)
change (wv_post B (2 - k) ot o v pretty d t D UL buf cap failed text live peak cnt fail regs ly St U W mem md)
  with (wvc_POST B F ly St U W mem md regs).
(* the entry and the opening put *)
apply (wvc_entry_step B HSS F ly St U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail
  (PjTree.tag t) num str kids keys n cap0 str str k ra8 _ HPUT HIMG eq_refl Hra8 Hty
  (conj HH (conj (Z.le_refl str) (Z.le_refl str)))
  Hdep HPRE HHD Hfrl R10 R11 R12 R13 Hp Hd Hdd Hs0 HOUT HGL HU0 Hspo Hoot Hot16 Hottop HCH HPRES HN HPO HUL HD HROOT
  Hplain Hfoot Hroom HcapW Hcapl HBUD).
intros ly1 S1 U1 W1 regs1 mem1 md1 buf1 HO.
change (cfg_at tfibsegs WVC_R_OPEN regs1 mem1 md1)
  with (mkCfg (mkst regs1 (Z_to_bv 64 WVC_R_OPEN) mem1 (seg_rom tfibsegs)) md1).
destruct (Z.eq_dec (wf_n F) 0) as [Hn0 | Hn0].
- (* the empty container: the tail put of the closing bracket *)
  exact (wvc_empty_tail B F ly St U W mem md regs HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp HE_tp
    HE_cap0 HE_capl HE_cnt0 HE_p HE_room HE_bud HE_frl HE_ty HE_n HE_kk ch ly1 S1 U1 W1 _ md1 buf1
    HIMG HPUT HPRE0 HSP0 HS00 Hn0 HO).
- (* the first indent, then the item loop *)
  destruct HT as [(items & Et & En & _) | (members & Et & En & _)].
  + assert (Et' : wf_t F = PjTree.JArr items) by exact Et.
    assert (Ety : wf_ty F = 5) by (unfold F, wvc_F; cbn [wf_ty]; rewrite Et; reflexivity).
    destruct items as [|u0 items'] eqn:Eitems; [exfalso; apply Hn0; exact En|].
    rewrite <- Eitems in Et', En.
    assert (Hu0 : nth_error items 0 = Some u0) by (rewrite Eitems; reflexivity).
    set (p := negb (wf_p F =? 0)).
    assert (EWP : wvc_WP F = [if wf_ty F =? 6 then [123] else [91]] ++ WriterValue.wind p (wf_d F + 1)
                             ++ (WriterValue.wvpieces u0 p (wf_d F + 1) ++ wvc_rest F 0)).
    { rewrite (wvc_split_arr F items 0 u0 Et' Ety Hu0), (wvc_done_0_arr F items Et' Ety).
      unfold wvc_itemP. rewrite Ety. cbn [Z.eqb Pos.eqb]. rewrite <- ?app_assoc. reflexivity. }
    apply (wvc_open_ind_step B HSS F ly St U W mem md regs HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp
      HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk
      (WriterValue.wvpieces u0 p (wf_d F + 1) ++ wvc_rest F 0) ly1 S1 U1 W1 _ md1 buf1 _ HIND EWP HO Hn0).
    intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 key2 HI.
    change (cfg_at tfibsegs WVC_R_IND regs2 mem2 md2)
      with (mkCfg (mkst regs2 (Z_to_bv 64 WVC_R_IND) mem2 (seg_rom tfibsegs)) md2).
    apply (wvc_loop_arr B HSS F ly St U W mem md regs HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp HE_tp
      HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_foot HE_plain HE_ty HE_hdr HE_n HE_kk
      HPUT HIND HIMG k HREC HM HDEP ch HPRE0 HSP0 HS00 items (length items - 1) 0 key2 ly2 S2 U2 W2 _ md2 buf2
      Et' ltac:(rewrite Eitems; cbn [length]; lia)).
    rewrite (wvc_done_0_arr F items Et' Ety).
    replace (wf_keys F + 8 * Z.of_nat 0) with (wf_keys F) by lia.
    rewrite Ety in HI. cbn [Z.eqb Pos.eqb] in HI. exact HI.
  + assert (Et' : wf_t F = PjTree.JObj members) by exact Et.
    assert (Ety : wf_ty F = 6) by (unfold F, wvc_F; cbn [wf_ty]; rewrite Et; reflexivity).
    destruct members as [|[nm0 u0] members'] eqn:Emem; [exfalso; apply Hn0; exact En|].
    rewrite <- Emem in Et', En.
    assert (Hu0 : nth_error members 0 = Some (nm0, u0)) by (rewrite Emem; reflexivity).
    set (p := negb (wf_p F =? 0)).
    assert (EWP : wvc_WP F = [if wf_ty F =? 6 then [123] else [91]] ++ WriterValue.wind p (wf_d F + 1)
                             ++ (wvc_itemP F nm0 u0 ++ wvc_rest F 0)).
    { rewrite (wvc_split_obj F members 0 nm0 u0 Et' Ety Hu0), (wvc_done_0_obj F members Et' Ety).
      rewrite Ety. cbn [Z.eqb Pos.eqb]. rewrite <- ?app_assoc. reflexivity. }
    apply (wvc_open_ind_step B HSS F ly St U W mem md regs HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp
      HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk
      (wvc_itemP F nm0 u0 ++ wvc_rest F 0) ly1 S1 U1 W1 _ md1 buf1 _ HIND EWP HO Hn0).
    intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 key2 HI.
    change (cfg_at tfibsegs WVC_R_IND regs2 mem2 md2)
      with (mkCfg (mkst regs2 (Z_to_bv 64 WVC_R_IND) mem2 (seg_rom tfibsegs)) md2).
    apply (wvc_loop_obj B HSS F ly St U W mem md regs HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo HE_gp HE_tp
      HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_foot HE_plain HE_ty HE_hdr HE_n HE_kk
      HPUT HIND HPS HIMG k HREC HM HDEP ch HPRE0 HSP0 HS00 members (length members - 1) 0 key2 ly2 S2 U2 W2 _ md2 buf2
      Et' ltac:(rewrite Emem; cbn [length]; lia)).
    rewrite (wvc_done_0_obj F members Et' Ety).
    replace (wf_keys F + 8 * Z.of_nat 0) with (wf_keys F) by lia.
    rewrite Ety in HI. cbn [Z.eqb Pos.eqb] in HI. exact HI.
Qed.

(* ================= the two arms, in the agreed text ================= *)
Theorem wv_arr_holds : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on B (fun t => exists items, t = PjTree.JArr items) k.
Proof.
intros k IH.
apply (wvc_spec_on_mono B _
  (fun t => (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members)) k);
  [intros t Ht; left; exact Ht | exact (wvc_arm k IH)].
Qed.

Theorem wv_obj_holds : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on B (fun t => exists members, t = PjTree.JObj members) k.
Proof.
intros k IH.
apply (wvc_spec_on_mono B _
  (fun t => (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members)) k);
  [intros t Ht; right; exact Ht | exact (wvc_arm k IH)].
Qed.

End W.

(* ================= write_value, every level, with the container arms discharged ================= *)
(* FSW_write_value.write_value_holds with its two named hypotheses wv_arr / wv_obj replaced by the arms proved here;
   what remains are the callees' specs and the image / runtime facts, each owned elsewhere *)
Theorem write_value_spec_holds {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) :
  FsShadowSyms B -> fs_img_facts tfibsegs B ->
  put_spec B tfibsegs -> indent_spec B tfibsegs -> put_string_spec B tfibsegs ->
  astrlen_realizesU tfibsegs B PC_strlen ->
  forall k, write_value_spec_at B tfibsegs k.
Proof.
intros HSS HIMG HPUT HIND HPS HSLEN.
exact (write_value_holds B HSS HIMG HPUT HPS (wv_arr_holds B HSS HIMG HPUT HIND HPS)
  (wv_obj_holds B HSS HIMG HPUT HIND HPS) HSLEN).
Qed.
