(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cent.v, with its module names changed; 193 of its 257 lines of code are new or changed and 525 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the ITEM LOOP. From the loop invariant at
   the first item's indent return (WVC_R_IND, item i, the pieces wvc_done F i written), the arm runs item by item -
   the value (array: wvc_ind_item; object: wvc_ind_key, wvc_key_sep, wvc_sep_item), then either the comma and the
   next indent (wvc_item_comma, wvc_comma_ind) or the closing indent and the tail put (wvc_item_close,
   wvc_close_tail) - to write_value's post. Induction on the number of items left.
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
ZZwv_cps ZZwv_cwv ZZwv_ctail ZZwv_cind ZZwv_cput ZZwv_cont.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* the arm's callees and its own level *)
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIMG : fs_img_facts tfibsegs B.
Variable k : nat.
Hypothesis HREC : (k < 2)%nat -> write_value_spec_at B tfibsegs (S k).
Hypothesis HM : wf_m F = (2 - k)%nat.
Hypothesis HDEP : (PjTree.depth (wf_t F) <= 2 - k)%nat.
(* the arm's entry, as write_value_spec_at gives it *)
Variable ch0 : list (Z * Z * Z).
Hypothesis HPRE0 : fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0.
Hypothesis HSP0 : spZ regs0 = wf_sp F.
Hypothesis HS00 : s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0.

(* the part steps, with this Section's instance applied *)
Let ind_item := wvc_ind_item B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_foot HE_plain HE_ty HE_hdr HE_n HE_kk.
Let sep_item := wvc_sep_item B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_foot HE_plain HE_ty HE_hdr HE_n HE_kk.
Let ind_key := wvc_ind_key B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_plain HE_ty HE_hdr HE_n HE_kk.
Let comma_ind := wvc_comma_ind B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk.
Let item_close := wvc_item_close B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk.
Let key_sep := wvc_key_sep B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk.
Let item_comma := wvc_item_comma B HSS F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_d HE_dd HE_room HE_bud HE_frl HE_ty HE_hdr HE_n HE_kk.
Let close_tail := wvc_close_tail B F ly0 S0 U0 W0 mem0 md0 regs0 HE_sp16 HE_ot16 HE_oot HE_o8 HE_top HE_top47 HE_lo
  HE_gp HE_tp HE_cap0 HE_capl HE_cnt0 HE_p HE_room HE_bud HE_frl HE_ty HE_n HE_kk.

(* the arm's post *)
Definition wvc_POST : world tfibsegs -> config -> Prop :=
  FSW_write_value.wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
    (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
    regs0 ly0 S0 U0 W0 mem0 md0.

(* the tree's type and the item count, from the entry facts *)
Lemma wvl_arr : forall items, wf_t F = PjTree.JArr items -> wf_ty F = 5 /\ wf_n F = Z.of_nat (length items).
Proof.
intros items Et. pose proof HE_ty as HTY. destruct HTY as [(Ety & items' & Et' & En & _) | (Ety & members & Et' & _)];
  rewrite Et in Et'; [injection Et' as E; rewrite <- E in En; split; [exact Ety | exact En] | discriminate].
Qed.

Lemma wvl_obj : forall members, wf_t F = PjTree.JObj members ->
  wf_ty F = 6 /\ wf_n F = Z.of_nat (length members).
Proof.
intros members Et. pose proof HE_ty as HTY. destruct HTY as [(Ety & items & Et' & _) | (Ety & members' & Et' & En)];
  rewrite Et in Et'; [discriminate | injection Et' as E; rewrite <- E in En; split; [exact Ety | exact En]].
Qed.

Lemma wvl_nth : forall {X : Type} (l : list X) i, (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|].
apply nth_error_None in E. lia.
Qed.

(* ================= the ARRAY loop ================= *)
Lemma wvc_loop_arr : forall items (j i : nat) key ly St U (W : world tfibsegs) ms mdc buf,
  wf_t F = PjTree.JArr items -> length items = (i + S j)%nat ->
  wvc_inv B F WVC_R_IND (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key (wvc_done F i)
    ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly St U buf ->
  SRr tfibsegs W (mkCfg ms mdc) wvc_POST.
Proof.
intros items j. induction j as [|j IH]; intros i key ly St U W ms mdc buf Et Hlen HINV.
all: destruct (wvl_arr items Et) as (Ety & En).
all: destruct (wvl_nth items i ltac:(lia)) as (u & Hu).
all: set (p := negb (wf_p F =? 0)).
all: set (PU := WriterValue.wvpieces u p (wf_d F + 1)).
all: assert (ESP : wvc_WP F = wvc_done F i ++ PU ++ wvc_rest F i)
       by (rewrite (wvc_split_arr F items i u Et Ety Hu); unfold wvc_itemP; rewrite Ety; reflexivity).
all: assert (Hu' : nth_error items (Z.to_nat (Z.of_nat i)) = Some u) by (rewrite Nat2Z.id; exact Hu).
all: apply (ind_item k (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key (wvc_done F i) (wvc_rest F i) items u
       ly St U W ms mdc buf wvc_POST HREC HM ESP HINV HDEP Et Hu').
all: intros ly1 S1 U1 W1 regs1 mem1 md1 buf1 key1 HINV1.
all: change (cfg_at tfibsegs WVC_R_ITEM regs1 mem1 md1)
       with (mkCfg (mkst regs1 (Z_to_bv 64 WVC_R_ITEM) mem1 (seg_rom tfibsegs)) md1).
- (* the last item: the closing indent, then the tail put of ']' *)
  assert (ERL : wvc_rest F i = WriterValue.wind p (wf_d F) ++ [[93]])
    by exact (wvc_rest_last_arr F items i Et ltac:(lia)).
  assert (EWP : wvc_WP F = (wvc_done F i ++ PU) ++ WriterValue.wind p (wf_d F) ++ [[93]])
    by (rewrite ESP, ERL, <- ?app_assoc; reflexivity).
  apply (item_close (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key1 (wvc_done F i ++ PU) [[93]]
    ly1 S1 U1 W1 (mkst regs1 (Z_to_bv 64 WVC_R_ITEM) mem1 (seg_rom tfibsegs)) md1 buf1 wvc_POST HIND
    EWP HINV1 ltac:(lia)).
  intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 HC.
  change (cfg_at tfibsegs WVC_R_CLOSE regs2 mem2 md2)
    with (mkCfg (mkst regs2 (Z_to_bv 64 WVC_R_CLOSE) mem2 (seg_rom tfibsegs)) md2).
  assert (EWP2 : wvc_WP F = ((wvc_done F i ++ PU) ++ WriterValue.wind p (wf_d F))
                            ++ [if wf_ty F =? 6 then [125] else [93]])
    by (rewrite Ety, EWP, <- ?app_assoc; reflexivity).
  exact (close_tail ch0 _ ly2 S2 U2 W2 _ md2 buf2 HIMG HPUT HPRE0 HSP0 HS00 EWP2 HC).
- (* another item follows: the comma, the next indent, and the loop *)
  destruct (wvl_nth items (S i) ltac:(lia)) as (u2 & Hu2).
  set (PU2 := WriterValue.wvpieces u2 p (wf_d F + 1)).
  assert (ERS : wvc_rest F i = [[44]] ++ WriterValue.wind p (wf_d F + 1) ++ PU2 ++ wvc_rest F (S i))
    by (rewrite (wvc_rest_step_arr F items i u2 Et Ety Hu2), wv_comma_S; unfold wvc_itemP; rewrite Ety;
        reflexivity).
  assert (EWP : wvc_WP F = (wvc_done F i ++ PU) ++ [[44]]
                           ++ (WriterValue.wind p (wf_d F + 1) ++ PU2 ++ wvc_rest F (S i)))
    by (rewrite ESP, ERS, <- ?app_assoc; reflexivity).
  apply (item_comma (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key1 (wvc_done F i ++ PU)
    (WriterValue.wind p (wf_d F + 1) ++ PU2 ++ wvc_rest F (S i))
    ly1 S1 U1 W1 (mkst regs1 (Z_to_bv 64 WVC_R_ITEM) mem1 (seg_rom tfibsegs)) md1 buf1 wvc_POST HPUT HIMG
    ltac:(lia) EWP HINV1).
  intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 key2 HINV2.
  change (cfg_at tfibsegs WVC_R_COMMA regs2 mem2 md2)
    with (mkCfg (mkst regs2 (Z_to_bv 64 WVC_R_COMMA) mem2 (seg_rom tfibsegs)) md2).
  assert (EWP2 : wvc_WP F = ((wvc_done F i ++ PU) ++ [[44]]) ++ WriterValue.wind p (wf_d F + 1)
                            ++ (PU2 ++ wvc_rest F (S i)))
    by (rewrite EWP, <- ?app_assoc; reflexivity).
  apply (comma_ind (Z.of_nat i + 1) (wf_keys F + 8 * (Z.of_nat i + 1)) key2 ((wvc_done F i ++ PU) ++ [[44]])
    (PU2 ++ wvc_rest F (S i)) ly2 S2 U2 W2 (mkst regs2 (Z_to_bv 64 WVC_R_COMMA) mem2 (seg_rom tfibsegs)) md2 buf2
    wvc_POST HIND EWP2 HINV2).
  intros ly3 S3 U3 W3 regs3 mem3 md3 buf3 key3 HINV3.
  change (cfg_at tfibsegs WVC_R_IND regs3 mem3 md3)
    with (mkCfg (mkst regs3 (Z_to_bv 64 WVC_R_IND) mem3 (seg_rom tfibsegs)) md3).
  assert (EDN : wvc_done F (S i) = ((wvc_done F i ++ PU) ++ [[44]]) ++ WriterValue.wind p (wf_d F + 1))
    by (rewrite (wvc_done_step_arr F items i u Et Ety Hu); unfold wvc_itemP; rewrite Ety; rewrite <- ?app_assoc;
        reflexivity).
  assert (EI : Z.of_nat (S i) = Z.of_nat i + 1) by lia.
  apply (IH (S i) key3 ly3 S3 U3 W3 _ md3 buf3 Et ltac:(lia)).
  rewrite EDN, EI. exact HINV3.
Qed.

(* ================= the OBJECT loop ================= *)
Lemma wvc_loop_obj : forall members (j i : nat) key ly St U (W : world tfibsegs) ms mdc buf,
  wf_t F = PjTree.JObj members -> length members = (i + S j)%nat ->
  wvc_inv B F WVC_R_IND (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key (wvc_done F i)
    ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly St U buf ->
  SRr tfibsegs W (mkCfg ms mdc) wvc_POST.
Proof.
intros members j. induction j as [|j IH]; intros i key ly St U W ms mdc buf Et Hlen HINV.
all: destruct (wvl_obj members Et) as (Ety & En).
all: destruct (wvl_nth members i ltac:(lia)) as ([nm u] & Hu).
all: set (p := negb (wf_p F =? 0)).
all: set (PK := WriterSpec.spieces nm).
all: set (PS := [WriterValue.wsep p]).
all: set (PU := WriterValue.wvpieces u p (wf_d F + 1)).
all: assert (ESP : wvc_WP F = wvc_done F i ++ PK ++ PS ++ PU ++ wvc_rest F i)
       by (rewrite (wvc_split_obj F members i nm u Et Ety Hu); unfold wvc_itemP; rewrite Ety, Z.eqb_refl; rewrite <- ?app_assoc;
           reflexivity).
all: assert (Hu' : nth_error members (Z.to_nat (Z.of_nat i)) = Some (nm, u)) by (rewrite Nat2Z.id; exact Hu).
all: apply (ind_key (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key (wvc_done F i) (PS ++ PU ++ wvc_rest F i)
       ly St U W ms mdc buf members nm u wvc_POST HPS ESP HINV Et Hu').
all: intros ly1 S1 U1 W1 regs1 mem1 md1 buf1 key1 HINV1.
all: change (cfg_at tfibsegs WVC_R_KEY regs1 mem1 md1)
       with (mkCfg (mkst regs1 (Z_to_bv 64 WVC_R_KEY) mem1 (seg_rom tfibsegs)) md1).
all: assert (EWP1 : wvc_WP F = (wvc_done F i ++ PK) ++ PS ++ (PU ++ wvc_rest F i))
       by (rewrite ESP, <- ?app_assoc; reflexivity).
all: apply (key_sep (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key1 (wvc_done F i ++ PK) (PU ++ wvc_rest F i)
       ly1 S1 U1 W1 (mkst regs1 (Z_to_bv 64 WVC_R_KEY) mem1 (seg_rom tfibsegs)) md1 buf1 wvc_POST HPUT HIMG Ety
       EWP1 HINV1).
all: intros ly2 S2 U2 W2 regs2 mem2 md2 buf2 key2 HINV2.
all: change (cfg_at tfibsegs WVC_R_SEP regs2 mem2 md2)
       with (mkCfg (mkst regs2 (Z_to_bv 64 WVC_R_SEP) mem2 (seg_rom tfibsegs)) md2).
all: assert (EWP2 : wvc_WP F = ((wvc_done F i ++ PK) ++ PS) ++ PU ++ wvc_rest F i)
       by (rewrite ESP, <- ?app_assoc; reflexivity).
all: apply (sep_item k (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key2 ((wvc_done F i ++ PK) ++ PS) (wvc_rest F i)
       members nm u ly2 S2 U2 W2 (mkst regs2 (Z_to_bv 64 WVC_R_SEP) mem2 (seg_rom tfibsegs)) md2 buf2 wvc_POST
       HREC HM EWP2 HINV2 HDEP Et Hu').
all: intros ly3 S3 U3 W3 regs3 mem3 md3 buf3 key3 HINV3.
all: change (cfg_at tfibsegs WVC_R_ITEM regs3 mem3 md3)
       with (mkCfg (mkst regs3 (Z_to_bv 64 WVC_R_ITEM) mem3 (seg_rom tfibsegs)) md3).
all: set (PD := ((wvc_done F i ++ PK) ++ PS) ++ PU) in HINV3.
- (* the last member *)
  assert (ERL : wvc_rest F i = WriterValue.wind p (wf_d F) ++ [[125]])
    by exact (wvc_rest_last_obj F members i Et ltac:(lia)).
  assert (EWP : wvc_WP F = PD ++ WriterValue.wind p (wf_d F) ++ [[125]])
    by (unfold PD; rewrite ESP, ERL, <- ?app_assoc; reflexivity).
  apply (item_close (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key3 PD [[125]]
    ly3 S3 U3 W3 (mkst regs3 (Z_to_bv 64 WVC_R_ITEM) mem3 (seg_rom tfibsegs)) md3 buf3 wvc_POST HIND
    EWP HINV3 ltac:(lia)).
  intros ly4 S4 U4 W4 regs4 mem4 md4 buf4 HC.
  change (cfg_at tfibsegs WVC_R_CLOSE regs4 mem4 md4)
    with (mkCfg (mkst regs4 (Z_to_bv 64 WVC_R_CLOSE) mem4 (seg_rom tfibsegs)) md4).
  assert (EWP4 : wvc_WP F = (PD ++ WriterValue.wind p (wf_d F)) ++ [if wf_ty F =? 6 then [125] else [93]])
    by (rewrite Ety, EWP, <- ?app_assoc; reflexivity).
  exact (close_tail ch0 _ ly4 S4 U4 W4 _ md4 buf4 HIMG HPUT HPRE0 HSP0 HS00 EWP4 HC).
- (* another member follows *)
  destruct (wvl_nth members (S i) ltac:(lia)) as ([nm2 u2] & Hu2).
  set (PI2 := wvc_itemP F nm2 u2).
  assert (ERS : wvc_rest F i = [[44]] ++ WriterValue.wind p (wf_d F + 1) ++ PI2 ++ wvc_rest F (S i))
    by (rewrite (wvc_rest_step_obj F members i nm2 u2 Et Ety Hu2), wv_comma_S; reflexivity).
  assert (EWP : wvc_WP F = PD ++ [[44]] ++ (WriterValue.wind p (wf_d F + 1) ++ PI2 ++ wvc_rest F (S i)))
    by (unfold PD; rewrite ESP, ERS, <- ?app_assoc; reflexivity).
  apply (item_comma (Z.of_nat i) (wf_keys F + 8 * Z.of_nat i) key3 PD
    (WriterValue.wind p (wf_d F + 1) ++ PI2 ++ wvc_rest F (S i))
    ly3 S3 U3 W3 (mkst regs3 (Z_to_bv 64 WVC_R_ITEM) mem3 (seg_rom tfibsegs)) md3 buf3 wvc_POST HPUT HIMG
    ltac:(lia) EWP HINV3).
  intros ly4 S4 U4 W4 regs4 mem4 md4 buf4 key4 HINV4.
  change (cfg_at tfibsegs WVC_R_COMMA regs4 mem4 md4)
    with (mkCfg (mkst regs4 (Z_to_bv 64 WVC_R_COMMA) mem4 (seg_rom tfibsegs)) md4).
  assert (EWP4 : wvc_WP F = (PD ++ [[44]]) ++ WriterValue.wind p (wf_d F + 1) ++ (PI2 ++ wvc_rest F (S i)))
    by (rewrite EWP, <- ?app_assoc; reflexivity).
  apply (comma_ind (Z.of_nat i + 1) (wf_keys F + 8 * (Z.of_nat i + 1)) key4 (PD ++ [[44]])
    (PI2 ++ wvc_rest F (S i)) ly4 S4 U4 W4 (mkst regs4 (Z_to_bv 64 WVC_R_COMMA) mem4 (seg_rom tfibsegs)) md4 buf4
    wvc_POST HIND EWP4 HINV4).
  intros ly5 S5 U5 W5 regs5 mem5 md5 buf5 key5 HINV5.
  change (cfg_at tfibsegs WVC_R_IND regs5 mem5 md5)
    with (mkCfg (mkst regs5 (Z_to_bv 64 WVC_R_IND) mem5 (seg_rom tfibsegs)) md5).
  assert (EDN : wvc_done F (S i) = (PD ++ [[44]]) ++ WriterValue.wind p (wf_d F + 1))
    by (unfold PD; rewrite (wvc_done_step_obj F members i nm u Et Ety Hu); unfold wvc_itemP;
        rewrite Ety, Z.eqb_refl; rewrite <- ?app_assoc; reflexivity).
  assert (EI : Z.of_nat (S i) = Z.of_nat i + 1) by lia.
  apply (IH (S i) key5 ly5 S5 U5 W5 _ md5 buf5 Et ltac:(lia)).
  rewrite EDN, EI. exact HINV5.
Qed.

End A.
