(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod BitsLib BuildTreeLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel ScanModel SendModel TreesTab CompressModel
  BuildTreeModel GenBitlenModel RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7 TFB6_8 TFB6_9 TFB6_10 TFB6_11 TFB6_12 TFB6_13.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variables (buf : option Z) (bufp len last : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation SP := (sp - 64).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).

Hypothesis HH : FBH F mem0 mem S p PBL ds ra sp buf bufp len last.

Let MEMSET : memset_run6 := fbh_mset _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let MEMCPY : memcpy_run6 := fbh_mcpy _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := fbh_L _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := fbh_FS _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hret : ret_ok ra := fbh_ret _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := fbh_br _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := fbh_binv _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6 mem := fbh_rod _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlast : 0 <= last <= 1 := fbh_last _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : 0 <= len < 2 ^ 32 := fbh_len _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp TFB_FRAME := fbh_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := fbh_pbl _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : TFB_FRAME <= sp <= 2 ^ 63 := proj1 Hcf.
Local Abbreviation GFB := (TFB6_1.GFB S p PBL sp).
Local Abbreviation FI := (TFB6_1.FI F mem0 mem S p PBL sp).
Local Abbreviation Fmin := TFB6_1.Fmin.
Local Abbreviation KR := (TFB6_1.KR S sp last).
Local Abbreviation VB := TFB6_1.VB.
Local Abbreviation FBv := TFB6_1.FBv.
Local Abbreviation KPN := TFB6_1.KPN.
Local Abbreviation FRAME := (TFB6_2.FRAME ra sp).
Local Abbreviation pro_blk := (TFB6_2.pro_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation epi_blk := (TFB6_2.epi_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation wind_blk := (TFB6_2.wind_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation FRAME_fi := (TFB6_2.FRAME_fi F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation dt_phase := (TFB6_4.dt_phase F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation KR3 := (TFB6_8.KR3 S bufp len).
Local Abbreviation trees_phase := (TFB6_8.trees_phase F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation mb_chain := (TFB6_9.mb_chain F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation ZR := (TFB6_10.ZR S sp bufp len last).
Local Abbreviation sz1_blk := (TFB6_10.sz1_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation sz2_blk := (TFB6_10.sz2_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation low_blk := (TFB6_10.low_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation LPC := (TFB6_11.LPC last).
Local Abbreviation stored_arm := (TFB6_11.stored_arm F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation static_arm := (TFB6_11.static_arm F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation dyn_arm := (TFB6_13.dyn_arm F mem0 mem S p PBL ds ra sp buf bufp len last HH).


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [TFB6_1.tfF].

Local Ltac fb_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = ?v =>
      lazymatch v with
      | pb ?tt ?i =>
          match goal with H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
            eapply (pb_read4m sg m P len tt i a H); [lia | lia] end
      | arr_get bl_order_a ?i =>
          match goal with H : cells sg m ?P 1 1%nat _ (arr_get bl_order_a) |- _ =>
            eapply (bytes_read_at sg m P _ (arr_get bl_order_a) i a _ H); [lia | pose proof (bl_order_bound i); lia | lia | reflexivity] end
      end
  end.

Local Ltac side_closer :=
  try solve [ assumption
            | rewrite zw_u; reflexivity
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; fb_read
            | zcond_close
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; first [apply pb_range | apply bl_order_bound] ].

Local Ltac run C fuel dirs rds pins pv X :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals (TFB6_1.tfF X) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac runv C fuel dirs rds pins pv rv X :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs C fuel dirs rdv pinsv vbv NoRegions pv rv (TFB6_1.tfF X) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run_dbg C fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex_dbg s6_segs C fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6_rom)
  end.

Local Ltac open_br6 HB :=
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let C40 := fresh "C40" in let C16 := fresh "C16" in let C5936 := fresh "C5936" in let C5940 := fresh "C5940" in
  let Cpb := fresh "Cpb" in
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB) as (C40 & C16 & C5936 & C5940 & Cpb); dsred in C40; dsred in C5940; dsred in C5936; dsred in Cpb;
  let TLc := fresh "TLc" in let TLd := fresh "TLd" in let TDd := fresh "TDd" in let BLc := fresh "BLc" in let BLd := fresh "BLd" in
  pose proof (arrays_fc s6_segs _ _ _ TL Har) as TLc; pose proof (arrays_dl s6_segs _ _ _ TL Har) as TLd;
  pose proof (arrays_dl s6_segs _ _ _ TD Har) as TDd;
  pose proof (arrays_fc s6_segs _ _ _ TB Har) as BLc; pose proof (arrays_dl s6_segs _ _ _ TB Har) as BLd;
  rewrite ?SendTree6_1.tree_dl_set_bi_buf in TLd; rewrite ?SendTree6_1.tree_dl_set_bi_buf in TDd;
  rewrite ?SendTree6_1.tree_fc_set_bi_buf in TLc; rewrite ?SendTree6_1.tree_fc_set_bi_buf in BLc; rewrite ?SendTree6_1.tree_dl_set_bi_buf in BLd;
  cbn [toff tsize tree_fc tree_dl] in TLc, TLd, TDd, BLc, BLd;
  replace (S + 212 + 2) with (S + 214) in TLd by lia; replace (S + 2504 + 2) with (S + 2506) in TDd by lia;
  replace (S + 2748 + 2) with (S + 2750) in BLd by lia;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp'; unfold TFB_FRAME in Hsp';
  let HPBL' := fresh "HPBL'" in pose proof HPBL as HPBL';
  let Hcf' := fresh "Hcf'" in let HfS := fresh "HfS" in let HfP := fresh "HfP" in
  pose proof Hcf as Hcf'; destruct Hcf' as (_ & _ & _ & HfS & HfP); unfold TFB_FRAME, dsl_SIZE in HfS, HfP.

Local Ltac open_fi HF :=
  let HB := fresh "HB" in let HRC := fresh "HRC" in let HAG := fresh "HAG" in let MF := fresh "MF" in let HGR := fresh "HGR" in
  pose proof HF as HF'; destruct HF' as (HB & HRC & HAG & MF & HGR); unfold mapped in MF; open_br6 HB.

Local Ltac wr_tower MS MP :=
  repeat (apply wr_ok_wbytes;
          [ | let x := fresh "x" in let Hx := fresh "Hx" in
              intros x Hx; rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
              first [ apply MS; lia | apply MP; lia ]
            | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]);
  apply wr_ok_refl.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold TFB6_1.GFB;
              first [ apply sub_franges_here; unfold dsl_SIZE; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [reflexivity | assumption | f_equal; lia | f_equal; f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] end
        | idtac ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.
Local Ltac cnt_reg HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
    let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
    rewrite ?lxor_ltb1 by lia; rewrite ?Z.eqb_refl;
    try (replace (_ =? _) with false by (symmetry; apply Z.eqb_neq; lia));
    vm_compute; reflexivity
  end.
Local Ltac kregs HR Hfr := unfold TFB6_1.KR; regs_of HR Hfr.
Local Ltac kd H := destruct H as (K8 & K9 & K21 & K22 & K2).

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                           | apply mod16_congr; lia
                           | apply mod16_up; lia
                           | rewrite land16_mod; first [apply mod16_congr; lia | apply mod16_up; lia]
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; first [reflexivity | apply mod16_congr; lia | apply mod16_up; lia]
                          | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                          | apply wrap16_id'; lia
                          | apply land16_wrap16; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia | apply land16_range ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia
                        | lazymatch goal with H : SendTree6_1.RBr _ _ _ |- _ => exact H end
                        | apply Z.mod_small; lia ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply srl_eq'; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold SendTree6_1.RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply srl_eq'; [vrange | vwrap | lia].
Local Ltac bv_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia.
Local Ltac st_keep vnorm :=
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); st_eq;
  [ reflexivity
  | reflexivity
  | first [reflexivity | vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); lia] ].
Local Ltac rb_keep r HR vnorm :=
  unfold SendTree6_1.RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr].
Local Ltac bv_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); lia.
Local Ltac sll_flush r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; f_equal; lia.
Local Ltac sll_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); f_equal; lia.

Local Ltac site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      end
  end.
Local Ltac site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eexists; eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      end
  end.


Lemma match_some {A} : forall (o : option Z) off (x y : A), o = Some off -> match o with Some _ => x | None => y end = x.
Proof. intros o off x y ->. reflexivity. Qed.
Lemma match_none {A} : forall (o : option Z) (x y : A), o = None -> match o with Some _ => x | None => y end = y.
Proof. intros o x y ->. reflexivity. Qed.

Lemma bufp_facts :
  0 <= bufp < 2 ^ 64 /\ (bufp = 0 \/ 0 < bufp < 2 ^ 64)
  /\ ((buf = None /\ negb (bufp =? 0) = false) \/ (exists off, buf = Some off /\ negb (bufp =? 0) = true)).
Proof.
  pose proof (fbh_src _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as Hsrc. unfold fb_src in Hsrc.
  destruct buf as [off|].
  - destruct Hsrc as (_ & Hb & _). split; [lia|]. split; [lia|]. right. exists off. split; [reflexivity|].
    destruct (Z.eqb_spec bufp 0); [lia | reflexivity].
  - rewrite Hsrc. split; [lia|]. split; [lia|]. left. split; reflexivity.
Qed.

Lemma dyn_res_eq : forall X mb,
  dyn_res last X mb =
   (let s := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
    let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (mb + 1) in
    compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s)).
Proof.
  intros X mb. unfold dyn_res, send_all_trees. cbv zeta.
  rewrite !sb_lmc, !sb_dmc.
  replace (ds_l_max_code X + 1 - 1) with (ds_l_max_code X) by lia.
  replace (ds_d_max_code X + 1 - 1) with (ds_d_max_code X) by lia.
  reflexivity.
Qed.

Lemma OLB0_range : forall X6, 0 <= TFB6_10.OLB0 X6 < 2 ^ 61.
Proof. intros X6. unfold TFB6_10.OLB0. destruct (_ || _); [apply TFB6_10.SLB_range | apply TFB6_10.OLB_range]. Qed.

Lemma dt_st_eq : forall X,
  TFB6_4.dt_st X = (if cs_data_type (ds_strm X) =? 2 then set_strm X (cset_data_type (ds_strm X) (detect_data_type X)) else X).
Proof. intros X. reflexivity. Qed.

Lemma bll_of_tree_dl : forall X,
  (forall k, 0 <= k < 39 -> 0 <= arr_get (tree_dl X TB) k < 65536) ->
  forall k, 0 <= k < 39 -> 0 <= arr_get (ds_bl_tree_dl X) k < 65536.
Proof. intros X H. exact H. Qed.


Local Ltac frw H Hr := rewrite (H _ ) by (eapply reg_in_sub; [|exact Hr]; reflexivity).


Lemma tail_run : forall regs (regs0 : bvmap 5 word) m1 m X7,
  FI m1 m (init_block X7) -> FRAME m1 regs0 -> KR regs -> tail_ok PBL X7 last ->
  exists R m',
    msteps s6_segs (mkst regs LPC m s6_rom) (mkst R ra m' s6_rom)
    /\ FI m1 m' (let X8 := init_block X7 in if negb (last =? 0) then bi_windup X8 else X8)
    /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 m X7 HF HFR HK (HBI & Hroom). cbv zeta. unfold TFB6_11.LPC.
  destruct (Z.eqb_spec last 0) as [El|El]; cbn [negb].
  - destruct (epi_blk regs regs0 m1 m _ HF (FRAME_fi m1 m _ regs0 HF HFR) HK) as (R & Hms & Q2 & Q1 & Hcs & Hfr).
    exists R, m. split; [exact Hms|]. split; [exact HF|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact Hcs | fr_weak Hfr].
  - destruct (wind_blk regs m1 m _ HF HBI (Hroom El) HK) as (R1 & m2 & Hms1 & HF1 & HK1 & Hfr1).
    destruct (epi_blk R1 regs0 m1 m2 _ HF1 (FRAME_fi m1 m2 _ regs0 HF1 HFR) HK1) as (R & Hms & Q2 & Q1 & Hcs & Hfr).
    exists R, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HF1|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact Hcs|].
    intros r Hr. frw Hfr Hr. apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Definition HI_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28; 29; 30; 31]%bv.

Lemma hi_run : forall R0 (regs0 : bvmap 5 word) m1 (X0 X1 X2 X3 X4 X5 : deflate_state) (mb : Z) (X6 : deflate_state),
  X0 = TFB6_4.dt_st ds ->
  X1 = build_tree X0 TL -> X2 = build_tree X1 TD -> X3 = scan_tree X2 TL (ds_l_max_code X2) ->
  X4 = scan_tree X3 TD (ds_d_max_code X3) -> X5 = build_tree X4 TB -> mb = build_bl_tree_loop 17 X5 18 ->
  X6 = set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)) ->
  FI m1 m1 ds -> FRAME m1 regs0 -> KR R0 -> KR3 R0 ->
  cell s6_segs m1 (p_strm p + 88) 4 (cs_data_type (ds_strm ds)) ->
  - 2 ^ 31 <= cs_data_type (ds_strm ds) < 2 ^ 31 ->
  (cs_data_type (ds_strm ds) = 2 -> forall k, 0 <= k < 573 -> 0 <= arr_get (ds_dyn_ltree_fc ds) k < 65536) ->
  let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
  let static_lenb := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3 in
  let opt_lenb0 := if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb in
  let sto := (len + 4 <=? opt_lenb0) && match buf with Some _ => true | None => false end in
  let sta := static_lenb =? opt_lenb0 in
  let X7 := if sto then tr_stored_block X6 buf len last
            else if sta
            then (let s := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                  compress_block s static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
            else (let s := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                  let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (mb + 1) in
                  compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s)) in
  bt_safe X0 TL -> bt_safe X1 TD ->
  (0 <= ds_l_max_code X2 /\ ds_l_max_code X2 + 1 < 573) -> (forall i, 0 <= i <= ds_l_max_code X2 -> 0 <= Len X2 TL i <= 15) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536) ->
  (0 <= ds_d_max_code X3 /\ ds_d_max_code X3 + 1 < 61) -> (forall i, 0 <= i <= ds_d_max_code X3 -> 0 <= Len X3 TD i <= 15) ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536) ->
  bt_safe X4 TB ->
  (forall k, 0 <= k < 39 -> 0 <= arr_get (tree_dl X5 TB) k < 65536) ->
  0 <= ds_opt_len X5 < 2 ^ 64 -> 0 <= ds_static_len X5 < 2 ^ 64 -> 0 <= ds_strategy X5 <= 4 ->
  (if sto then sto_ok PBL ds X6 buf len last else if sta then stat_ok PBL X6 last else dyn_ok PBL last X6 mb) ->
  exists R mB m',
    msteps s6_segs (mkst R0 (0x1afe8 : word) m1 s6_rom) (mkst R LPC m' s6_rom)
    /\ FI mB m' (init_block X7) /\ FRAME mB regs0
    /\ cell s6_segs mB (p_strm p + 88) 4 (cs_data_type (ds_strm X0))
    /\ KR R
    /\ (forall r : reg, reg_in r HI_CLOB = false -> getr R r = getr R0 r).
Proof.
  intros R0 regs0 m1 X0 X1 X2 X3 X4 X5 mb X6 E0 E1 E2 E3 E4 E5 Emb E6 HF1 HFR HK0 HK30 Cdt Hdt HLF. cbv zeta.
  intros BT1 BT2 Hmcl L1 L2 L3 Hmcd M1 M2 M3 BT3 HBD HOL HSL HSTR HDEC.
  pose proof Hsp as Hsp'; unfold TFB_FRAME in Hsp'.
  pose proof bufp_facts as (Hbufp & Hbz & Hbcase).
  destruct (dt_phase R0 m1 m1 ds HF1 HK0 Cdt Hdt HLF) as (R1 & mB & Hms1 & HFB & CE1 & CdtB & HK1 & Hfr1).
  rewrite <- E0 in HFB. rewrite <- E0 in CdtB.
  assert (HFRB : FRAME mB regs0) by (exact (TFB6_2.FRAME_keep ra sp m1 mB regs0 CE1 HFR)).
  assert (HK31 : KR3 R1).
  { destruct HK30 as (A18 & A19 & A20). unfold TFB6_8.KR3.
    rewrite (Hfr1 18%bv eq_refl), (Hfr1 19%bv eq_refl), (Hfr1 20%bv eq_refl). repeat split; assumption. }
  pose proof (trees_phase R1 mB mB X0 HFB HK1 HK31 Hbufp) as T. cbv zeta in T.
  rewrite <- E1 in T. rewrite <- E2 in T. rewrite <- E3 in T. rewrite <- E4 in T. rewrite <- E5 in T.
  specialize (T BT1 BT2 Hmcl L1 L2 L3 Hmcd M1 M2 M3 BT3).
  destruct T as (R2 & m2 & Hms2 & HF2 & HK2 & HK32 & Hfr2).
  destruct (mb_chain R2 mB m2 X5 HF2 HK2 HK32 Hbufp (bll_of_tree_dl X5 HBD)) as (R3 & Hms3 & HK3 & HK33 & Q10 & Hfr3).
  rewrite <- (TFB6_9.mbv_eq X5), <- Emb in Q10.
  pose proof (TFB6_9.mbv_range X5) as Hmb. rewrite <- (TFB6_9.mbv_eq X5), <- Emb in Hmb.
  destruct (sz1_blk R3 mB m2 X5 mb HF2 HK3 HK33 Hbufp Q10 ltac:(lia) HOL HSL HSTR) as (R4 & m4 & Hms4 & HF4 & HZ4 & Hfr4).
  assert (EX6 : TFB6_10.X6of X5 mb = X6) by (rewrite E6; reflexivity).
  rewrite EX6 in HF4. rewrite EX6 in HZ4.
  pose proof (OLB0_range X6) as HO0. pose proof (TFB6_10.SLB_range X6) as HS0.
  unfold TFB6_10.OLB0, TFB6_10.OLB, TFB6_10.SLB in HZ4, HO0, HS0.
  assert (HBI6 : BINV PBL X6).
  { clear - HDEC. revert HDEC.
    lazymatch goal with |- (if ?b then _ else _) -> _ => destruct b end; [intros H; exact (proj1 H)|].
    lazymatch goal with |- (if ?b then _ else _) -> _ => destruct b end; intros H; [exact (proj1 H) | exact (proj1 (proj1 H))]. }
  assert (Hbv6 : 0 <= ds_bi_valid X6 <= 16) by (destruct HBI6 as (Hbv & _); exact Hbv).
  destruct (sz2_blk R4 mB m4 X6 mb _ _ HF4 HZ4 Hbz ltac:(lia) HS0 HO0 Hbv6) as (R5 & Hms5 & HZ5 & HQ12 & Hfr5).
  assert (Ebuf : negb (bufp =? 0) = match buf with Some _ => true | None => false end).
  { destruct Hbcase as [[Eb En]|(off & Eb & En)]; rewrite En; symmetry; [exact (match_none buf true false Eb) | exact (match_some buf off true false Eb)]. }
  rewrite Ebuf in Hms5. rewrite Ebuf in HQ12. clear Ebuf.
  pose proof HZ5 as (HK5 & HK35 & V10 & V11 & V13).
  lazymatch goal with |- exists Ra mBa ma, _ /\ TFB6_1.FI _ _ _ _ _ _ _ _ _ ?st /\ _ =>
  lazymatch type of Hms5 with context [mkst R5 (TFB6_10.SZPC ?b1 ?b2) m4] =>
  assert (ARMS : exists R m',
    msteps s6_segs (mkst R5 (TFB6_10.SZPC b1 b2) m4 s6_rom) (mkst R LPC m' s6_rom)
    /\ FI mB m' st /\ KR R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28; 29; 30; 31]%bv = false -> getr R r = getr R5 r))
  end end.
  { lazymatch goal with |- exists Rq mq, msteps _ (mkst _ (TFB6_10.SZPC ?b1 _) _ _) _ /\ _ =>
      destruct (Sumbool.sumbool_of_bool b1) as [Hsto|Hsto] end.
    - rewrite Hsto in HQ12, HDEC |- *. unfold TFB6_10.SZPC. cbv iota beta in HDEC. cbv iota beta.
      destruct HDEC as (_ & Hroom6 & EW6).
      assert (Hb : buf <> None).
      { intros En. destruct Hbcase as [[_ Ez]|(off & Eb & _)]; [| rewrite Eb in En; discriminate En].
        rewrite (match_none buf true false En), Bool.andb_false_r in Hsto. discriminate Hsto. }
      destruct (stored_arm R5 mB m4 X6 mb _ _ HF4 HZ5 Hbufp ltac:(lia) HS0 HO0 HBI6 Hroom6 EW6 (fun _ => Hb))
        as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
      exists R6, m6. split; [exact Hms6|]. split; [exact HF6|]. split; [exact HK6 | fr_weak Hfr6].
    - rewrite Hsto in HQ12, HDEC |- *. unfold TFB6_10.SZPC. cbv iota beta in HDEC. cbv iota beta.
      lazymatch goal with |- exists Rq mq, msteps _ (mkst _ (if ?b2 then _ else _) _ _) _ /\ _ =>
        destruct (Sumbool.sumbool_of_bool b2) as [Hsta|Hsta] end.
      + rewrite Hsta in HDEC |- *. cbv iota beta in HDEC. cbv iota beta.
        destruct (static_arm R5 mB m4 X6 HF4 HK5 (HQ12 eq_refl) HDEC) as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
        exists R6, m6. split; [exact Hms6|]. split; [exact HF6|]. split; [exact HK6 | fr_weak Hfr6].
      + rewrite Hsta in HDEC |- *. cbv iota beta in HDEC. cbv iota beta.
        destruct (dyn_arm R5 mB m4 X6 mb HF4 HK5 V10 (proj2 (proj2 HK35)) (HQ12 eq_refl) ltac:(lia) HDEC)
          as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
        rewrite (dyn_res_eq X6 mb) in HF6. cbv zeta in HF6.
        exists R6, m6. split; [exact Hms6|]. split; [exact HF6|]. split; [exact HK6 | exact Hfr6]. }
  destruct ARMS as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
  exists R6, mB, m6. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
    eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6]. }
  split; [exact HF6|]. split; [exact HFRB|]. split; [exact CdtB|]. split; [exact HK6|].
  unfold HI_CLOB. intros r Hr. frw Hfr6 Hr. frw Hfr5 Hr. frw Hfr4 Hr. frw Hfr3 Hr. frw Hfr2 Hr.
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Definition LO_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Lemma lo_run : forall R0 m1,
  FI m1 m1 ds -> KR R0 -> KR3 R0 ->
  match buf with Some _ => sto_ok PBL ds ds buf len last | None => stat_ok PBL ds last end ->
  exists R m',
    msteps s6_segs (mkst R0 (0x1b104 : word) m1 s6_rom) (mkst R LPC m' s6_rom)
    /\ FI m1 m' (init_block (match buf with
                             | Some _ => tr_stored_block ds buf len last
                             | None => compress_block (send_bits ds (Z.shiftl STATIC_TREES 1 + last) 3)
                                         static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
                             end))
    /\ KR R
    /\ (forall r : reg, reg_in r LO_CLOB = false -> getr R r = getr R0 r).
Proof.
  intros R0 m1 HF1 HK0 HK30 HDEC.
  pose proof bufp_facts as (Hbufp & Hbz & Hbcase). pose proof Hlen as Hln.
  destruct (low_blk R0 m1 m1 ds HF1 HK0 HK30 Hbufp) as (R1 & Hms1 & HZ1 & Hfr1).
  assert (Hbv : 0 <= ds_bi_valid ds <= 16) by (pose proof Hbinv as (A & _); exact A).
  destruct (sz2_blk R1 m1 m1 ds 0 (len + 5) (len + 5) HF1 HZ1 Hbz ltac:(lia) ltac:(lia) ltac:(lia) Hbv) as (R2 & Hms2 & HZ2 & HQ12 & Hfr2).
  replace (len + 4 <=? len + 5) with true in Hms2, HQ12 by (symmetry; apply Z.leb_le; lia).
  rewrite Z.eqb_refl in Hms2. cbn [andb] in Hms2, HQ12. unfold TFB6_10.SZPC in Hms2.
  pose proof HZ2 as (HK2 & HK32 & V10 & V11 & V13).
  destruct Hbcase as [[Eb En]|(off & Eb & En)]; rewrite En in Hms2, HQ12; cbv iota beta in Hms2;
    [rewrite (match_none buf _ _ Eb) in HDEC; rewrite (match_none buf _ _ Eb)
    |rewrite (match_some buf off _ _ Eb) in HDEC; rewrite (match_some buf off _ _ Eb)].
  -
    destruct (static_arm R2 m1 m1 ds HF1 HK2 (HQ12 eq_refl) HDEC) as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
    exists R6, m6. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms6]|].
    split; [exact HF6|]. split; [exact HK6|].
    unfold LO_CLOB. intros r Hr. frw Hfr6 Hr. frw Hfr2 Hr. apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
  -
    destruct HDEC as (HBI & Hroom & EW).
    destruct (stored_arm R2 m1 m1 ds 0 (len + 5) (len + 5) HF1 HZ2 Hbufp ltac:(lia) ltac:(lia) ltac:(lia) HBI Hroom EW
                ltac:(intros _; rewrite Eb; discriminate))
      as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
    exists R6, m6. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms6]|].
    split; [exact HF6|]. split; [exact HK6|].
    unfold LO_CLOB. intros r Hr. frw Hfr6 Hr. frw Hfr2 Hr. apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Theorem tr_flush_block_run : forall regs,
  fb_safe ds buf len last ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len ->
  getr regs 13 = zw last -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1af98 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (tr_flush_block ds buf len last)
    /\ cell s6_segs m' (p_strm p + 88) 4 (cs_data_type (ds_strm (tr_flush_block ds buf len last)))
    /\ trees_rod_clear6 m'
    /\ (forall r : reg, reg_in r TFB_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs HS P10 P11 P12 P13 P2 P1.
  pose proof HBR0 as (_ & _ & _ & _ & EPBL & _).
  cbv beta delta [fb_safe] in HS. rewrite EPBL in HS. cbv delta [Z_UNKNOWN] in HS.
  destruct HS as (Hlv & Hdt & _ & Hstrm & HS).
  pose proof (fbh_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as (Cdt0 & Hps0 & Hps1 & HsF & Hsm & HsS & HsP & Hssp).
  unfold TFB_FRAME, dsl_SIZE in HsS, HsP, Hssp.
  pose proof Hsp as Hsp'; unfold TFB_FRAME in Hsp'. pose proof Hlen as Hln.
  pose proof HLb as ((HS1 & HS2) & (HP1' & HP2') & _). unfold dsl_SIZE in HS2.
  pose proof bufp_facts as (Hbufp & Hbz & Hbcase).
  destruct (pro_blk regs ltac:(lia) P10 P11 P12 P13 P2 P1 Hbufp) as (R0 & m1 & Hms0 & HF0 & HFR0 & CE0 & HK0 & Q18 & Q19 & Q20 & Hfr0).
  assert (Cdt1 : cell s6_segs m1 (p_strm p + 88) 4 (cs_data_type (ds_strm ds))) by (apply CE0; [exact Cdt0 | lia | cbn; lia]).
  assert (HK30 : KR3 R0) by (split; [exact Q18|]; split; [exact Q19 | exact Q20]).
  assert (STRM : forall mB m' X, FI mB m' X -> forall v, cell s6_segs mB (p_strm p + 88) 4 v -> cell s6_segs m' (p_strm p + 88) 4 v).
  { intros mB m' X (_ & _ & HAG & _) v Hc.
    apply (cell_agree_out s6_segs GFB mB m' _ 4 v HAG); [| lia | cbn; lia | exact Hc].
    unfold TFB6_1.GFB. intros x Hx [H|[H|[H|[]]]]; cbn in H; unfold dsl_SIZE in *; lia. }
  destruct (Z_lt_le_dec 0 (ds_level ds)) as [Cl|Cl].
  -
    rewrite (proj2 (Z.ltb_lt 0 _) Cl) in Hms0, HS, Hstrm. cbv iota beta in HS. cbn [andb] in Hstrm.
    destruct HS as (HLF & HS). cbv zeta in HS.
    destruct HS as (BT1 & BT2 & Hmcl & L1 & L2 & L3 & Hmcd & M1 & M2 & M3 & BT3 & HBD & HOL & HSL & HSTR & HDEC & HTAIL).
    rewrite (wrap64_id (len + _)) in HDEC by lia. rewrite (wrap64_id (len + _)) in HTAIL by lia.
    pose proof (hi_run R0 regs m1 _ _ _ _ _ _ _ _ (eq_sym (dt_st_eq ds)) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  HF0 HFR0 HK0 HK30 Cdt1 Hdt HLF) as T.
    cbv zeta in T.
    specialize (T BT1 BT2 Hmcl L1 L2 L3 Hmcd M1 M2 M3 BT3 HBD HOL HSL HSTR HDEC).
    destruct T as (R6 & mB & m6 & Hms6 & HF6 & HFRB & CdtB & HK6 & Hfr6).
    destruct (tail_run R6 regs mB m6 _ HF6 HFRB HK6 HTAIL) as (R7 & m7 & Hms7 & HF7 & W2 & W1 & Hcs & Hfr7).
    exists R7, m7. split.
    { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms6 | exact Hms7]. }
    split.
    { destruct HF7 as (HB7 & _). rewrite (tfb_eq_raw ds buf len last Cl). cbv delta [Z_UNKNOWN].
      change (BL_CODES - 1) with 18. cbv zeta in HB7. cbv zeta.
      rewrite (wrap64_id (len + _)) by lia. exact HB7. }
    split.
    { rewrite Hstrm. apply (STRM mB m7 _ HF7).
      pose proof (TFB6_4.dt_st_data_type ds) as Edt. rewrite (dt_st_eq ds) in Edt. rewrite Edt in CdtB. exact CdtB. }
    split; [destruct HF7 as (_ & HRC7 & _); exact HRC7|].
    apply (frame_fix R7 regs 1%bv); [rewrite W1, P1; reflexivity|].
    apply (frame_fix R7 regs 2%bv); [rewrite W2, P2; reflexivity|].
    apply (frame_fix R7 regs 8%bv); [exact (Hcs 8%bv eq_refl)|]. apply (frame_fix R7 regs 9%bv); [exact (Hcs 9%bv eq_refl)|].
    apply (frame_fix R7 regs 18%bv); [exact (Hcs 18%bv eq_refl)|]. apply (frame_fix R7 regs 19%bv); [exact (Hcs 19%bv eq_refl)|].
    apply (frame_fix R7 regs 20%bv); [exact (Hcs 20%bv eq_refl)|]. apply (frame_fix R7 regs 21%bv); [exact (Hcs 21%bv eq_refl)|].
    apply (frame_fix R7 regs 22%bv); [exact (Hcs 22%bv eq_refl)|].
    unfold TFB_CLOB. intros r Hr. frw Hfr7 Hr. frw Hfr6 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
  -
    rewrite (proj2 (Z.ltb_ge 0 _) Cl) in Hms0, HS, Hstrm. cbv iota beta in HS. cbn [andb] in Hstrm.
    assert (HDEC : match buf with Some _ => sto_ok PBL ds ds buf len last | None => stat_ok PBL ds last end).
    { destruct Hbcase as [[Eb En]|(off & Eb & En)].
      - rewrite (match_none buf _ _ Eb). rewrite (match_none buf _ _ Eb) in HS. exact (proj1 HS).
      - rewrite (match_some buf off _ _ Eb). rewrite (match_some buf off _ _ Eb) in HS. exact (proj1 HS). }
    assert (HTAIL : tail_ok PBL (match buf with
                                 | Some _ => tr_stored_block ds buf len last
                                 | None => compress_block (send_bits ds (Z.shiftl STATIC_TREES 1 + last) 3)
                                             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
                                 end) last).
    { destruct Hbcase as [[Eb En]|(off & Eb & En)].
      - rewrite (match_none buf _ _ Eb). rewrite (match_none buf _ _ Eb) in HS. exact (proj2 HS).
      - rewrite (match_some buf off _ _ Eb). rewrite (match_some buf off _ _ Eb) in HS. exact (proj2 HS). }
    destruct (lo_run R0 m1 HF0 HK0 HK30 HDEC) as (R6 & m6 & Hms6 & HF6 & HK6 & Hfr6).
    destruct (tail_run R6 regs m1 m6 _ HF6 HFR0 HK6 HTAIL) as (R7 & m7 & Hms7 & HF7 & W2 & W1 & Hcs & Hfr7).
    exists R7, m7. split.
    { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms6 | exact Hms7]. }
    split.
    { destruct HF7 as (HB7 & _). rewrite (tfb_eq_low ds buf len last Cl Hln). cbv zeta in HB7. cbv zeta. exact HB7. }
    split.
    { rewrite Hstrm. apply (STRM m1 m7 _ HF7). exact Cdt1. }
    split; [destruct HF7 as (_ & HRC7 & _); exact HRC7|].
    apply (frame_fix R7 regs 1%bv); [rewrite W1, P1; reflexivity|].
    apply (frame_fix R7 regs 2%bv); [rewrite W2, P2; reflexivity|].
    apply (frame_fix R7 regs 8%bv); [exact (Hcs 8%bv eq_refl)|]. apply (frame_fix R7 regs 9%bv); [exact (Hcs 9%bv eq_refl)|].
    apply (frame_fix R7 regs 18%bv); [exact (Hcs 18%bv eq_refl)|]. apply (frame_fix R7 regs 19%bv); [exact (Hcs 19%bv eq_refl)|].
    apply (frame_fix R7 regs 20%bv); [exact (Hcs 20%bv eq_refl)|]. apply (frame_fix R7 regs 21%bv); [exact (Hcs 21%bv eq_refl)|].
    apply (frame_fix R7 regs 22%bv); [exact (Hcs 22%bv eq_refl)|].
    unfold TFB_CLOB. intros r Hr. frw Hfr7 Hr. frw Hfr6 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.


Theorem tr_flush_block_run6_ok : tr_flush_block_run6 fb_safe.
Proof.
  unfold tr_flush_block_run6.
  intros F mem0 mem S p PBL ds ra regs sp buf bufp len last MS MC HL HFS Hret HB HBI HRC HS Hlast Hlen Hcf Hsrc Hstrm
         P10 P11 P12 P13 P2 P1.
  assert (HPBL : 0 < PBL).
  { pose proof HB as (_ & _ & _ & _ & EPBL & _). rewrite <- EPBL. destruct HS as (_ & _ & H & _). exact H. }
  pose (HH := {| fbh_mset := MS; fbh_mcpy := MC; fbh_L := HL; fbh_FS := HFS; fbh_ret := Hret; fbh_br := HB; fbh_binv := HBI;
                 fbh_rod := HRC; fbh_last := Hlast; fbh_len := Hlen; fbh_fr := Hcf; fbh_src := Hsrc; fbh_strm := Hstrm; fbh_pbl := HPBL |}
          : FBH F mem0 mem S p PBL ds ra sp buf bufp len last).
  destruct (tr_flush_block_run F mem0 mem S p PBL ds ra sp buf bufp len last HH regs HS P10 P11 P12 P13 P2 P1)
    as (R & m' & Hms & HB' & Hc & HRC' & Hfr).
  exists R, m'. unfold A6_TR_FLUSH_BLOCK. replace (zw 0x1af98) with (0x1af98%bv : word) by (apply bv_eq; reflexivity).
  split; [exact Hms|]. split; [exact HB'|]. split; [exact Hc|]. split; [exact HRC' | exact Hfr].
Qed.
End FXG.
