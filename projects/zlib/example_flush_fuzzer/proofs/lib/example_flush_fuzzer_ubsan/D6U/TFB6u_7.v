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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u FillWin6uD
  CompressBlk6u_1 CompressBlk6u_4 BuildTree6u_11 TrSmall6u TrStored6u ScanTree6u SendTree6u_1 SendTree6u_5 TFB6u_1 TFB6u_2 TFB6u_3 TFB6u_4 TFB6u_5 TFB6u_6.
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
Local Abbreviation BRm := (BR6u F mem0 S p PBL).

Hypothesis HH : FBHu F mem0 mem S p PBL ds ra sp buf bufp len last.

Let MEMSET : memset_run6u := fbh_mset _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let MEMCPY : memcpy_run6u := fbh_mcpy _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := fbh_L _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := fbh_FS _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hret : ret_ok ra := fbh_ret _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := fbh_br _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hbinv : BINV PBL ds := fbh_binv _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6u mem := fbh_rod _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlast : 0 <= last <= 1 := fbh_last _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hlen : 0 <= len < 2 ^ 32 := fbh_len _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp TFB_FRAME6u := fbh_fr _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := fbh_pbl _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HUB : UBT S p := fbh_ub _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : TFB_FRAME6u <= sp <= 2 ^ 63 := proj1 Hcf.
Local Abbreviation GFB := (TFB6u_1.GFB S p PBL sp).
Local Abbreviation FI := (TFB6u_1.FI F mem0 mem S p PBL sp).
Local Abbreviation KR := (TFB6u_1.KR S sp last).
Local Abbreviation VB := TFB6u_1.VB.
Local Abbreviation FBv := TFB6u_1.FBv.
Local Abbreviation KPN := TFB6u_1.KPN.
Local Abbreviation KRW := (TFB6u_1.KRW S sp last).
Local Abbreviation KPW := TFB6u_1.KPW.
Local Abbreviation KR_W := (TFB6u_1.KR_W S sp last).
Local Abbreviation HS8 := (TFB6u_1.HS8 F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation RBr := SendTree6u_1.RBr.
Local Abbreviation LR := (TFB6u_6.LR S sp last).
Local Abbreviation LPC := (TFB6u_5.LPC last).


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [TFB6u_1.tfF].

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
            | change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
            | nf; change (2 ^ 2) with 4 in *; zcond_close
            | nf; match goal with H : zaluw ALU_SRL _ _ = 0 |- _ => rewrite !H end; zcond_close
            | nf; apply SendTree6u_1.srl_check0u; lia
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; first [apply pb_range | apply bl_order_bound] ].

Local Ltac run C fuel dirs rds pins pv X :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals (TFB6u_1.tfF X) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs C fuel dirs rdv pinsv vbv NoRegions pv rv (TFB6u_1.tfF X) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run_dbg C fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex_dbg s6u_segs C fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6u_rom)
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
  pose proof (arrays_fc s6u_segs _ _ _ TL Har) as TLc; pose proof (arrays_dl s6u_segs _ _ _ TL Har) as TLd;
  pose proof (arrays_dl s6u_segs _ _ _ TD Har) as TDd;
  pose proof (arrays_fc s6u_segs _ _ _ TB Har) as BLc; pose proof (arrays_dl s6u_segs _ _ _ TB Har) as BLd;
  rewrite ?SendTree6u_1.tree_dl_set_bi_buf in TLd; rewrite ?SendTree6u_1.tree_dl_set_bi_buf in TDd;
  rewrite ?SendTree6u_1.tree_fc_set_bi_buf in TLc; rewrite ?SendTree6u_1.tree_fc_set_bi_buf in BLc; rewrite ?SendTree6u_1.tree_dl_set_bi_buf in BLd;
  cbn [toff tsize tree_fc tree_dl] in TLc, TLd, TDd, BLc, BLd;
  replace (S + 212 + 2) with (S + 214) in TLd by lia; replace (S + 2504 + 2) with (S + 2506) in TDd by lia;
  replace (S + 2748 + 2) with (S + 2750) in BLd by lia;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp'; unfold TFB_FRAME6u in Hsp';
  let HPBL' := fresh "HPBL'" in pose proof HPBL as HPBL';
  let Hcf' := fresh "Hcf'" in let HfS := fresh "HfS" in let HfP := fresh "HfP" in
  pose proof Hcf as Hcf'; destruct Hcf' as (_ & _ & _ & HfS & HfP); unfold TFB_FRAME6u, dsl_SIZE in HfS, HfP.

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
            | rewrite ?length_Z_to_le_bytes; unfold TFB6u_1.GFB;
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
Local Ltac kregs HR Hfr := unfold TFB6u_1.KR; regs_of HR Hfr.
Local Ltac kd H := destruct H as (K8 & K9 & K20 & K21 & K2).
Local Ltac kdw H := destruct H as (K8 & K9 & K2).
Local Ltac kregsw HR Hfr := unfold TFB6u_1.KRW; regs_of HR Hfr.

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                           | apply mod16_congr; lia
                           | apply mod16_up; lia
                           | rewrite land16_mod; first [apply mod16_congr; lia | apply mod16_up; lia]
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; first [apply mod16_congr; lia | apply mod16_up; lia]
                           | repeat (rewrite (szwrap_small 16) by lia); first [reflexivity | apply mod16_congr; lia] ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; first [reflexivity | apply mod16_congr; lia | apply mod16_up; lia]
                          | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity
                          | apply wrap16_id'; lia
                          | apply land16_wrap16; first [apply mod16_congr; lia | apply mod16_up; lia] ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia | apply land16_range ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia
                        | lazymatch goal with H : SendTree6u_1.RBr _ _ _ |- _ => exact H end
                        | apply Z.mod_small; lia ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; first [eapply nb_eqm2 | eapply nb_eqm2']; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply SendTree6u_1.srl_eq'u; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold SendTree6u_1.RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; apply SendTree6u_1.srl_eq'u; [vrange | vwrap | lia].
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
  unfold SendTree6u_1.RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
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
                        | split; [ apply (trees_rod_clear_wr R6u _ _ HRC); wr_tower MS MP
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
                        | split; [ apply (trees_rod_clear_wr R6u _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      end
  end.

Definition lC : cfg := CFG FBv [] [EVar 50%nat] [0x1c8d8; 0x1c9c0] [].

Local Abbreviation lmax X := (ds_l_max_code X).
Local Abbreviation dmax X := (ds_d_max_code X).

Lemma sb_lmc : forall s v l, ds_l_max_code (send_bits s v l) = ds_l_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.
Lemma sb_dmc : forall s v l, ds_d_max_code (send_bits s v l) = ds_d_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.
Lemma sat_lmc : forall f s b r, ds_l_max_code (send_all_trees_loop f s b r) = ds_l_max_code s.
Proof. induction f as [|f IH]; intros; [reflexivity|]. rewrite sat_loop_step. destruct (r <? b); [|reflexivity]. rewrite IH. apply sb_lmc. Qed.
Lemma sat_dmc : forall f s b r, ds_d_max_code (send_all_trees_loop f s b r) = ds_d_max_code s.
Proof. induction f as [|f IH]; intros; [reflexivity|]. rewrite sat_loop_step. destruct (r <? b); [|reflexivity]. rewrite IH. apply sb_dmc. Qed.

Lemma st_tree_fc : forall X t mc t', tree_fc (send_tree X t mc) t' = tree_fc X t'.
Proof.
  intros X t mc t'. unfold send_tree. destruct (Len X t 0 =? 0).
  - exact (proj1 (send_loop_tree_fc (Z.to_nat (mc + 1)) X t mc 0 (-1) (Len X t 0) 0 138 3 t' ltac:(lia))).
  - exact (proj1 (send_loop_tree_fc (Z.to_nat (mc + 1)) X t mc 0 (-1) (Len X t 0) 0 7 4 t' ltac:(lia))).
Qed.
Lemma sat_tree_fc : forall f X b r t', tree_fc (send_all_trees_loop f X b r) t' = tree_fc X t'.
Proof.
  induction f as [|f IH]; intros; [reflexivity|]. rewrite sat_loop_step. destruct (r <? b); [|reflexivity].
  rewrite IH. apply sb_tree_fc.
Qed.


Local Ltac lrd H := destruct H as (HK & HRB & P6 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P22).
Definition LRP : list (Z * expr) :=
  KPN ++ [(5, EVar 47); (6, EVar 35); (10, ESub (EAdd (EVar 43) (ELit 1)) (EVar 45)); (11, EAdd (EVar 41) (ELit 1));
          (12, EAdd (EVar 32) (ELit 2748)); (13, ELit 14); (14, ELit 31); (15, EXor (EAdd (EVar 32) (ELit 2748)) (ELit (-1)));
          (16, EAdd (ELit 0x12410) (EVar 45)); (17, ELit 16); (18, EVar 42); (22, ELit 0)].

Definition HNEXT (mb r : Z) : word := if r + 1 =? mb + 1 then (0x1c9c0 : word) else (0x1c8d8 : word).

Lemma hiter : forall regs m1 m X mb r,
  FI m1 m X -> LR regs mb r X -> 0 <= mb <= 18 -> 0 <= r <= mb -> BINV PBL X -> sb_room PBL X 3 ->
  256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X) c < 16) ->
  let X' := send_bits X (Len X TB (arr_get bl_order_a r)) 3 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c8d8 : word) m s6u_rom) (mkst R (HNEXT mb r) m' s6u_rom)
    /\ FI m1 m' X'
    /\ (LR R mb (r + 1) X' /\ (forall r0 : reg, reg_in r0 [5; 6; 7; 10; 16; 28; 29; 30]%bv = false -> getr R r0 = getr regs r0)).
Proof.
  intros regs m1 m X mb r HF HL Hmb Hr HBI Hroom Hl Hd Hbl. cbv zeta.
  open_fi HF. lrd HL. kd HK. open_ubt HUB. destruct HBI as (Hbv & Hbb & Hpd). pose proof (u64_range (getr regs 5)) as U5.
  pose proof (bl_order_cells R6u _ _ trod_ok6u HRC) as BO. cbn [tr_bl_order R6u] in BO.
  pose proof (bl_order_bound r) as Bor.
  pose proof (Hbl (arr_get bl_order_a r) ltac:(lia)) as Vc.
  assert (Ev : pb (ds_bl_tree_dl X) (arr_get bl_order_a r) = arr_get (ds_bl_tree_dl X) (arr_get bl_order_a r)) by (apply pb_small; lia).
  assert (Hchk : zaluw ALU_SRL (pb (ds_bl_tree_dl X) (arr_get bl_order_a r)) (Z.lxor (ds_bi_valid X) (-1)) = 0)
    by (rewrite Ev; apply SendTree6u_1.srl_check0u; lia).
  unfold sb_room, Buf_size in Hroom. unfold HNEXT. unfold Len. cbn [tree_dl].
  destruct (Z.ltb_spec (16 - 3) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|];
    destruct (Z.eqb_spec (r + 1) (mb + 1)) as [Er|Er].
  - run lC 100%nat [false; false; false; false; false; false; false; false; false; false; false; false; true; true]
        [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45))); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; lmax X; dmax X; mb; 0; r; 0; bv_unsigned (getr regs 5)] X.
    all: match goal with |- ?g => idtac "HIF1" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold TFB6u_6.LR; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (5%bv : reg) HR nf | bv_flush (6%bv : reg) HR nf | rewrite sb_lmc; reg1 HR Hfr | rewrite sb_dmc; reg1 HR Hfr | reg1 HR Hfr ]).
  - run lC 100%nat [false; false; false; false; false; false; false; false; false; false; false; false; true; false]
        [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45))); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; lmax X; dmax X; mb; 0; r; 0; bv_unsigned (getr regs 5)] X.
    all: match goal with |- ?g => idtac "HIF2" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold TFB6u_6.LR; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (5%bv : reg) HR nf | bv_flush (6%bv : reg) HR nf | rewrite sb_lmc; reg1 HR Hfr | rewrite sb_dmc; reg1 HR Hfr | reg1 HR Hfr ]).
  - run lC 80%nat [true; false; false; true] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45)))] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; lmax X; dmax X; mb; 0; r; 0; bv_unsigned (getr regs 5)] X.
    all: match goal with |- ?g => idtac "HIK1" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold TFB6u_6.LR; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (5%bv : reg) HR nf | bv_keep (6%bv : reg) HR nf | rewrite sb_lmc; reg1 HR Hfr | rewrite sb_dmc; reg1 HR Hfr | reg1 HR Hfr ]).
  - run lC 80%nat [true; false; false; false] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45)))] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; lmax X; dmax X; mb; 0; r; 0; bv_unsigned (getr regs 5)] X.
    all: match goal with |- ?g => idtac "HIK2" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold TFB6u_6.LR; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (5%bv : reg) HR nf | bv_keep (6%bv : reg) HR nf | rewrite sb_lmc; reg1 HR Hfr | rewrite sb_dmc; reg1 HR Hfr | reg1 HR Hfr ]).
  all: match goal with |- ?g => idtac "HILEFT" g end.
Qed.

Lemma hloop : forall mb, 0 <= mb <= 18 -> forall k (f : nat) r regs m1 m X,
  r + Z.of_nat k = mb + 1 -> (1 <= k)%nat -> (k <= f)%nat -> 0 <= r ->
  FI m1 m X -> LR regs mb r X -> BINV PBL X -> sat_ok PBL f X (mb + 1) r ->
  256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X) c < 16) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1c8d8 : word) m s6u_rom) (mkst R (0x1c9c0 : word) m' s6u_rom)
    /\ FI m1 m' (send_all_trees_loop f X (mb + 1) r)
    /\ LR R mb (mb + 1) (send_all_trees_loop f X (mb + 1) r)
    /\ (forall r0 : reg, reg_in r0 [5; 6; 7; 10; 16; 28; 29; 30]%bv = false -> getr R r0 = getr regs r0).
Proof.
  intros mb Hmb. induction k as [|k IH]; intros f r regs m1 m X Hrk Hk Hf Hr0 HF HL HBI Hok Hl Hd Hbl; [lia|].
  destruct f as [|f]; [lia|]. rewrite sat_loop_step. rewrite sat_ok_step in Hok.
  replace (r <? mb + 1) with true in Hok |- * by (symmetry; apply Z.ltb_lt; lia). destruct Hok as [Hroom Hok].
  destruct (hiter regs m1 m X mb r HF HL Hmb ltac:(lia) HBI Hroom Hl Hd Hbl) as (R1 & ma & Hms1 & HF1 & HL1 & Hfr1).
  unfold HNEXT in Hms1. set (X' := send_bits X _ 3) in *.
  assert (HBI' : BINV PBL X') by (apply send_bits_BINV; [exact HBI | lia | exact Hroom]).
  assert (Hbl' : forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X') c < 16).
  { intros i Hi. subst X'. pose proof (sb_tree_dl_TB X (Len X TB (arr_get bl_order_a r)) 3) as E. cbn [tree_dl] in E. rewrite E. apply Hbl. exact Hi. }
  assert (Hl' : 256 <= lmax X' < 572) by (subst X'; rewrite sb_lmc; exact Hl).
  assert (Hd' : 0 <= dmax X' < 60) by (subst X'; rewrite sb_dmc; exact Hd).
  destruct k as [|k'].
  - replace (r + 1 =? mb + 1) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia).
    rewrite sat_loop_done by lia. replace (r + 1) with (mb + 1) in HL1 by lia.
    exists R1, ma. split; [exact Hms1|]. split; [exact HF1|]. split; [exact HL1 | exact Hfr1].
  - replace (r + 1 =? mb + 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH f (r + 1) R1 m1 ma X' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HF1 HL1 HBI' Hok Hl' Hd' Hbl')
      as (R2 & mb2 & Hms2 & HF2 & HL2 & Hfr2).
    exists R2, mb2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HF2|]. split; [exact HL2|].
    intros r0 Hq. rewrite (Hfr2 r0 Hq). exact (Hfr1 r0 Hq).
Qed.

End Walk.
End FXG.
