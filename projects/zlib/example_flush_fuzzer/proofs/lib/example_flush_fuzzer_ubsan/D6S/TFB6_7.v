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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6.
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
Local Abbreviation cntsnz := SendTree6_1.cntsnz.
Local Abbreviation sc_upd := TFB6_5.sc_upd.
Local Abbreviation BR_st_blfc := (TFB6_5.BR_st_blfc F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation BR_st_dl_at := (TFB6_5.BR_st_dl_at F mem0 mem S p PBL ds ra sp buf bufp len last HH).


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


Definition VBS : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 65536); (37%nat, 2); (38%nat, 2 ^ 32);
   (39%nat, 2 ^ 64); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 600); (43%nat, 19); (44%nat, 2 ^ 64);
   (45%nat, 600); (46%nat, 16); (47%nat, 65536); (48%nat, 200); (49%nat, 65536); (50%nat, 200); (51%nat, 10)].

Definition sC : cfg := CFG FBv [] [EVar 1%nat] [0x1b288; 0x1b29c; 0x1b2bc; 0x1b300; 0x1b340] [].

Local Ltac runs fuel dirs rds pins pv X :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBS in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs sC fuel dirs rdv pinsv vbv NoRegions pv NoVals (TFB6_1.tfF X) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Definition SK (mc : Z) (R : bvmap 5 word) : Prop :=
  KR R /\ getr R 10 = zw (S + 2748) /\ getr R 13 = zw 4 /\ getr R 15 = zw 9 /\ getr R 14 = zw (S + 2510 + 4 + 4 * mc).
Definition SKP : list (Z * expr) :=
  KPN ++ [(10, EAdd (EVar 32) (ELit 2748)); (13, ELit 4); (15, ELit 9); (14, EAdd (EAdd (EVar 32) (ELit (2510 + 4))) (EShl (EVar 41) 2))].
Local Ltac skd H := destruct H as (HKR & Kbl & Kfour & Knine & Kend).
Local Ltac skregs HR Hfr := unfold SK; split; [kregs HR Hfr | regs_of HR Hfr].

Definition SH (mc : Z) (R : bvmap 5 word) (n pl c k mx mn : Z) : Prop :=
  SK mc R /\ getr R 12 = zw (S + 2510 + 4 * n) /\ getr R 11 = zw c /\ getr R 6 = zw k
  /\ getr R 17 = zw mx /\ getr R 5 = zw mn /\ getr R 28 = zw pl.
Local Ltac shd H := destruct H as (HSK & Pptr & P11 & Pk & Pmx & Pmn & Ppl).
Definition SHP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(12, EAdd (EAdd (EVar 32) (ELit 2510)) (EShl (EVar 45) 2)); (11, EVar 46); (6, EVar 48); (17, EVar 50); (5, EVar 51)] ++ plp.

Definition SD (mc : Z) (R : bvmap 5 word) (n pl c nl k mx mn : Z) : Prop :=
  SK mc R /\ getr R 12 = zw (S + 2510 + 4 * n) /\ getr R 16 = zw c /\ getr R 11 = zw nl
  /\ getr R 7 = zw (k + 1) /\ getr R 6 = zw k /\ getr R 17 = zw mx /\ getr R 5 = zw mn /\ getr R 28 = zw pl.
Local Ltac sdd H := destruct H as (HSK & Pptr & Pc & P11 & Pk1 & Pk & Pmx & Pmn & Ppl).
Definition SDP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(12, EAdd (EAdd (EVar 32) (ELit 2510)) (EShl (EVar 45) 2)); (16, EVar 46); (11, EVar 47);
          (7, EAdd (EVar 48) (ELit 1)); (6, EVar 48); (17, EVar 50); (5, EVar 51)] ++ plp.

Definition SG (mc : Z) (R : bvmap 5 word) (n c nl : Z) : Prop :=
  SK mc R /\ getr R 12 = zw (S + 2510 + 4 * n) /\ getr R 16 = zw c /\ getr R 11 = zw nl /\ getr R 7 = zw 0.
Local Ltac sgd H := destruct H as (HSK & Pptr & Pc & P11 & Pk1).
Definition SGP : list (Z * expr) :=
  SKP ++ [(12, EAdd (EAdd (EVar 32) (ELit 2510)) (EShl (EVar 45) 2)); (16, EVar 46); (11, EVar 47); (7, ELit 0)].

Definition STGT (nl : Z) : word := if nl =? 0 then (0x1b300 : word) else (0x1b2bc : word).
Definition SNEXT (mc n : Z) : word := if n + 1 =? mc + 1 then (0x1b340 : word) else (0x1b288 : word).

Definition SCL : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28]%bv.


Lemma s2h_emit : forall regs m1 m X mc n pl c k mx mn,
  FI m1 m X -> SH mc regs n pl c k mx mn -> 0 <= mc /\ mc + 1 < 61 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536) ->
  (mx <= k + 1 \/ c <> Len X TD (n + 1)) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b288 : word) m s6_rom) (mkst R (0x1b29c : word) m s6_rom)
    /\ SD mc R n pl c (Len X TD (n + 1)) k mx mn
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n pl c k mx mn HF HSH Hmc Hn Hc Hk Hmx Hmn Hdl Hcase.
  open_fi HF. shd HSH. skd HSK. kd HKR.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl X TD) (n + 1) = Len X TD (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  cbn [tree_dl] in Enl, Vnl.
  destruct (Z_le_gt_dec mx (k + 1)) as [C1|C1].
  - runs 30%nat [true] [RVal (EApp1 2 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SD. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 30%nat [false; false] [RVal (EApp1 2 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SD. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma s2h_cont : forall regs m1 m X mc n pl c k mx mn,
  FI m1 m X -> SH mc regs n pl c k mx mn -> 0 <= mc /\ mc + 1 < 61 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536) ->
  k + 1 < mx -> c = Len X TD (n + 1) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b288 : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
    /\ SH mc R (n + 1) pl c (k + 1) mx mn
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n pl c k mx mn HF HSH Hmc Hn Hc Hk Hmx Hmn Hdl C1 Ec.
  open_fi HF. shd HSH. skd HSK. kd HKR.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl X TD) (n + 1) = Len X TD (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  cbn [tree_dl] in Enl, Vnl. unfold SNEXT.
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - runs 30%nat [false; true; true] [RVal (EApp1 2 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 30%nat [false; true; false] [RVal (EApp1 2 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.


Lemma s2tnz : forall regs m1 m X mc n c nl,
  FI m1 m X -> SG mc regs n c nl -> 0 <= mc /\ mc + 1 < 61 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 < nl < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b2bc : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
    /\ SH mc R (n + 1) c nl 0 (fst (cntsnz c nl)) (snd (cntsnz c nl))
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n c nl HF HG Hmc Hn Hc Hnl. open_fi HF. sgd HG. skd HSK. kd HKR.
  unfold SendTree6_1.cntsnz, SNEXT.
  destruct (Z.eqb_spec c nl) as [Ecn|Ecn]; destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En]; cbn [fst snd].
  - subst c. runs 30%nat [true] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; nl; nl] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
  - subst c. runs 30%nat [false] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; nl; nl] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
  - runs 30%nat [true] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
  - runs 30%nat [false] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr. all: cnt_reg HR.
Qed.

Lemma s2tz : forall regs m1 m X mc n c,
  FI m1 m X -> SG mc regs n c 0 -> 0 <= mc /\ mc + 1 < 61 -> 0 <= n <= mc -> 0 <= c <= 15 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b300 : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
    /\ SH mc R (n + 1) c 0 0 138 3
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n c HF HG Hmc Hn Hc. open_fi HF. sgd HG. skd HSK. kd HKR. unfold SNEXT.
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - runs 30%nat [true] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 30%nat [false] NoReads SGP [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.


Local Ltac upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP i1 i2 tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      lazymatch M with
      | wbytes (wbytes ?M0 (zw ?a1) (Z_to_le_bytes 2 ?v1)) (zw ?a2) (Z_to_le_bytes 2 ?v2) =>
          let H1 := fresh "HBR" in let H2 := fresh "HBR" in
          pose proof (BR_st_blfc M0 _ i1 v1 a1 HB ltac:(lia) ltac:(lia)) as H1;
          pose proof (BR_st_blfc _ _ i2 v2 a2 H1 ltac:(lia) ltac:(lia)) as H2; clear H1;
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact H2|]; clear H2
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      | wbytes ?M0 (zw ?a1) (Z_to_le_bytes 2 ?v1) =>
          let H1 := fresh "HBR" in
          pose proof (BR_st_blfc M0 _ i1 v1 a1 HB ltac:(lia) ltac:(lia)) as H1;
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact H1|]; clear H1
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      end
  end.

Local Ltac upd_pre Hms HR Hfr HB HRC HAG MF HGR MS MP mc tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      lazymatch M with
      | wbytes ?M0 (zw ?a1) (Z_to_le_bytes 2 ?v1) =>
          let H1 := fresh "HBR" in
          pose proof (BR_st_dl_at M0 _ TD (mc + 1) v1 a1 HB ltac:(cbn; lia) ltac:(cbn; lia)) as H1;
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact H1|]; clear H1
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [ ag_tower HAG
                                          | split; [ intros x Hx; repeat apply wbytes_grows; apply MF; exact Hx
                                                   | intros x Hx; repeat apply wbytes_grows; apply HGR; exact Hx ] ] ] ]
                 | tregs ]
      end
  end.

Local Ltac freq_eq :=
  unfold set_Freq, Freq; cbn [tree_fc set_tree_fc TFB6_1.tfF]; dsred;
  repeat first [ reflexivity | lia
               | rewrite arr_get_set_other by lia
               | lazymatch goal with |- wrap16 ?a = wrap16 (arr_get ?b ?i + ?y) =>
                   replace a with (szwrap 16 (pb b i) + y) by lia; apply wrap16_szpb_add end
               | f_equal ].

Lemma s2upd : forall regs m1 m X mc n pl c nl k mx mn,
  FI m1 m X -> SD mc regs n pl c nl k mx mn -> 0 <= mc /\ mc + 1 < 61 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= nl < 65536 ->
  0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 -> (pl = -1 \/ 0 <= pl <= 15) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b29c : word) m s6_rom) (mkst R (STGT nl) m' s6_rom)
    /\ FI m1 m' (sc_upd X mn c pl (k + 1))
    /\ (SG mc R n c nl /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mc n pl c nl k mx mn HF HSD Hmc Hn Hc Hnl Hk Hmx Hmn Hpl Hty.
  open_fi HF. sdd HSD. skd HSK. kd HKR.
  pose proof HB as (_ & _ & HTL & _). unfold tree_lens in HTL. cbn [tree_fc tree_dl] in HTL.
  assert (Evc : forall i, 0 <= i < 39 -> pb (ds_bl_tree_fc X) i = arr_get (ds_bl_tree_fc X) i) by (intros i Hi; apply pb_small; apply Hty; exact Hi).
  unfold STGT, sc_upd. change REP_3_6 with 16. change REPZ_3_10 with 17. change REPZ_11_138 with 18.
  destruct (Z.ltb_spec (k + 1) mn) as [Cm|Cm].
  -
    destruct (Z.eqb_spec nl 0) as [Enl|Enl].
    + runs 40%nat [false; true] [RVal (EApp1 3 (EVar 46))] (SDP [])
          [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
      upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c c ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
      freq_eq.
    + runs 40%nat [false; false] [RVal (EApp1 3 (EVar 46))] (SDP [])
          [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
      upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c c ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
      freq_eq.
  - replace (k + 1 <=? 10) with (k <=? 9) by (destruct (Z.leb_spec (k + 1) 10), (Z.leb_spec k 9); try reflexivity; lia).
    destruct (Z.eqb_spec c 0) as [Cz|Cz]; cbn [negb].
    +
      subst c.
      destruct (Z.leb_spec k 9) as [Kn9|Kn9]; destruct (Z.eqb_spec nl 0) as [Enl|Enl].
      * runs 40%nat [true; true; false; false] [RVal (EApp1 3 (ELit 17))] (SDP [])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; 0; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 17 17 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * runs 40%nat [true; true; false; true] [RVal (EApp1 3 (ELit 17))] (SDP [])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; 0; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 17 17 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * runs 40%nat [true; true; true; false] [RVal (EApp1 3 (ELit 18))] (SDP [])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; 0; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 18 18 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * runs 40%nat [true; true; true; true] [RVal (EApp1 3 (ELit 18))] (SDP [])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; 0; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 18 18 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
    +
      destruct (Z.eqb_spec c pl) as [Ecp|Ecp]; cbn [negb]; destruct (Z.eqb_spec nl 0) as [Enl|Enl].
      * subst pl. runs 40%nat [true; false; true; false] [RVal (EApp1 3 (ELit 16))] (SDP [(28, EVar 46)])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 16 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * subst pl. runs 40%nat [true; false; true; true] [RVal (EApp1 3 (ELit 16))] (SDP [(28, EVar 46)])
            [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
        upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP 16 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
        freq_eq.
      * destruct Hpl as [Hpl|Hpl].
        -- subst pl. runs 40%nat [true; false; false; false] [RVal (EApp1 3 (EVar 46)); RVal (EApp1 3 (ELit 16))] (SDP [(28, ELit 18446744073709551615)])
              [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
           upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
        -- runs 40%nat [true; false; false; false] [RVal (EApp1 3 (EVar 46)); RVal (EApp1 3 (ELit 16))] (SDP [(28, EVar 49)])
              [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; pl; mx; mn] X.
           upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
      * destruct Hpl as [Hpl|Hpl].
        -- subst pl. runs 40%nat [true; false; false; true] [RVal (EApp1 3 (EVar 46)); RVal (EApp1 3 (ELit 16))] (SDP [(28, ELit 18446744073709551615)])
              [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; 0; mx; mn] X.
           upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
        -- runs 40%nat [true; false; false; true] [RVal (EApp1 3 (EVar 46)); RVal (EApp1 3 (ELit 16))] (SDP [(28, EVar 49)])
              [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; nl; k; pl; mx; mn] X.
           upd_fin Hms HR Hfr HB HRC HAG MF HGR MS MP c 16 ltac:(split; [| fr_weak Hfr]; unfold SG; split; [skregs HR Hfr|]; regs_of HR Hfr).
           freq_eq.
Qed.


Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

Lemma s2loop : forall m1 mc, 0 <= mc /\ mc + 1 < 61 ->
  forall f n, 0 <= n -> mc + 1 - n <= Z.of_nat f ->
  forall regs m X pl c k mx mn,
    FI m1 m X -> SH mc regs n pl c k mx mn -> n <= mc -> SendTree6_5.BND pl c k mx mn -> c = Len X TD n ->
    (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536) ->
    (forall i, 0 <= i <= mc -> 0 <= Len X TD i <= 15) ->
    (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) ->
    exists R m',
      msteps s6_segs (mkst regs (0x1b288 : word) m s6_rom) (mkst R (0x1b340 : word) m' s6_rom)
      /\ FI m1 m' (scan_tree_loop (Z.to_nat (mc + 1 - n)) X TD mc n pl c k mx mn)
      /\ SK mc R
      /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros m1 mc Hmc. induction f as [|f IH]; intros n Hn0 Hf regs m X pl c k mx mn HF HSH Hn HB Ec Hdl Hl15 Hty; [exfalso; lia|].
  pose proof (SendTree6_5.BND_facts _ _ _ _ _ HB) as (Bmx & Bmn & Bc0 & Bc1 & Bc2). pose proof HB as (Bpl & Bc & Bk & Bcn).
  pose proof (Hdl (n + 1) ltac:(lia)) as R1.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite scan_loop_S'. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  set (nl := Len X TD (n + 1)) in *.
  assert (Rnl : 0 <= nl < 65536) by (unfold nl, Len; exact R1).
  assert (IHn : forall R' m' X' pl' c' k' mx' mn',
            FI m1 m' X' -> SH mc R' (n + 1) pl' c' k' mx' mn' -> n + 1 <= mc -> SendTree6_5.BND pl' c' k' mx' mn' -> c' = Len X' TD (n + 1) ->
            (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X' TD) i < 65536) ->
            (forall i, 0 <= i <= mc -> 0 <= Len X' TD i <= 15) ->
            (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X') i < 65536) ->
            exists R m'', msteps s6_segs (mkst R' (0x1b288 : word) m' s6_rom) (mkst R (0x1b340 : word) m'' s6_rom)
              /\ FI m1 m'' (scan_tree_loop (Z.to_nat (mc + 1 - (n + 1))) X' TD mc (n + 1) pl' c' k' mx' mn')
              /\ SK mc R /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr R' r)).
  { intros. apply (IH (n + 1)); try assumption; lia. }
  assert (LATCH : forall R' m' X' pl' c' k' mx' mn',
            FI m1 m' X' -> SH mc R' (n + 1) pl' c' k' mx' mn' -> (n + 1 <= mc -> SendTree6_5.BND pl' c' k' mx' mn') -> c' = Len X' TD (n + 1) ->
            (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X' TD) i < 65536) ->
            (forall i, 0 <= i <= mc -> 0 <= Len X' TD i <= 15) ->
            (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X') i < 65536) ->
            exists R m'', msteps s6_segs (mkst R' (SNEXT mc n) m' s6_rom) (mkst R (0x1b340 : word) m'' s6_rom)
              /\ FI m1 m'' (scan_tree_loop (Z.to_nat (mc + 1 - (n + 1))) X' TD mc (n + 1) pl' c' k' mx' mn')
              /\ SK mc R /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr R' r)).
  { intros R' m' X' pl' c' k' mx' mn' HF' HSH' HB' Ec' Hdl' Hl15' Hty'. unfold SNEXT.
    destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
    - rewrite scan_loop_out by lia. exists R', m'. split; [apply mst_refl|]. split; [exact HF'|].
      split; [exact (proj1 HSH') | intros r Hr; reflexivity].
    - apply (IHn R' m' X' pl' c' k' mx' mn' HF' HSH' ltac:(lia) (HB' ltac:(lia)) Ec' Hdl' Hl15' Hty'). }
  destruct (Sumbool.sumbool_of_bool ((k + 1 <? mx) && (c =? nl))) as [CC|CC]; rewrite CC.
  -
    apply andb_prop in CC. destruct CC as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    destruct (s2h_cont regs m1 m X mc n pl c k mx mn HF HSH Hmc ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) Hdl C1 C2)
      as (Ra & Hmsa & HSHa & Hfra).
    destruct (LATCH Ra m X pl nl (k + 1) mx mn HF ltac:(rewrite <- C2; exact HSHa)
                ltac:(intros Hle; unfold SendTree6_5.BND; rewrite <- C2; repeat split; try lia; exact Bcn) eq_refl Hdl Hl15 Hty)
      as (Rb & mb & Hmsb & HFb & HSKb & Hfrb).
    exists Rb, mb. split; [eapply msteps_trans; [exact Hmsa | exact Hmsb]|]. split; [exact HFb|]. split; [exact HSKb | frc2 Hfrb Hfra].
  -
    assert (Hcase : mx <= k + 1 \/ c <> nl).
    { apply Bool.andb_false_iff in CC. destruct CC as [C1|C1]; [apply Z.ltb_ge in C1; lia | apply Z.eqb_neq in C1; lia]. }
    destruct (s2h_emit regs m1 m X mc n pl c k mx mn HF HSH Hmc ltac:(lia) Bc Bk ltac:(lia) ltac:(lia) Hdl Hcase)
      as (Rd & Hmsd & HSD & Hfrd).
    destruct (s2upd Rd m1 m X mc n pl c nl k mx mn HF HSD Hmc ltac:(lia) Bc ltac:(lia) Bk ltac:(lia) ltac:(lia) Bpl Hty)
      as (Ru & mu & Hmsu & HFu & HSGu & Hfru).
    set (X' := sc_upd X mn c pl (k + 1)) in *.
    assert (HTL : arr_len (ds_bl_tree_fc X) = 39).
    { destruct HF as (HBx & _). destruct HBx as (_ & _ & HL & _). unfold tree_lens in HL. tauto. }
    pose proof (TFB6_5.sc_upd_typed X mn c pl (k + 1) Hty HTL) as [Hty' HTL']. fold X' in Hty', HTL'.
    assert (Hdl' : forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X' TD) i < 65536) by (intros i Hi; subst X'; rewrite TFB6_5.sc_upd_tree_dl; apply Hdl; exact Hi).
    assert (Hl15x : forall i, 0 <= i <= mc -> 0 <= Len X' TD i <= 15) by (intros i Hi; subst X'; rewrite TFB6_5.sc_upd_Len; apply Hl15; exact Hi).
    assert (Enl' : nl = Len X' TD (n + 1)) by (subst X'; rewrite TFB6_5.sc_upd_Len; reflexivity).
    rewrite SendTree6_5.cnts_tree_counts. unfold SendTree6_5.cnts in *; unfold STGT in *.
    destruct (Z.eqb_spec nl 0) as [E1|E1].
    +
      rewrite E1 in HSGu |- *.
      destruct (s2tz Ru m1 mu X' mc n c HFu HSGu Hmc ltac:(lia) Bc) as (Rt & Hmst & HSHt & Hfrt).
      destruct (LATCH Rt mu X' c 0 0 138 3 HFu HSHt ltac:(intros Hle; unfold SendTree6_5.BND, SendTree6_5.cnts; cbn; repeat split; lia)
                  ltac:(rewrite <- Enl'; symmetry; exact E1) Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HFb & HSKb & Hfrb).
      exists Rb, mb. split.
      { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
      split; [exact HFb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
    + destruct (s2tnz Ru m1 mu X' mc n c nl HFu HSGu Hmc ltac:(lia) Bc ltac:(lia)) as (Rt & Hmst & HSHt & Hfrt).
      unfold SendTree6_1.cntsnz in HSHt. rewrite (Z.eqb_sym c nl) in HSHt.
      destruct (Z.eqb_spec nl c) as [E2|E2]; cbn [fst snd] in HSHt.
      * destruct (LATCH Rt mu X' c nl 0 6 3 HFu HSHt
                    ltac:(intros Hle; pose proof (Hl15 (n + 1) ltac:(lia)) as L15; unfold SendTree6_5.BND, SendTree6_5.cnts; replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
                          rewrite E2, Z.eqb_refl; repeat split; lia)
                    Enl' Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HFb & HSKb & Hfrb).
        exists Rb, mb. split.
        { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
        split; [exact HFb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
      * destruct (LATCH Rt mu X' c nl 0 7 4 HFu HSHt
                    ltac:(intros Hle; pose proof (Hl15 (n + 1) ltac:(lia)) as L15; unfold SendTree6_5.BND, SendTree6_5.cnts; replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
                          replace (nl =? c) with false by (symmetry; apply Z.eqb_neq; lia); repeat split; lia)
                    Enl' Hdl' Hl15x Hty') as (Rb & mb & Hmsb & HFb & HSKb & Hfrb).
        exists Rb, mb. split.
        { eapply msteps_trans; [exact Hmsd|]. eapply msteps_trans; [exact Hmsu|]. eapply msteps_trans; [exact Hmst | exact Hmsb]. }
        split; [exact HFb|]. split; [exact HSKb|]. intros r Hr. rewrite (Hfrb r Hr), (Hfrt r Hr), (Hfru r Hr). exact (Hfrd r Hr).
Qed.


Definition scnts0 (X : deflate_state) : Z * Z := if Len X TD 0 =? 0 then (138, 3) else (7, 4).

Lemma s2pre : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 20 = zw (S + 2047) -> getr regs 10 = zw 18446744073709551615 ->
  0 <= ds_d_max_code X /\ ds_d_max_code X + 1 < 61 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536) ->
  (forall i, 0 <= i <= ds_d_max_code X -> 0 <= Len X TD i <= 15) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b20c : word) m s6_rom) (mkst R (0x1b288 : word) m' s6_rom)
    /\ FI m1 m' (set_Len X TD (ds_d_max_code X + 1) 65535)
    /\ SH (ds_d_max_code X) R 0 (-1) (Len X TD 0) 0 (fst (scnts0 X)) (snd (scnts0 X))
    /\ True
    /\ (forall r : reg, reg_in r (10 :: 5 :: 6 :: 7 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 28 :: 29 :: nil)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P20 P10 Hmc Hdl Hl15. open_fi HF. kd HK.
  pose proof (dsl_d_desc_max_code _ _ _ _ _ _ _ _ Hsc) as Cmc.
  pose proof (Hdl 0 ltac:(lia)) as R0. pose proof (Hl15 0 ltac:(lia)) as V0.
  assert (E0 : pb (tree_dl X TD) 0 = Len X TD 0) by (unfold Len; apply pb_small; exact R0).
  unfold scnts0. unfold Len in *. cbn [tree_dl] in *.
  destruct (Z.eqb_spec (arr_get (ds_dyn_dtree_dl X) 0) 0) as [CZ|CZ]; cbn [fst snd].
  - runs 60%nat [false; true] [RVal (EVar 41); RVal (EApp1 2 (ELit 0))] (KPN ++ [(20, EAdd (EVar 32) (ELit 2047)); (10, ELit 18446744073709551615)])
        [S; PB; 0; 0; 0; last; 0; 0; SP; ds_d_max_code X] X.
    upd_pre Hms HR Hfr HB HRC HAG MF HGR MS MP (ds_d_max_code X)
      ltac:(split; [unfold SH; split; [skregs HR Hfr|]; regs_of HR Hfr | split; [exact I | fr_weak Hfr]]).
    all: try (unfold set_Len, set_Dad; cbn [tree_dl set_tree_dl]; reflexivity).
    all: try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; f_equal; nf; rewrite E0, CZ; reflexivity end).
  - runs 60%nat [false; false] [RVal (EVar 41); RVal (EApp1 2 (ELit 0))] (KPN ++ [(20, EAdd (EVar 32) (ELit 2047)); (10, ELit 18446744073709551615)])
        [S; PB; 0; 0; 0; last; 0; 0; SP; ds_d_max_code X] X.
    upd_pre Hms HR Hfr HB HRC HAG MF HGR MS MP (ds_d_max_code X)
      ltac:(split; [unfold SH; split; [skregs HR Hfr|]; regs_of HR Hfr | split; [exact I | fr_weak Hfr]]).
    all: try (unfold set_Len, set_Dad; cbn [tree_dl set_tree_dl]; reflexivity).
    all: try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; f_equal; nf; rewrite E0;
              replace (0 <? arr_get _ 0) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity end).
Qed.

Lemma s2phase : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 20 = zw (S + 2047) -> getr regs 10 = zw 18446744073709551615 ->
  0 <= ds_d_max_code X /\ ds_d_max_code X + 1 < 61 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536) ->
  (forall i, 0 <= i <= ds_d_max_code X -> 0 <= Len X TD i <= 15) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b20c : word) m s6_rom) (mkst R (0x1b340 : word) m' s6_rom)
    /\ FI m1 m' (scan_tree X TD (ds_d_max_code X))
    /\ KR R /\ True
    /\ (forall r : reg, reg_in r (10 :: 5 :: 6 :: 7 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 28 :: 29 :: nil)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P20 P10 Hmc Hdl Hl15 Hty.
  set (mc := ds_d_max_code X) in *.
  destruct (s2pre regs m1 m X HF HK P20 P10 Hmc Hdl Hl15) as (R1 & ma & Hms1 & HF1 & HSH1 & Q10 & Hfr1).
  assert (HTL : arr_len (tree_dl X TD) = 61).
  { destruct HF as (HBx & _). destruct HBx as (_ & _ & HL & _). apply (tree_lens_dl X TD) in HL. exact HL. }
  set (X1 := set_Len X TD (mc + 1) 65535) in *.
  assert (EL : forall i, i <> mc + 1 -> Len X1 TD i = Len X TD i).
  { intros i Hi. subst X1. rewrite Len_set_Len by (rewrite HTL; lia). replace (mc + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (Hdl1 : forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X1 TD) i < 65536).
  { intros i Hi. subst X1. unfold set_Len, set_Dad. rewrite tree_dl_set_tree_dl. rewrite arr_get_set.
    destruct (_ && _); [rewrite wrap16_mod'; change (2 ^ 16) with 65536; apply Z.mod_pos_bound; lia | apply Hdl; exact Hi]. }
  assert (Hl151 : forall i, 0 <= i <= mc -> 0 <= Len X1 TD i <= 15) by (intros i Hi; rewrite EL by lia; apply Hl15; exact Hi).
  assert (Hty1 : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X1) i < 65536) by (intros i Hi; subst X1; apply Hty; exact Hi).
  assert (HB0 : SendTree6_5.BND (-1) (Len X TD 0) 0 (fst (scnts0 X)) (snd (scnts0 X))).
  { pose proof (Hl15 0 ltac:(lia)) as L0. unfold SendTree6_5.BND, SendTree6_5.cnts, scnts0.
    destruct (Z.eqb_spec (Len X TD 0) 0); cbn [fst snd]; [repeat split; lia|].
    replace (Len X TD 0 =? -1) with false by (symmetry; apply Z.eqb_neq; lia). repeat split; lia. }
  destruct (s2loop m1 mc Hmc (Datatypes.S (Z.to_nat (mc + 1))) 0 ltac:(lia) ltac:(lia) R1 ma X1 (-1) (Len X TD 0) 0 (fst (scnts0 X)) (snd (scnts0 X))
              HF1 HSH1 ltac:(lia) HB0 ltac:(symmetry; apply EL; lia) Hdl1 Hl151 Hty1) as (R2 & mb & Hms2 & HF2 & HSK2 & Hfr2).
  exists R2, mb. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split.
  { unfold scan_tree. fold mc. unfold scnts0 in HF2. replace (mc + 1 - 0) with (mc + 1) in HF2 by lia. subst X1.
    destruct (Len X TD 0 =? 0); exact HF2. }
  split; [exact (proj1 HSK2)|]. split; [exact I|].
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr1. exact Hr.
Qed.
End Walk.
End FXG.
