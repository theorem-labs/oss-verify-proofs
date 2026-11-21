(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod BitsLib BuildTreeLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel ScanModel SendModel TreesTab CompressModel
  BuildTreeModel GenBitlenModel RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
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

(* 1.4: the bi_used store (S + 5944) goes through BitsLib.BR_st_bi_used; the frame
   fact sub_franges F (S + 5944) 4 is taken from HFS (the S-frame covers dsl_SIZE). *)
Local Ltac br_fwd2 HB M :=
  lazymatch M with
  | wbytes ?M1 (zw (S + 5944)) (Z_to_le_bytes 4 ?v) =>
      br_fwd2 HB M1;
      lazymatch goal with
      | H1 : BR _ _ _ _ _ _ _ _ _ M1 _ |- _ =>
          let H2 := fresh "HBR" in
          assert (H2 : BR _ _ _ _ _ _ _ _ _ (wbytes M1 (zw (S + 5944)) (Z_to_le_bytes 4 v)) _) by (eapply BR_st_bi_used; eauto);
          clear H1
      end
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      br_fwd2 HB M1;
      lazymatch goal with
      | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 ?s1, HL : BRH ?F ?S ?p ?PBL |- _ =>
          let H2 := fresh "HBR" in
          lazymatch a with
          | S + 40 => pose proof (BR_st_pending sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5936 => pose proof (BR_st_bi_buf sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5940 => pose proof (BR_st_bi_valid sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5936 + 4 => pose proof (BR_st_bi_valid sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | _ =>
              first
                [ let Hi := fresh in
                  let ty := constr:(0 <= a - p_pending_buf p < PBL) in
                  assert (Hi : ty) by lia;
                  pose proof (BR_st_pb sg AL AD AB F mem0 S p PBL HL M1 s1 a (a - p_pending_buf p) v H1 ltac:(lia) Hi) as H2;
                  clear Hi
                | pose proof (BR_st_other sg AL AD AB F mem0 S p PBL HL M1 s1 a (Z_to_le_bytes w v) H1
                    ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes;
                          solve [eapply sub_franges_mono; [eassumption | cbn; lia | cbn; lia]])) as H2 ]
          end;
          clear H1
      end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Local Ltac site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd2 HB M;
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


Definition FRAME (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6_segs m (SP + 56) 8 (bv_unsigned ra)
  /\ cell s6_segs m (SP + 48) 8 (bv_unsigned (getr regs0 8)) /\ cell s6_segs m (SP + 40) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6_segs m (SP + 32) 8 (bv_unsigned (getr regs0 18)) /\ cell s6_segs m (SP + 24) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6_segs m (SP + 16) 8 (bv_unsigned (getr regs0 20)) /\ cell s6_segs m (SP + 8) 8 (bv_unsigned (getr regs0 21))
  /\ cell s6_segs m SP 8 (bv_unsigned (getr regs0 22)).

Lemma FRAME_keep : forall m m' regs0,
  (forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6_segs m' a w v) ->
  FRAME m regs0 -> FRAME m' regs0.
Proof using.
  intros m m' regs0 HC (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold FRAME.
  repeat split; (apply HC; [assumption | lia | cbn; lia]).
Qed.

Lemma FRAME_fi : forall m1 m X regs0, FI m1 m X -> FRAME m1 regs0 -> FRAME m regs0.
Proof using HPBL Hcf HLb HH last len bufp buf ds fx.
  intros m1 m X regs0 (_ & _ & HAG & _ & _) HF.
  pose proof Hcf as (Hsp0 & _ & _ & HfS & HfP). unfold TFB_FRAME, dsl_SIZE in *.
  pose proof HLb as ((HS1 & HS2) & (HP1 & HP2) & _).
  apply (FRAME_keep m1 m regs0); [|exact HF].
  intros a w v Hc Ha1 Ha2. apply (cell_agree_out s6_segs GFB m1 m a w v HAG); [| lia | lia | exact Hc].
  unfold TFB6_1.GFB. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; unfold dsl_SIZE in Hin; lia.
Qed.

Definition pC : cfg := CFG FBv [] [EVar 50%nat] [0x1afe8; 0x1b104; 0x1b8e4] [].


Lemma pro_blk : forall regs,
  0 <= ds_level ds < 2 ^ 31 ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw sp -> getr regs 1 = ra -> 0 <= bufp < 2 ^ 64 ->
  exists R m1,
    msteps s6_segs (mkst regs (0x1af98 : word) mem s6_rom)
           (mkst R (if 0 <? ds_level ds then (0x1afe8 : word) else (0x1b104 : word)) m1 s6_rom)
    /\ FI m1 m1 ds /\ FRAME m1 regs
    /\ (forall a w v, cell s6_segs mem a w v -> 0 <= a -> (a + Z.of_nat w <= SP \/ (sp <= a /\ a + Z.of_nat w <= 2 ^ 64)) -> cell s6_segs m1 a w v)
    /\ KR R /\ getr R 18 = zw len /\ getr R 19 = zw bufp /\ getr R 20 = zw (S + 2047)
    /\ (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof using Hsp HPBL Hcf Hlen Hlast HRC0 HBR0 HLb HH buf.
  intros regs Hlev P10 P11 P12 P13 P2 P1 Hbufp.
  pose proof HBR0 as HB. pose proof HPBL as HPBL'. pose proof HLb as HL'. destruct HL' as (HS' & HPB' & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  pose proof (dsl_level _ _ _ _ _ _ _ _ Hsc) as C196. clear Hsc.
  pose proof Hcf as (Hsp0 & HFf & Hmf & HfS & HfP). unfold TFB_FRAME, dsl_SIZE in Hsp0, HFf, Hmf, HfS, HfP.
  pose proof Hmf as MF. unfold mapped in MF.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19. pose proof (u64_range (getr regs 20)) as U20.
  pose proof (u64_range (getr regs 21)) as U21. pose proof (u64_range (getr regs 22)) as U22.
  assert (P2' : getr regs 2 = zw (SP + 64)) by (rewrite P2; f_equal; lia).
  assert (BRfr : forall M s0, BRm M s0 -> forall b v, SP <= b -> b + 8 <= sp -> BRm (wbytes M (zw b) (Z_to_le_bytes 8 v)) s0).
  { intros M s0 HM b v Hb1 Hb2.
    apply (BR_st_other _ _ _ _ F mem0 S p PBL HLb); [exact HM | lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; eapply sub_franges_mono; [exact HFf | cbn; lia | cbn; lia] ]. }
  assert (FIN : forall R M (pc : word),
    msteps s6_segs (mkst regs (0x1af98 : word) mem s6_rom) (mkst R pc M s6_rom) ->
    M = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
          (zw (SP + 56)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 1))))
          (zw (SP + 48)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 8))))
          (zw (SP + 40)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 9))))
          (zw (SP + 32)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 18))))
          (zw (SP + 24)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 19))))
          (zw (SP + 16)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 20))))
          (zw (SP + 8)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 21))))
          (zw SP) (Z_to_le_bytes 8 (bv_unsigned (getr regs 22))) ->
    KR R /\ getr R 18 = zw len /\ getr R 19 = zw bufp /\ getr R 20 = zw (S + 2047) ->
    (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r) ->
    exists R' m1,
      msteps s6_segs (mkst regs (0x1af98 : word) mem s6_rom) (mkst R' pc m1 s6_rom)
      /\ FI m1 m1 ds /\ FRAME m1 regs
      /\ (forall a w v, cell s6_segs mem a w v -> 0 <= a -> (a + Z.of_nat w <= SP \/ (sp <= a /\ a + Z.of_nat w <= 2 ^ 64)) -> cell s6_segs m1 a w v)
      /\ KR R' /\ getr R' 18 = zw len /\ getr R' 19 = zw bufp /\ getr R' 20 = zw (S + 2047)
      /\ (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%bv = false -> getr R' r = getr regs r)).
  { intros R M pc Hms -> HK Hfr. eexists R, _. split; [exact Hms|].
    split.
    { split; [repeat (apply BRfr; [|lia|lia]); exact HB|].
      split.
      { apply (trees_rod_clear_wr R6 _ _ HRC0).
        repeat (apply wr_ok_wbytes; [ | intros x Hx; rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply MF; lia
                                    | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]). apply wr_ok_refl. }
      split; [apply agree_out_refl|].
      split; [intros x Hx; repeat apply wbytes_grows; apply MF; lia|].
      intros x Hx; repeat apply wbytes_grows; exact Hx. }
    split.
    { unfold FRAME. rewrite <- P1. repeat split;
      repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                    | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]). }
    split.
    { intros a w v Hc Ha Hd.
      repeat (apply cell_write_other; [| lia | lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia]).
      exact Hc. }
    destruct HK as (HK1 & HK2 & HK3 & HK4). split; [exact HK1|]. split; [exact HK2|]. split; [exact HK3|]. split; [exact HK4 | exact Hfr]. }
  destruct (Z.ltb_spec 0 (ds_level ds)) as [CL|CL].
  - run pC 40%nat [false] [RVal (EVar 45)]
        [(10, EVar 32); (11, EVar 39); (12, EVar 38); (13, EVar 37); (2, EAdd (EVar 40) (ELit 64))]
        [S; PB; 0; 0; 0; last; len; bufp; SP; 0; 0; 0; 0; ds_level ds] ds.
    apply (FIN R _ _ Hms); [reflexivity | | fr_weak Hfr]. split; [kregs HR Hfr | regs_of HR Hfr].
  - run pC 40%nat [true] [RVal (EVar 45)]
        [(10, EVar 32); (11, EVar 39); (12, EVar 38); (13, EVar 37); (2, EAdd (EVar 40) (ELit 64))]
        [S; PB; 0; 0; 0; last; len; bufp; SP; 0; 0; 0; 0; ds_level ds] ds.
    apply (FIN R _ _ Hms); [reflexivity | | fr_weak Hfr]. split; [kregs HR Hfr | regs_of HR Hfr].
Qed.


Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m1 m X,
  FI m1 m X -> FRAME m regs0 -> KR regs ->
  exists R,
    msteps s6_segs (mkst regs (0x1b8e4 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof using Hsp HPBL Hcf Hlast Hret HLb HH len bufp buf ds.
  intros regs regs0 m1 m X HF (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22) HK. open_fi HF. kd HK.
  pose proof Hret as Hret'.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20.
  pose proof (u64_range (getr regs0 21)) as U21. pose proof (u64_range (getr regs0 22)) as U22.
  run pC 20%nat NoDirs
      [RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53); RVal (EVar 54); RVal (EVar 55); RVal (EVar 56); RVal (EVar 57)]
      KPN
      [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; 0; 0; 0; 0; 0;
       bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
       bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22)] X.
  exists R. split; [exact Hms|].
  split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|].
  split; [| fr_weak Hfr].
  intros r Hr. apply FillWin6D.reg_in_true_In in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reg1 HR Hfr.
Qed.


Local Ltac wind_bytes :=
  repeat first [ reflexivity | lia
               | lazymatch goal with
                 | |- wrap8 (?b mod 256) = wrap8 (Z.land ?b 255) => change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity
                 | |- wrap8 (?b / 256) = wrap8 (Z.shiftr (wrap16 ?b) 8) => rewrite wrap16_id by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity
                 | |- wrap8 (?b mod 256) = wrap8 ?b => rewrite !wrap8_mod'; change (2 ^ 8) with 256; rewrite Z.mod_mod by lia; reflexivity
                 end
               | f_equal ].

Lemma wind_blk : forall regs m1 m X,
  FI m1 m X -> BINV PBL X -> ds_pending (bi_windup X) <= PBL -> KR regs ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b870 : word) m s6_rom) (mkst R (0x1b8e4 : word) m' s6_rom)
    /\ FI m1 m' (bi_windup X) /\ KR R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof using Hsp HPBL Hcf Hlast HLb HFS HH len bufp buf ra ds.
  intros regs m1 m X HF HBI Hroom HK. open_fi HF. kd HK. destruct HBI as (Hbv & Hbb & Hpd).
  assert (Hbu : sub_franges F (S + 5944) 4) by (eapply sub_franges_mono; [exact HFS | lia | unfold dsl_SIZE; lia]).
  pose proof (cell2_lo _ _ _ _ C5936 ltac:(lia)) as Rlo.
  pose proof (cell2_hi _ _ _ _ C5936 ltac:(lia) ltac:(lia) ltac:(lia)) as Rhi.
  replace (S + 5936 + 1) with (S + 5937) in Rhi by lia.
  assert (Hlo : 0 <= ds_bi_buf X mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hhi : 0 <= ds_bi_buf X / 256 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (Z_lt_le_dec 8 (ds_bi_valid X)) as [C1|C1].
  - rewrite bi_windup_eq2 in Hroom |- * by lia. rewrite upd4_pending in Hroom.
    runv pC 60%nat [false] [RVal (EVar 35); RVal (EVar 34); RVal (EVar 33); RFresh; RFresh; RVal (EVar 35)] KPN
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP] [ds_bi_buf X mod 256; ds_bi_buf X / 256] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_eq; [wind_bytes | lia | reflexivity | reflexivity]) ltac:(split; [kregs HR Hfr | fr_weak Hfr]).
  - destruct (Z_lt_le_dec 0 (ds_bi_valid X)) as [C2|C2].
    + rewrite bi_windup_eq1 in Hroom |- * by lia. rewrite upd4_pending in Hroom.
      runv pC 60%nat [true; false] [RVal (EVar 35); RVal (EVar 34); RVal (EVar 33); RFresh; RVal (EVar 35)] KPN
          [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP] [ds_bi_buf X mod 256] X.
      site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_eq; [wind_bytes | lia | reflexivity | reflexivity]) ltac:(split; [kregs HR Hfr | fr_weak Hfr]).
    + rewrite bi_windup_eq0 by lia.
      runv pC 60%nat [true; true] [RVal (EVar 35); RVal (EVar 35)] KPN
          [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP] NoVals X.
      site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_eq; [wind_bytes | lia | reflexivity | reflexivity]) ltac:(split; [kregs HR Hfr | fr_weak Hfr]).
Qed.
End Walk.
End FXG.
