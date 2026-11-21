(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod BitsLib BuildTreeLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel ScanModel SendModel TreesTab CompressModel
  BuildTreeModel GenBitlenModel RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7 TFB6_8 TFB6_9 TFB6_10 TFB6_11 TFB6_12.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
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
Local Abbreviation call_st := (TFB6_1.call_st F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation call_ib := (TFB6_1.call_ib F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation call_cb := (TFB6_1.call_cb F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation LPC := (TFB6_11.LPC last).
Local Abbreviation ibg_blk := (TFB6_11.ibg_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation lt_blk := (TFB6_11.lt_blk F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation dynhdr := (TFB6_12.dynhdr F mem0 mem S p PBL ds ra sp buf bufp len last HH).


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

Definition dC : cfg := CFG FBv [] [EVar 50%nat] [0x1c6fc; 0x1c2a8; 0x1aaac] [].


Lemma g1_blk : forall regs m1 m X lmc,
  FI m1 m X -> KR regs -> getr regs 12 = zw lmc -> 0 <= lmc < 600 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b830 : word) m s6_rom) (mkst R (0x1c6fc : word) m s6_rom)
    /\ KR R /\ getr R 10 = zw S /\ getr R 11 = zw (S + 212) /\ getr R 12 = zw lmc /\ getr R 19 = zw (S + 212) /\ getr R 1 = zw 0x1b840
    /\ (forall r : reg, reg_in r [1; 10; 11; 19]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X lmc HF HK P12 Hlmc. open_fi HF. kd HK.
  run dC 8%nat NoDirs NoReads (KPN ++ [(12, EVar 41)]) [S; PB; 0; 0; 0; last; 0; 0; SP; lmc] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma g2_blk : forall regs m1 m X dmc,
  FI m1 m X -> KR regs -> getr regs 18 = zw dmc -> getr regs 20 = zw (S + 2047) -> 0 <= dmc < 600 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b840 : word) m s6_rom) (mkst R (0x1c6fc : word) m s6_rom)
    /\ KR R /\ getr R 10 = zw S /\ getr R 11 = zw (S + 2504) /\ getr R 12 = zw dmc /\ getr R 20 = zw (S + 2504) /\ getr R 1 = zw 0x1b854
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 20]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X dmc HF HK P18 P20 Hdmc. open_fi HF. kd HK.
  run dC 8%nat NoDirs NoReads (KPN ++ [(18, EVar 42); (20, EAdd (EVar 32) (ELit 2047))]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; dmc] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma g3_blk : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 19 = zw (S + 212) -> getr regs 20 = zw (S + 2504) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b854 : word) m s6_rom) (mkst R (0x1c2a8 : word) m s6_rom)
    /\ KR R /\ getr R 10 = zw S /\ getr R 11 = zw (S + 212) /\ getr R 12 = zw (S + 2504) /\ getr R 1 = zw 0x1b864
    /\ (forall r : reg, reg_in r [1; 10; 11; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P19 P20. open_fi HF. kd HK.
  run dC 8%nat NoDirs NoReads (KPN ++ [(19, EAdd (EVar 32) (ELit 212)); (20, EAdd (EVar 32) (ELit 2504))]) [S; PB; 0; 0; 0; last; 0; 0; SP] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.


Lemma dyn_tail : forall regs m1 m X11 lmc dmc,
  FI m1 m X11 -> KR regs -> getr regs 12 = zw lmc -> getr regs 18 = zw dmc -> getr regs 20 = zw (S + 2047) ->
  (0 <= lmc /\ lmc + 1 < 573) -> (0 <= dmc /\ dmc + 1 < 61) -> BINV PBL X11 ->
  let X12 := send_tree X11 TL lmc in
  let X13 := send_tree X12 TD dmc in
  let X14 := compress_block X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13) in
  ((forall i, 0 <= i <= lmc -> 0 <= Len X11 TL i <= 15) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X11 TL) i < 65536)
      /\ (forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc X11) c < 65536) /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X11) c < 16)
      /\ RefSendTree4.send_tree_safe PBL X11 TL lmc) ->
  ((forall i, 0 <= i <= dmc -> 0 <= Len X12 TD i <= 15) /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X12 TD) i < 65536)
      /\ (forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc X12) c < 65536) /\ (forall c, 0 <= c < 19 -> 0 <= arr_get (ds_bl_tree_dl X12) c < 16)
      /\ RefSendTree4.send_tree_safe PBL X12 TD dmc) ->
  (compress_block_ok PBL X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13)
      /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X13) i < 65536)
      /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X13) i < 65536)
      /\ (0 <= ds_sym_next X13 /\ ds_sym_next X13 + 3 < 2 ^ 31) /\ (0 <= ds_lit_bufsize X13 < 2 ^ 32)) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b830 : word) m s6_rom) (mkst R LPC m' s6_rom)
    /\ FI m1 m' (init_block X14) /\ KR R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X11 lmc dmc HF HK P12 P18 P20 Hlm Hdm HBI11. cbv zeta.
  intros (HLenL & HdlL & HbcL & HblL & HsafeL) (HLenD & HdlD & HbcD & HblD & HsafeD) (Hcb & Hlfc & Hdfc & Hsn & Hlb).
  pose proof HLb as ((HS1 & HS2) & _). unfold dsl_SIZE in HS2.
  destruct (g1_blk regs m1 m X11 lmc HF HK P12 ltac:(lia)) as (R0 & Hms0 & HK0 & A10 & A11 & A12 & A19 & A1 & Hfr0).
  destruct (call_st R0 m1 m X11 TL lmc (0x1b840%bv : word) HF ltac:(apply ret_ok_even; reflexivity)
              ltac:(left; reflexivity) ltac:(change (tsize TL) with 573; lia)
              HLenL ltac:(change (tsize TL) with 573; exact HdlL) HbcL HblL HBI11 HPBL HsafeL
              A10 ltac:(cbn [toff]; exact A11) A12 (proj2 (proj2 (proj2 (proj2 HK0)))) ltac:(rewrite A1; apply bv_eq; reflexivity))
    as (R1 & ma & Hms1 & HF1 & HP1 & _ & Q2a & Hfr1).
  set (X12 := send_tree X11 TL lmc) in *.
  destruct HP1 as (HBI12 & Tfc12 & Tdl12 & Hpl12 & Hlens12).
  assert (HK1 : KR R1 /\ getr R1 18 = zw dmc /\ getr R1 20 = zw (S + 2047)).
  { destruct HK0 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr1 8%bv eq_refl), !(Hfr1 9%bv eq_refl), !(Hfr1 21%bv eq_refl), !(Hfr1 22%bv eq_refl), Q2a,
            (Hfr1 18%bv eq_refl), (Hfr1 20%bv eq_refl), (Hfr0 18%bv eq_refl), (Hfr0 20%bv eq_refl).
    repeat split; assumption. }
  destruct HK1 as (HK1 & B18 & B20).
  destruct (g2_blk R1 m1 ma X12 dmc HF1 HK1 B18 B20 ltac:(lia)) as (R2 & Hms2 & HK2 & C10 & C11 & C12 & C20 & C1 & Hfr2).
  destruct (call_st R2 m1 ma X12 TD dmc (0x1b854%bv : word) HF1 ltac:(apply ret_ok_even; reflexivity)
              ltac:(right; reflexivity) ltac:(change (tsize TD) with 61; lia)
              HLenD ltac:(change (tsize TD) with 61; exact HdlD) HbcD HblD HBI12 HPBL HsafeD
              C10 ltac:(cbn [toff]; exact C11) C12 (proj2 (proj2 (proj2 (proj2 HK2)))) ltac:(rewrite C1; apply bv_eq; reflexivity))
    as (R3 & mb' & Hms3 & HF3 & HP3 & _ & Q2b & Hfr3).
  set (X13 := send_tree X12 TD dmc) in *.
  destruct HP3 as (HBI13 & Tfc13 & Tdl13 & Hpl13 & Hlens13).
  assert (HK3 : KR R3 /\ getr R3 19 = zw (S + 212) /\ getr R3 20 = zw (S + 2504)).
  { destruct HK2 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr3 8%bv eq_refl), !(Hfr3 9%bv eq_refl), !(Hfr3 21%bv eq_refl), !(Hfr3 22%bv eq_refl), Q2b,
            (Hfr3 19%bv eq_refl), (Hfr3 20%bv eq_refl), (Hfr2 19%bv eq_refl), (Hfr1 19%bv eq_refl).
    repeat split; assumption. }
  destruct HK3 as (HK3 & D19 & D20).
  destruct (g3_blk R3 m1 mb' X13 HF3 HK3 D19 D20) as (R4 & Hms4 & HK4 & E10 & E11 & E12 & E1 & Hfr4).
  assert (HT : forall m'' s', BR6 (Fmin S PB PBL SP 48) mb' S p PBL m'' s' ->
     (forall t, tree_fc s' t = tree_fc X13 t) -> (forall t, tree_dl s' t = tree_dl X13 t) -> trees_rod_clear6 m'' ->
     cells s6_segs m'' (S + 212) 4 2 286 (arr_get (ds_dyn_ltree_fc X13)) /\ cells s6_segs m'' (S + 212 + 2) 4 2 286 (arr_get (ds_dyn_ltree_dl X13))
     /\ cells s6_segs m'' (S + 2504) 4 2 30 (arr_get (ds_dyn_dtree_fc X13)) /\ cells s6_segs m'' (S + 2504 + 2) 4 2 30 (arr_get (ds_dyn_dtree_dl X13))).
  { intros m'' s' HB'' Hfc'' Hdl'' _.
    pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB'') as (_ & Har'' & _).
    pose proof (arrays_fc s6_segs _ _ _ TL Har'') as T1. pose proof (arrays_dl s6_segs _ _ _ TL Har'') as T2.
    pose proof (arrays_fc s6_segs _ _ _ TD Har'') as T3. pose proof (arrays_dl s6_segs _ _ _ TD Har'') as T4.
    rewrite Hfc'' in T1, T3. rewrite Hdl'' in T2, T4. cbn [toff tsize tree_fc tree_dl] in T1, T2, T3, T4.
    split; [intros i Hi; apply T1; lia|]. split; [intros i Hi; apply T2; lia|].
    split; [intros i Hi; apply T3; lia|]. intros i Hi; apply T4; lia. }
  destruct (call_cb R4 m1 mb' X13 (S + 212) (S + 2504) (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13)
              (0x1b864%bv : word) HF3 ltac:(apply ret_ok_even; reflexivity) Hcb HT ltac:(lia) ltac:(lia) Hsn Hlb HPBL
              E10 E11 E12 (proj2 (proj2 (proj2 (proj2 HK4)))) ltac:(rewrite E1; apply bv_eq; reflexivity))
    as (R5 & mc' & Hms5 & HF5 & _ & Q2c & Hfr5).
  assert (HK5 : KR R5).
  { destruct HK4 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr5 8%bv eq_refl), !(Hfr5 9%bv eq_refl), !(Hfr5 21%bv eq_refl), !(Hfr5 22%bv eq_refl), Q2c. repeat split; assumption. }
  destruct (ibg_blk (0x1b864%bv : word) 0x1b86c R5 m1 mc' _ ltac:(right; right; split; reflexivity) HF5 HK5) as (R6 & Hms6 & HK6 & G10 & G1 & Hfr6).
  destruct (call_ib R6 m1 mc' _ (0x1b86c%bv : word) HF5 ltac:(apply ret_ok_even; reflexivity) G10 ltac:(rewrite G1; apply bv_eq; reflexivity))
    as (R7 & md' & Hms7 & HF7 & _ & Hfr7).
  assert (HK7 : KR R7).
  { destruct HK6 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr7 8%bv eq_refl), !(Hfr7 9%bv eq_refl), !(Hfr7 21%bv eq_refl), !(Hfr7 22%bv eq_refl), !(Hfr7 2%bv eq_refl). repeat split; assumption. }
  destruct (lt_blk (0x1b86c%bv : word) R7 m1 md' _ ltac:(right; right; reflexivity) HF7 HK7) as (R8 & Hms8 & HK8 & Hfr8).
  exists R8, md'. split.
  { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|].
    eapply msteps_trans; [exact Hms6|]. eapply msteps_trans; [exact Hms7 | exact Hms8]. }
  split; [exact HF7|]. split; [exact HK8|].
  intros r Hr. rewrite (Hfr8 r eq_refl).
  rewrite (Hfr7 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr6 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr5 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr1 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Lemma sat_BINV : forall f X b r, 0 <= r -> BINV PBL X -> sat_ok PBL f X b r -> BINV PBL (send_all_trees_loop f X b r).
Proof.
  induction f as [|f IH]; intros X b r Hr HB Hok; [exact HB|].
  rewrite sat_loop_step. rewrite sat_ok_step in Hok. destruct (r <? b); [|exact HB].
  destruct Hok as [Hroom Hok]. apply IH; [lia| |exact Hok].
  apply send_bits_BINV; [exact HB | lia | exact Hroom].
Qed.

Lemma dyn_arm : forall regs m1 m X mb,
  FI m1 m X -> KR regs -> getr regs 10 = zw mb -> getr regs 20 = zw (S + 2047) -> getr regs 12 = zw (ds_bi_valid X) ->
  0 <= mb <= 18 -> dyn_ok PBL last X mb ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b534 : word) m s6_rom) (mkst R LPC m' s6_rom)
    /\ FI m1 m' (init_block (dyn_res last X mb)) /\ KR R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 28; 29; 30; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mb HF HK P10 P20 P12 Hmb HOK.
  destruct HOK as ((HBI & R3 & R8 & R9 & R10 & Rsat) & Hlm & Hdm & Hty & HL & HD & HCB).
  destruct (dynhdr regs m1 m X mb HF HK P10 P20 P12 Hmb ltac:(lia) ltac:(lia) Hty HBI R3 R8 R9 R10 Rsat)
    as (R1 & ma & Hms1 & HF1 & HK1 & A12 & A18 & A20 & Hfr1).
  assert (HBI11 : BINV PBL (send_all_trees_loop 19
     (send_bits (send_bits (send_bits (send_bits X (Z.shiftl DYN_TREES 1 + last) 3) (ds_l_max_code X + 1 - 257) 5) (ds_d_max_code X + 1 - 1) 5) (mb + 1 - 4) 4) (mb + 1) 0)).
  { apply sat_BINV; [lia| |exact Rsat].
    apply send_bits_BINV; [|lia|exact R10]. apply send_bits_BINV; [|lia|exact R9].
    apply send_bits_BINV; [|lia|exact R8]. apply send_bits_BINV; [exact HBI|lia|exact R3]. }
  destruct (dyn_tail R1 m1 ma _ (ds_l_max_code X) (ds_d_max_code X) HF1 HK1 A12 A18 A20 Hlm Hdm HBI11 HL HD HCB)
    as (R2 & mb2 & Hms2 & HF2 & HK2 & Hfr2).
  exists R2, mb2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [unfold dyn_res; exact HF2|]. split; [exact HK2|].
  intros r Hr.
  rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.
End FXG.
