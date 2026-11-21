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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u FillWin6uD
  CompressBlk6u_1 CompressBlk6u_4 BuildTree6u_11 TrSmall6u TrStored6u ScanTree6u SendTree6u_1 SendTree6u_5 TFB6u_1 TFB6u_2 TFB6u_3 TFB6u_4 TFB6u_5.
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

Definition hC : cfg := CFG FBv [] [EVar 50%nat] [0x1c5cc; 0x1c828; 0x1c6a0; 0x1c85c; 0x1c76c; 0x1c888; 0x1c8d8] [].

Local Ltac flag0 HR :=
  lazymatch goal with |- getr ?R ?r = _ =>
    let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
    repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia);
    first [ replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
          | replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity ]
  end.
Local Ltac regw HR Hfr := first [ flag0 HR | reg1 HR Hfr ].

Local Abbreviation lmax X := (ds_l_max_code X).
Local Abbreviation dmax X := (ds_d_max_code X).


Definition S2PC (X7 : deflate_state) : word := if ds_bi_valid X7 <=? 11 then (0x1c828 : word) else (0x1c5cc : word).

Definition H1R (R : bvmap 5 word) (mb : Z) (X7 : deflate_state) : Prop :=
  KR R /\ getr R 10 = zw mb /\ getr R 11 = zw (lmax X7 + 1) /\ getr R 12 = zw 65535 /\ getr R 13 = zw (dmax X7 + 1)
  /\ getr R 14 = zw 0 /\ RBr 15%bv R X7 /\ getr R 16 = zw (ds_bi_valid X7) /\ getr R 17 = zw (lmax X7 - 256).
Local Ltac h1regs H := destruct H as (HK & P10 & P11 & P12 & P13 & P14 & HRB & P16 & P17).

Lemma sb_lmc : forall s v l, ds_l_max_code (send_bits s v l) = ds_l_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.
Lemma sb_dmc : forall s v l, ds_d_max_code (send_bits s v l) = ds_d_max_code s.
Proof. intros. rewrite send_bits_shape. destruct s; reflexivity. Qed.

Lemma stage1 : forall regs m1 m X mb,
  FI m1 m X -> KR regs -> getr regs 10 = zw mb -> getr regs 11 = zw (ds_bi_valid X) -> 0 <= mb <= 18 ->
  BINV PBL X -> sb_room PBL X 3 -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c454 : word) m s6u_rom) (mkst R (S2PC X7) m' s6u_rom)
    /\ FI m1 m' X7 /\ (H1R R mb X7 /\ (forall r : reg, reg_in r [5; 11; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF HK P10 P11 Hmb HBI Hroom Hl Hd. cbv zeta. change (Z.shiftl DYN_TREES 1 + last) with (4 + last).
  open_fi HF. kd HK. open_ubt HUB. destruct HBI as (Hbv & Hbb & Hpd). pose proof Hlast as Hlast'.
  pose proof (dsl_l_desc_max_code _ _ _ _ _ _ _ _ Hsc) as Cml. pose proof (dsl_d_desc_max_code _ _ _ _ _ _ _ _ Hsc) as Cmd.
  assert (Hchk : zaluw ALU_SRL (last + 4) (Z.lxor (ds_bi_valid X) (-1)) = 0) by (apply SendTree6u_1.srl_check0u; lia).
  unfold S2PC. unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - 3) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  -
    assert (Ebv : ds_bi_valid (send_bits X (4 + last) 3) = ds_bi_valid X + 3 - 16)
      by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. replace (ds_bi_valid X + 3 - 16 <=? 11) with true by (symmetry; apply Z.leb_le; lia).
    run hC 100%nat [false; false; false; false; false; false; false; false; false; false; false; false; true; false; false; true]
        [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RVal (EVar 41); RVal (EVar 42)]
        (KPN ++ [(10, EVar 43); (11, EVar 35)]) [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb] X.
    all: match goal with |- ?g => idtac "ST1F" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush ltac:(nf; replace (last + 4) with (4 + last) by lia))
      ltac:(split; [| fr_weak Hfr]; unfold H1R; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (15%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia)
                  | bv_flush (16%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  - assert (Ebv : ds_bi_valid (send_bits X (4 + last) 3) = ds_bi_valid X + 3)
      by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec (ds_bi_valid X + 3) 11) as [C2|C2].
    + run hC 60%nat [true; false; false; false; false; true] [RVal (EVar 36); RVal (EVar 41); RVal (EVar 42)]
          (KPN ++ [(10, EVar 43); (11, EVar 35)]) [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb] X.
      all: match goal with |- ?g => idtac "ST1K1" g end.
      site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep ltac:(nf; replace (last + 4) with (4 + last) by lia))
        ltac:(split; [| fr_weak Hfr]; unfold H1R; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (15%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia)
                    | bv_keep (16%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
    + run hC 60%nat [true; false; false; false; false; false] [RVal (EVar 36); RVal (EVar 41); RVal (EVar 42)]
          (KPN ++ [(10, EVar 43); (11, EVar 35)]) [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb] X.
      all: match goal with |- ?g => idtac "ST1K2" g end.
      site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep ltac:(nf; replace (last + 4) with (4 + last) by lia))
        ltac:(split; [| fr_weak Hfr]; unfold H1R; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (15%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia)
                    | bv_keep (16%bv : reg) HR ltac:(nf; replace (last + 4) with (4 + last) by lia) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST1LEFT" g end.
Qed.


Definition S3PC (X8 : deflate_state) : word := if 12 <=? ds_bi_valid X8 then (0x1c6a0 : word) else (0x1c85c : word).

Definition H2R (R : bvmap 5 word) (mb : Z) (X8 : deflate_state) : Prop :=
  KR R /\ getr R 10 = zw mb /\ getr R 11 = zw (lmax X8 + 1) /\ getr R 12 = zw 65535
  /\ RBr 14%bv R X8 /\ getr R 16 = zw (ds_bi_valid X8) /\ getr R 18 = zw (dmax X8) /\ getr R 22 = zw 0.
Local Ltac h2regs H := destruct H as (HK & P10 & P11 & P12 & HRB & P16 & P18 & P22).

Definition H1P : list (Z * expr) :=
  KPN ++ [(10, EVar 43); (11, EAdd (EVar 41) (ELit 1)); (12, ELit 65535); (13, EAdd (EVar 42) (ELit 1)); (14, ELit 0);
         (15, EVar 47); (16, EVar 35); (17, EAdd (EVar 41) (ELit (-256)))].

Lemma stage2k : forall regs m1 m X mb,
  FI m1 m X -> H1R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  0 <= ds_bi_valid X <= 11 ->
  let X8 := send_bits X (lmax X - 256) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c828 : word) m s6u_rom) (mkst R (S3PC X8) m' s6u_rom)
    /\ FI m1 m' X8 /\ (H2R R mb X8 /\ (forall r : reg, reg_in r [13; 14; 15; 16; 18; 22]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H1 Hmb HBI Hl Hd Hbv. cbv zeta.
  open_fi HF. h1regs H1. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 15)) as U15.
  unfold S3PC.
  assert (Ebv : ds_bi_valid (send_bits X (lmax X - 256) 5) = ds_bi_valid X + 5)
    by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
  rewrite Ebv. destruct (Z.leb_spec 12 (ds_bi_valid X + 5)) as [C2|C2].
  - run hC 60%nat [false; false; true] NoReads H1P
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 15)] X.
    all: match goal with |- ?g => idtac "ST2K1" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia))
      ltac:(split; [| fr_weak Hfr]; unfold H2R; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (14%bv : reg) HR ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia)
                  | bv_keep (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  - run hC 60%nat [false; false; false] NoReads H1P
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 15)] X.
    all: match goal with |- ?g => idtac "ST2K2" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia))
      ltac:(split; [| fr_weak Hfr]; unfold H2R; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (14%bv : reg) HR ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia)
                  | bv_keep (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST2KLEFT" g end.
Qed.

Lemma stage2f : forall regs m1 m X mb,
  FI m1 m X -> H1R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  12 <= ds_bi_valid X <= 16 -> ds_pending X + 2 <= PBL ->
  let X8 := send_bits X (lmax X - 256) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c5cc : word) m s6u_rom) (mkst R (S3PC X8) m' s6u_rom)
    /\ FI m1 m' X8 /\ (H2R R mb X8 /\ (forall r : reg, reg_in r [5; 6; 13; 14; 15; 16; 17; 18; 22]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H1 Hmb HBI Hl Hd Hbv Hroom. cbv zeta.
  open_fi HF. h1regs H1. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 15)) as U15.
  assert (Hchk : zaluw ALU_SRL (lmax X - 256) (Z.lxor (ds_bi_valid X) (-1)) = 0) by (apply SendTree6u_1.srl_check0u; lia).
  assert (Hchk' : zaluw ALU_SRL ((lmax X + -256) mod 2 ^ 16) (Z.lxor (ds_bi_valid X) (-1)) = 0).
  { replace (lmax X + -256) with (lmax X - 256) by lia. rewrite Z.mod_small by lia. exact Hchk. }
  unfold S3PC.
  assert (Ebv : ds_bi_valid (send_bits X (lmax X - 256) 5) = ds_bi_valid X + 5 - 16)
    by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
  rewrite Ebv. replace (12 <=? ds_bi_valid X + 5 - 16) with false by (symmetry; apply Z.leb_gt; lia).
  run hC 100%nat [false; false; false; false; false; false; false; false; false; false; false; false; true]
      [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H1P
      [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 15)] X.
  all: match goal with |- ?g => idtac "ST2F" g end.
  site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia))
    ltac:(split; [| fr_weak Hfr]; unfold H2R; split; [kregs HR Hfr|]; repeat split;
          first [ rb_flush (14%bv : reg) HR ltac:(nf; replace (lmax X + -256) with (lmax X - 256) by lia)
                | bv_flush (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST2FLEFT" g end.
Qed.

Lemma stage2 : forall regs m1 m X mb,
  FI m1 m X -> H1R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  sb_room PBL X 5 ->
  let X8 := send_bits X (lmax X - 256) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (S2PC X) m s6u_rom) (mkst R (S3PC X8) m' s6u_rom)
    /\ FI m1 m' X8 /\ (H2R R mb X8 /\ (forall r : reg, reg_in r [5; 6; 13; 14; 15; 16; 17; 18; 22]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H1 Hmb HBI Hl Hd Hroom. pose proof HBI as (Hbv & _ & _).
  unfold sb_room, Buf_size in Hroom. unfold S2PC.
  destruct (Z.leb_spec (ds_bi_valid X) 11) as [C|C].
  - destruct (stage2k regs m1 m X mb HF H1 Hmb HBI Hl Hd ltac:(lia)) as (R & m' & Hms & HF' & HR' & Hfr).
    exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HR' | fr_weak Hfr].
  - exact (stage2f regs m1 m X mb HF H1 Hmb HBI Hl Hd ltac:(lia) ltac:(lia)).
Qed.


Definition S4PC (X9 : deflate_state) : word := if 13 <=? ds_bi_valid X9 then (0x1c76c : word) else (0x1c888 : word).

Definition H3R (R : bvmap 5 word) (mb : Z) (X9 : deflate_state) : Prop :=
  KR R /\ getr R 10 = zw mb /\ getr R 11 = zw (lmax X9 + 1) /\ getr R 12 = zw 65535
  /\ RBr 13%bv R X9 /\ getr R 16 = zw (ds_bi_valid X9) /\ getr R 18 = zw (dmax X9) /\ getr R 22 = zw 0
  /\ getr R 14 = zw (mb - 3).
Local Ltac h3regs H := destruct H as (HK & P10 & P11 & P12 & HRB & P16 & P18 & P22 & P14).

Definition H2P : list (Z * expr) :=
  KPN ++ [(10, EVar 43); (11, EAdd (EVar 41) (ELit 1)); (12, ELit 65535); (14, EVar 47); (16, EVar 35); (18, EVar 42); (22, ELit 0)].

Lemma stage3k : forall regs m1 m X mb,
  FI m1 m X -> H2R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  0 <= ds_bi_valid X <= 11 ->
  let X9 := send_bits X (dmax X) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c85c : word) m s6u_rom) (mkst R (S4PC X9) m' s6u_rom)
    /\ FI m1 m' X9 /\ (H3R R mb X9 /\ (forall r : reg, reg_in r [13; 14; 15; 16]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H2 Hmb HBI Hl Hd Hbv. cbv zeta.
  open_fi HF. h2regs H2. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 14)) as U14.
  unfold S4PC.
  assert (Ebv : ds_bi_valid (send_bits X (dmax X) 5) = ds_bi_valid X + 5)
    by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
  rewrite Ebv. destruct (Z.leb_spec 13 (ds_bi_valid X + 5)) as [C2|C2].
  - run hC 60%nat [false; false; true] NoReads H2P
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 14)] X.
    all: match goal with |- ?g => idtac "ST3K1" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold H3R; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (13%bv : reg) HR ltac:(nf) | bv_keep (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  - run hC 60%nat [false; false; false] NoReads H2P
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 14)] X.
    all: match goal with |- ?g => idtac "ST3K2" g end.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold H3R; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (13%bv : reg) HR ltac:(nf) | bv_keep (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST3KLEFT" g end.
Qed.

Lemma stage3f : forall regs m1 m X mb,
  FI m1 m X -> H2R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  12 <= ds_bi_valid X <= 16 -> ds_pending X + 2 <= PBL ->
  let X9 := send_bits X (dmax X) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c6a0 : word) m s6u_rom) (mkst R (S4PC X9) m' s6u_rom)
    /\ FI m1 m' X9 /\ (H3R R mb X9 /\ (forall r : reg, reg_in r [5; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H2 Hmb HBI Hl Hd Hbv Hroom. cbv zeta.
  open_fi HF. h2regs H2. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 14)) as U14.
  assert (Hchk : zaluw ALU_SRL (dmax X) (Z.lxor (ds_bi_valid X) (-1)) = 0) by (apply SendTree6u_1.srl_check0u; lia).
  assert (Hchk' : zaluw ALU_SRL (dmax X mod 2 ^ 16) (Z.lxor (ds_bi_valid X) (-1)) = 0) by (rewrite Z.mod_small by lia; exact Hchk).
  unfold S4PC.
  assert (Ebv : ds_bi_valid (send_bits X (dmax X) 5) = ds_bi_valid X + 5 - 16)
    by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
  rewrite Ebv. replace (13 <=? ds_bi_valid X + 5 - 16) with false by (symmetry; apply Z.leb_gt; lia).
  run hC 100%nat [false; false; false; false; false; false; false; false; false; false; false; false; true]
      [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H2P
      [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 14)] X.
  all: match goal with |- ?g => idtac "ST3F" g end.
  site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
    ltac:(split; [| fr_weak Hfr]; unfold H3R; split; [kregs HR Hfr|]; repeat split;
          first [ rb_flush (13%bv : reg) HR ltac:(nf) | bv_flush (16%bv : reg) HR ltac:(nf) | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST3FLEFT" g end.
Qed.

Lemma stage3 : forall regs m1 m X mb,
  FI m1 m X -> H2R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  sb_room PBL X 5 ->
  let X9 := send_bits X (dmax X) 5 in
  exists R m',
    msteps s6u_segs (mkst regs (S3PC X) m s6u_rom) (mkst R (S4PC X9) m' s6u_rom)
    /\ FI m1 m' X9 /\ (H3R R mb X9 /\ (forall r : reg, reg_in r [5; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H2 Hmb HBI Hl Hd Hroom. pose proof HBI as (Hbv & _ & _).
  unfold sb_room, Buf_size in Hroom. unfold S3PC.
  destruct (Z.leb_spec 12 (ds_bi_valid X)) as [C|C].
  - exact (stage3f regs m1 m X mb HF H2 Hmb HBI Hl Hd ltac:(lia) ltac:(lia)).
  - destruct (stage3k regs m1 m X mb HF H2 Hmb HBI Hl Hd ltac:(lia)) as (R & m' & Hms & HF' & HR' & Hfr).
    exists R, m'. split; [exact Hms|]. split; [exact HF'|]. split; [exact HR' | fr_weak Hfr].
Qed.


Definition LR (R : bvmap 5 word) (mb r : Z) (X : deflate_state) : Prop :=
  KR R /\ RBr 5%bv R X /\ getr R 6 = zw (ds_bi_valid X) /\ getr R 10 = zw (mb + 1 - r)
  /\ getr R 11 = zw (lmax X + 1) /\ getr R 12 = zw (S + 2748) /\ getr R 13 = zw 14 /\ getr R 14 = zw 31
  /\ getr R 15 = zw (Z.lxor (S + 2748) (-1)) /\ getr R 16 = zw (0x12410 + r) /\ getr R 17 = zw 16
  /\ getr R 18 = zw (dmax X) /\ getr R 22 = zw 0.

Definition H3P : list (Z * expr) :=
  KPN ++ [(10, EVar 43); (11, EAdd (EVar 41) (ELit 1)); (12, ELit 65535); (13, EVar 47); (16, EVar 35); (18, EVar 42); (22, ELit 0);
         (14, EAdd (EVar 43) (ELit (-3)))].

Lemma stage4k : forall regs m1 m X mb,
  FI m1 m X -> H3R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  0 <= ds_bi_valid X <= 12 ->
  let X10 := send_bits X (mb - 3) 4 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c888 : word) m s6u_rom) (mkst R (0x1c8d8 : word) m' s6u_rom)
    /\ FI m1 m' X10 /\ (LR R mb 0 X10 /\ (forall r : reg, reg_in r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H3 Hmb HBI Hl Hd Hbv. cbv zeta.
  open_fi HF. h3regs H3. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 13)) as U13.
  run hC 60%nat [false] NoReads H3P
      [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 13)] X.
  all: match goal with |- ?g => idtac "ST4K" g end.
  site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep ltac:(nf; replace (mb + -3) with (mb - 3) by lia))
    ltac:(split; [| fr_weak Hfr]; unfold LR; split; [kregs HR Hfr|]; repeat split;
          first [ rb_keep (5%bv : reg) HR ltac:(nf; replace (mb + -3) with (mb - 3) by lia) | bv_keep (6%bv : reg) HR ltac:(nf)
                | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST4KLEFT" g end.
Qed.

Lemma stage4f : forall regs m1 m X mb,
  FI m1 m X -> H3R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  13 <= ds_bi_valid X <= 16 -> ds_pending X + 2 <= PBL ->
  let X10 := send_bits X (mb - 3) 4 in
  exists R m',
    msteps s6u_segs (mkst regs (0x1c76c : word) m s6u_rom) (mkst R (0x1c8d8 : word) m' s6u_rom)
    /\ FI m1 m' X10 /\ (LR R mb 0 X10 /\ (forall r : reg, reg_in r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H3 Hmb HBI Hl Hd Hbv Hroom. cbv zeta.
  open_fi HF. h3regs H3. kd HK. open_ubt HUB. destruct HBI as (_ & Hbb & Hpd).
  pose proof (u64_range (getr regs 13)) as U13.
  assert (Hchk : zaluw ALU_SRL (mb - 3) (Z.lxor (ds_bi_valid X) (-1)) = 0) by (apply SendTree6u_1.srl_check0u; lia).
  assert (Hchk' : zaluw ALU_SRL ((mb + -3) mod 2 ^ 16) (Z.lxor (ds_bi_valid X) (-1)) = 0).
  { replace (mb + -3) with (mb - 3) by lia. rewrite Z.mod_small by lia. exact Hchk. }
  run hC 100%nat [false; false; false; false; false; false; false; false; false; false; true]
      [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H3P
      [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; lmax X; dmax X; mb; 0; 0; 0; bv_unsigned (getr regs 13)] X.
  all: match goal with |- ?g => idtac "ST4F" g end.
  site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush ltac:(nf; replace (mb + -3) with (mb - 3) by lia))
    ltac:(split; [| fr_weak Hfr]; unfold LR; split; [kregs HR Hfr|]; repeat split;
          first [ rb_flush (5%bv : reg) HR ltac:(nf; replace (mb + -3) with (mb - 3) by lia) | bv_flush (6%bv : reg) HR ltac:(nf)
                | rewrite sb_lmc; regw HR Hfr | rewrite sb_dmc; regw HR Hfr | regw HR Hfr ]).
  all: match goal with |- ?g => idtac "ST4FLEFT" g end.
Qed.

Lemma stage4 : forall regs m1 m X mb,
  FI m1 m X -> H3R regs mb X -> 3 <= mb <= 18 -> BINV PBL X -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  sb_room PBL X 4 ->
  let X10 := send_bits X (mb - 3) 4 in
  exists R m',
    msteps s6u_segs (mkst regs (S4PC X) m s6u_rom) (mkst R (0x1c8d8 : word) m' s6u_rom)
    /\ FI m1 m' X10 /\ (LR R mb 0 X10 /\ (forall r : reg, reg_in r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF H3 Hmb HBI Hl Hd Hroom. pose proof HBI as (Hbv & _ & _).
  unfold sb_room, Buf_size in Hroom. unfold S4PC.
  destruct (Z.leb_spec 13 (ds_bi_valid X)) as [C|C].
  - exact (stage4f regs m1 m X mb HF H3 Hmb HBI Hl Hd ltac:(lia) ltac:(lia)).
  - exact (stage4k regs m1 m X mb HF H3 Hmb HBI Hl Hd ltac:(lia)).
Qed.


Local Ltac frw a Hr := rewrite (a _) by (eapply reg_in_sub; [|exact Hr]; reflexivity).

Lemma dynhdr : forall regs m1 m X mb,
  FI m1 m X -> KR regs -> getr regs 10 = zw mb -> getr regs 11 = zw (ds_bi_valid X) ->
  3 <= mb <= 18 -> 256 <= lmax X < 572 -> 0 <= dmax X < 60 ->
  let lmc := lmax X in
  let dmc := dmax X in
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  let X8 := send_bits X7 (lmc + 1 - 257) 5 in
  let X9 := send_bits X8 (dmc + 1 - 1) 5 in
  let X10 := send_bits X9 (mb + 1 - 4) 4 in
  BINV PBL X -> sb_room PBL X 3 -> sb_room PBL X7 5 -> sb_room PBL X8 5 -> sb_room PBL X9 4 ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1c454 : word) m s6u_rom) (mkst R (0x1c8d8 : word) m' s6u_rom)
    /\ FI m1 m' X10 /\ LR R mb 0 X10
    /\ (forall r : reg, reg_in r [5; 6; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mb HF HK P10 P11 Hmb Hl Hd. cbv zeta. intros HBI R3 R8 R9 R10.
  replace (lmax X + 1 - 257) with (lmax X - 256) in * by lia. replace (dmax X + 1 - 1) with (dmax X) in * by lia.
  replace (mb + 1 - 4) with (mb - 3) in * by lia.
  destruct (stage1 regs m1 m X mb HF HK P10 P11 ltac:(lia) HBI R3 Hl Hd) as (R1 & ma & Hms1 & HF1 & HR1 & Hfr1).
  set (X7 := send_bits X _ 3) in *.
  assert (HBI7 : BINV PBL X7) by (apply send_bits_BINV; [exact HBI | lia | exact R3]).
  assert (L7 : lmax X7 = lmax X) by (subst X7; apply sb_lmc). assert (D7 : dmax X7 = dmax X) by (subst X7; apply sb_dmc).
  destruct (stage2 R1 m1 ma X7 mb HF1 HR1 ltac:(lia) HBI7 ltac:(rewrite L7; exact Hl) ltac:(rewrite D7; exact Hd) R8)
    as (R2 & mb2 & Hms2 & HF2 & HR2 & Hfr2).
  rewrite L7 in Hms2, HF2, HR2.
  set (X8 := send_bits X7 _ 5) in *.
  assert (HBI8 : BINV PBL X8) by (apply send_bits_BINV; [exact HBI7 | lia | exact R8]).
  assert (L8 : lmax X8 = lmax X) by (subst X8; rewrite sb_lmc; exact L7). assert (D8 : dmax X8 = dmax X) by (subst X8; rewrite sb_dmc; exact D7).
  destruct (stage3 R2 m1 mb2 X8 mb HF2 HR2 Hmb HBI8 ltac:(rewrite L8; exact Hl) ltac:(rewrite D8; exact Hd) R9)
    as (R3' & mc3 & Hms3 & HF3 & HR3 & Hfr3).
  rewrite D8 in Hms3, HF3, HR3.
  set (X9 := send_bits X8 _ 5) in *.
  assert (HBI9 : BINV PBL X9) by (apply send_bits_BINV; [exact HBI8 | lia | exact R9]).
  assert (L9 : lmax X9 = lmax X) by (subst X9; rewrite sb_lmc; exact L8). assert (D9 : dmax X9 = dmax X) by (subst X9; rewrite sb_dmc; exact D8).
  destruct (stage4 R3' m1 mc3 X9 mb HF3 HR3 Hmb HBI9 ltac:(rewrite L9; exact Hl) ltac:(rewrite D9; exact Hd) R10)
    as (R4 & md & Hms4 & HF4 & HR4 & Hfr4).
  exists R4, md. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
  split; [exact HF4|]. split; [exact HR4|].
  intros r Hr. frw Hfr4 Hr. frw Hfr3 Hr. frw Hfr2 Hr. apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
End Walk.
End FXG.
