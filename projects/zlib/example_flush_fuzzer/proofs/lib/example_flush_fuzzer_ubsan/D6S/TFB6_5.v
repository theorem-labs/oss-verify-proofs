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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4.
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


Lemma wrap16_szwrap16_add : forall x y, wrap16 (szwrap 16 x + y) = wrap16 (x + y).
Proof.
  intros x y. rewrite !wrap16_mod'. rewrite <- Zplus_mod_idemp_l, (szwrap_eqm 16 x) by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma wrap16_pb_add : forall (b : arr) i y, wrap16 (pb b i + y) = wrap16 (arr_get b i + y).
Proof. intros b i y. unfold pb. rewrite !wrap16_mod'. change 65536 with (2 ^ 16). rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma wrap16_szpb_add : forall (b : arr) i y, wrap16 (szwrap 16 (pb b i) + y) = wrap16 (arr_get b i + y).
Proof. intros b i y. rewrite wrap16_szwrap16_add. apply wrap16_pb_add. Qed.

Lemma BR_st_blfc : forall m X i v a,
  BRm m X -> 0 <= i < 39 -> a = S + 2748 + 4 * i ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_fc X TB (arr_set (tree_fc X TB) i (wrap16 v))).
Proof.
  intros m X i v a HB Hi ->. change (S + 2748) with (S + toff TB).
  apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | cbn; lia].
Qed.

Lemma BR_st_dl_at : forall m X t i v a,
  BRm m X -> 0 <= i < tsize t -> a = S + toff t + 4 * i + 2 ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_dl X t (arr_set (tree_dl X t) i (wrap16 v))).
Proof. intros m X t i v a HB Hi ->. apply (BR_st_dl _ _ _ _ F mem0 S p PBL HLb HFS); assumption. Qed.

Definition sc_upd (X : deflate_state) (mn c pl k1 : Z) : deflate_state :=
  if k1 <? mn then set_Freq X TB c (Freq X TB c + k1)
  else if negb (c =? 0) then
    set_Freq (if negb (c =? pl) then set_Freq X TB c (Freq X TB c + 1) else X) TB REP_3_6
             (Freq (if negb (c =? pl) then set_Freq X TB c (Freq X TB c + 1) else X) TB REP_3_6 + 1)
  else if k1 <=? 10 then set_Freq X TB REPZ_3_10 (Freq X TB REPZ_3_10 + 1)
  else set_Freq X TB REPZ_11_138 (Freq X TB REPZ_11_138 + 1).

Lemma scan_loop_S' : forall f X t mc n prevlen nextlen count mx mn,
  scan_tree_loop (Datatypes.S f) X t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len X t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        scan_tree_loop f X t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        scan_tree_loop f (sc_upd X mn curlen prevlen count') t mc (n + 1) curlen nextlen' 0 mx' mn'
    else X.
Proof. intros. reflexivity. Qed.

Lemma set_Freq_TB_Len : forall X c v t i, Len (set_Freq X TB c v) t i = Len X t i.
Proof. intros X c v [| |] i; reflexivity. Qed.
Lemma set_Freq_TB_tree_dl : forall X c v t, tree_dl (set_Freq X TB c v) t = tree_dl X t.
Proof. intros X c v [| |]; reflexivity. Qed.
Lemma set_Freq_TB_blfc : forall X c v, ds_bl_tree_fc (set_Freq X TB c v) = arr_set (ds_bl_tree_fc X) c (wrap16 v).
Proof. intros; reflexivity. Qed.
Lemma blfc_typed_set : forall (b : arr) c v,
  (forall i, 0 <= i < 39 -> 0 <= arr_get b i < 65536) -> arr_len b = 39 ->
  forall i, 0 <= i < 39 -> 0 <= arr_get (arr_set b c (wrap16 v)) i < 65536.
Proof.
  intros b c v Hb Hl i Hi. rewrite arr_get_set. destruct (_ && _); [|apply Hb; exact Hi].
  rewrite wrap16_mod'. pose proof (Z.mod_pos_bound v (2 ^ 16) ltac:(lia)). change (2 ^ 16) with 65536 in *. lia.
Qed.

Lemma sc_upd_Len : forall X mn c pl k1 t i, Len (sc_upd X mn c pl k1) t i = Len X t i.
Proof.
  intros. unfold sc_upd. destruct (k1 <? mn); [apply set_Freq_TB_Len|].
  destruct (negb (c =? 0)); [destruct (negb (c =? pl)); rewrite !set_Freq_TB_Len; reflexivity|].
  destruct (k1 <=? 10); apply set_Freq_TB_Len.
Qed.
Lemma sc_upd_tree_dl : forall X mn c pl k1 t, tree_dl (sc_upd X mn c pl k1) t = tree_dl X t.
Proof.
  intros. unfold sc_upd. destruct (k1 <? mn); [apply set_Freq_TB_tree_dl|].
  destruct (negb (c =? 0)); [destruct (negb (c =? pl)); rewrite !set_Freq_TB_tree_dl; reflexivity|].
  destruct (k1 <=? 10); apply set_Freq_TB_tree_dl.
Qed.
Lemma sc_upd_typed : forall X mn c pl k1,
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X) i < 65536) -> arr_len (ds_bl_tree_fc X) = 39 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc (sc_upd X mn c pl k1)) i < 65536)
  /\ arr_len (ds_bl_tree_fc (sc_upd X mn c pl k1)) = 39.
Proof.
  intros X mn c pl k1 Hb Hl. unfold sc_upd.
  destruct (k1 <? mn); [rewrite set_Freq_TB_blfc, arr_len_set; split; [apply blfc_typed_set; assumption | exact Hl]|].
  destruct (negb (c =? 0)).
  - destruct (negb (c =? pl)); rewrite !set_Freq_TB_blfc, !arr_len_set; split; try exact Hl.
    + apply blfc_typed_set; [apply blfc_typed_set; assumption | rewrite arr_len_set; exact Hl].
    + apply blfc_typed_set; assumption.
  - destruct (k1 <=? 10); rewrite set_Freq_TB_blfc, arr_len_set; split; try exact Hl; apply blfc_typed_set; assumption.
Qed.


Definition VBS : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 65536); (37%nat, 2); (38%nat, 2 ^ 32);
   (39%nat, 2 ^ 64); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 600); (43%nat, 19); (44%nat, 2 ^ 64);
   (45%nat, 600); (46%nat, 16); (47%nat, 65536); (48%nat, 200); (49%nat, 65536); (50%nat, 200); (51%nat, 10)].

Definition sC : cfg := CFG FBv [] [EVar 1%nat] [0x1b154; 0x1b168; 0x1b188; 0x1b1cc; 0x1b20c] [].

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
  KR R /\ getr R 12 = zw (S + 2748) /\ getr R 14 = zw 4 /\ getr R 16 = zw 9 /\ getr R 15 = zw (S + 218 + 4 + 4 * mc).
Definition SKP : list (Z * expr) :=
  KPN ++ [(12, EAdd (EVar 32) (ELit 2748)); (14, ELit 4); (16, ELit 9); (15, EAdd (EAdd (EVar 32) (ELit (218 + 4))) (EShl (EVar 41) 2))].
Local Ltac skd H := destruct H as (HKR & Kbl & Kfour & Knine & Kend).
Local Ltac skregs HR Hfr := unfold SK; split; [kregs HR Hfr | regs_of HR Hfr].

Definition SH (mc : Z) (R : bvmap 5 word) (n pl c k mx mn : Z) : Prop :=
  SK mc R /\ getr R 13 = zw (S + 218 + 4 * n) /\ getr R 11 = zw c /\ getr R 7 = zw k
  /\ getr R 5 = zw mx /\ getr R 6 = zw mn /\ getr R 29 = zw pl.
Local Ltac shd H := destruct H as (HSK & Pptr & P11 & Pk & Pmx & Pmn & Ppl).
Definition SHP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(13, EAdd (EAdd (EVar 32) (ELit 218)) (EShl (EVar 45) 2)); (11, EVar 46); (7, EVar 48); (5, EVar 50); (6, EVar 51)] ++ plp.

Definition SD (mc : Z) (R : bvmap 5 word) (n pl c nl k mx mn : Z) : Prop :=
  SK mc R /\ getr R 13 = zw (S + 218 + 4 * n) /\ getr R 17 = zw c /\ getr R 11 = zw nl
  /\ getr R 28 = zw (k + 1) /\ getr R 7 = zw k /\ getr R 5 = zw mx /\ getr R 6 = zw mn /\ getr R 29 = zw pl.
Local Ltac sdd H := destruct H as (HSK & Pptr & Pc & P11 & Pk1 & Pk & Pmx & Pmn & Ppl).
Definition SDP (plp : list (Z * expr)) : list (Z * expr) :=
  SKP ++ [(13, EAdd (EAdd (EVar 32) (ELit 218)) (EShl (EVar 45) 2)); (17, EVar 46); (11, EVar 47);
          (28, EAdd (EVar 48) (ELit 1)); (7, EVar 48); (5, EVar 50); (6, EVar 51)] ++ plp.

Definition SG (mc : Z) (R : bvmap 5 word) (n c nl : Z) : Prop :=
  SK mc R /\ getr R 13 = zw (S + 218 + 4 * n) /\ getr R 17 = zw c /\ getr R 11 = zw nl /\ getr R 28 = zw 0.
Local Ltac sgd H := destruct H as (HSK & Pptr & Pc & P11 & Pk1).
Definition SGP : list (Z * expr) :=
  SKP ++ [(13, EAdd (EAdd (EVar 32) (ELit 218)) (EShl (EVar 45) 2)); (17, EVar 46); (11, EVar 47); (28, ELit 0)].

Definition STGT (nl : Z) : word := if nl =? 0 then (0x1b1cc : word) else (0x1b188 : word).
Definition SNEXT (mc n : Z) : word := if n + 1 =? mc + 1 then (0x1b20c : word) else (0x1b154 : word).

Definition SCL : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29]%bv.


Lemma s1h_emit : forall regs m1 m X mc n pl c k mx mn,
  FI m1 m X -> SH mc regs n pl c k mx mn -> 0 <= mc /\ mc + 1 < 573 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X TL) i < 65536) ->
  (mx <= k + 1 \/ c <> Len X TL (n + 1)) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b154 : word) m s6_rom) (mkst R (0x1b168 : word) m s6_rom)
    /\ SD mc R n pl c (Len X TL (n + 1)) k mx mn
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n pl c k mx mn HF HSH Hmc Hn Hc Hk Hmx Hmn Hdl Hcase.
  open_fi HF. shd HSH. skd HSK. kd HKR.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl X TL) (n + 1) = Len X TL (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  cbn [tree_dl] in Enl, Vnl.
  destruct (Z_le_gt_dec mx (k + 1)) as [C1|C1].
  - runs 30%nat [true] [RVal (EApp1 1 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SD. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 30%nat [false; false] [RVal (EApp1 1 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SD. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma s1h_cont : forall regs m1 m X mc n pl c k mx mn,
  FI m1 m X -> SH mc regs n pl c k mx mn -> 0 <= mc /\ mc + 1 < 573 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 <= k < mx -> mx <= 138 -> 0 <= mn < 10 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X TL) i < 65536) ->
  k + 1 < mx -> c = Len X TL (n + 1) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b154 : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
    /\ SH mc R (n + 1) pl c (k + 1) mx mn
    /\ (forall r : reg, reg_in r SCL = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mc n pl c k mx mn HF HSH Hmc Hn Hc Hk Hmx Hmn Hdl C1 Ec.
  open_fi HF. shd HSH. skd HSK. kd HKR.
  pose proof (Hdl (n + 1) ltac:(lia)) as Vnl.
  assert (Enl : pb (tree_dl X TL) (n + 1) = Len X TL (n + 1)) by (unfold Len; apply pb_small; exact Vnl).
  cbn [tree_dl] in Enl, Vnl. unfold SNEXT.
  destruct (Z.eqb_spec (n + 1) (mc + 1)) as [En|En].
  - runs 30%nat [false; true; true] [RVal (EApp1 1 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
  - runs 30%nat [false; true; false] [RVal (EApp1 1 (EAdd (EVar 45) (ELit 1)))] (SHP [])
        [S; PB; 0; 0; 0; last; 0; 0; SP; mc; 0; 0; 0; n; c; 0; k; 0; mx; mn] X.
    exists R. split; [exact Hms|]. split; [| fr_weak Hfr]. unfold SH. split; [skregs HR Hfr|]. regs_of HR Hfr.
Qed.


Lemma s1tnz : forall regs m1 m X mc n c nl,
  FI m1 m X -> SG mc regs n c nl -> 0 <= mc /\ mc + 1 < 573 -> 0 <= n <= mc -> 0 <= c <= 15 -> 0 < nl < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b188 : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
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

Lemma s1tz : forall regs m1 m X mc n c,
  FI m1 m X -> SG mc regs n c 0 -> 0 <= mc /\ mc + 1 < 573 -> 0 <= n <= mc -> 0 <= c <= 15 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b1cc : word) m s6_rom) (mkst R (SNEXT mc n) m s6_rom)
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
End Walk.
End FXG.
