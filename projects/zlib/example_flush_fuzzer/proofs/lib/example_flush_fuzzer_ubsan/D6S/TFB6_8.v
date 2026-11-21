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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7.
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
Local Abbreviation call_bt := (TFB6_1.call_bt F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation s1phase := (TFB6_6.s1phase F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation s2phase := (TFB6_7.s2phase F mem0 mem S p PBL ds ra sp buf bufp len last HH).


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

Definition gC : cfg := CFG FBv [] [EVar 50%nat] [0x1b94c] [].

Definition KR3 (R : bvmap 5 word) : Prop := getr R 18 = zw len /\ getr R 19 = zw bufp /\ getr R 20 = zw (S + 2047).

Lemma g_blk : forall (pc : word) (off : Z) (ra' : Z) regs m1 m X,
  (pc = (0x1b0b8%bv : word) /\ off = 857 /\ ra' = 0x1b0c4) \/ (pc = (0x1b0c4%bv : word) /\ off = 881 /\ ra' = 0x1b0d0)
  \/ (pc = (0x1b340%bv : word) /\ off = 905 /\ ra' = 0x1b34c) ->
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 ->
  exists R,
    msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x1b94c : word) m s6_rom)
    /\ KR R /\ KR3 R /\ getr R 10 = zw S /\ getr R 11 = zw (S + 2047 + off) /\ getr R 1 = zw ra'
    /\ (forall r : reg, reg_in r [1; 10; 11]%bv = false -> getr R r = getr regs r).
Proof.
  intros pc off ra' regs m1 m X Hcase HF HK (P18 & P19 & P20) Hbufp. open_fi HF. kd HK.
  destruct Hcase as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]];
    (run gC 10%nat NoDirs NoReads (KPN ++ [(18, EVar 38); (19, EVar 39); (20, EAdd (EVar 32) (ELit 2047))])
         [S; PB; 0; 0; 0; last; len; bufp; SP] X;
     exists R; split; [exact Hms|]; split; [kregs HR Hfr|]; split; [unfold KR3; regs_of HR Hfr|];
     split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr]).
Qed.

Local Ltac frw a Hr := rewrite (a _ ) by (eapply reg_in_sub; [|exact Hr]; reflexivity).

Lemma trees_phase : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 ->
  let X1 := build_tree X TL in
  let X2 := build_tree X1 TD in
  let mcl := ds_l_max_code X2 in
  let X3 := scan_tree X2 TL mcl in
  let mcd := ds_d_max_code X3 in
  let X4 := scan_tree X3 TD mcd in
  let X5 := build_tree X4 TB in
  bt_safe X TL -> bt_safe X1 TD ->
  (0 <= mcl /\ mcl + 1 < 573) -> (forall i, 0 <= i <= mcl -> 0 <= Len X2 TL i <= 15) ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536) ->
  (0 <= mcd /\ mcd + 1 < 61) -> (forall i, 0 <= i <= mcd -> 0 <= Len X3 TD i <= 15) ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536) ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536) ->
  bt_safe X4 TB ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b0b8 : word) m s6_rom) (mkst R (0x1b34c : word) m' s6_rom)
    /\ FI m1 m' X5 /\ KR R /\ KR3 R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK HK3 Hbufp. cbv zeta. intros S1 S2 Hmcl Hl15 Hdl1 Hty1 Hmcd Hd15 Hdl2 Hty2 S3.
  destruct (g_blk (0x1b0b8%bv : word) 857 0x1b0c4 regs m1 m X ltac:(left; repeat split; reflexivity) HF HK HK3 Hbufp)
    as (R0 & Hms0 & HK0 & HK30 & A10 & A11 & A1 & Hfr0).
  destruct (call_bt R0 m1 m X TL (0x1b0c4%bv : word) HF S1 ltac:(apply ret_ok_even; reflexivity) A10
              ltac:(rewrite A11; f_equal; cbn; lia) (proj2 (proj2 (proj2 (proj2 HK0)))) ltac:(rewrite A1; apply bv_eq; reflexivity))
    as (R1 & ma & Hms1 & HF1 & _ & Q2 & Hfr1).
  assert (HK1 : KR R1 /\ KR3 R1).
  { destruct HK0 as (K8 & K9 & K21 & K22 & K2). destruct HK30 as (K18 & K19 & K20). unfold KR, KR3.
    rewrite !(Hfr1 8%bv eq_refl), !(Hfr1 9%bv eq_refl), !(Hfr1 21%bv eq_refl), !(Hfr1 22%bv eq_refl), Q2,
            !(Hfr1 18%bv eq_refl), !(Hfr1 19%bv eq_refl), !(Hfr1 20%bv eq_refl). repeat split; assumption. }
  destruct HK1 as [HK1 HK31].
  destruct (g_blk (0x1b0c4%bv : word) 881 0x1b0d0 R1 m1 ma _ ltac:(right; left; repeat split; reflexivity) HF1 HK1 HK31 Hbufp)
    as (R2 & Hms2 & HK2 & HK32 & B10 & B11 & B1 & Hfr2).
  destruct (call_bt R2 m1 ma _ TD (0x1b0d0%bv : word) HF1 S2 ltac:(apply ret_ok_even; reflexivity) B10
              ltac:(rewrite B11; f_equal; cbn; lia) (proj2 (proj2 (proj2 (proj2 HK2)))) ltac:(rewrite B1; apply bv_eq; reflexivity))
    as (R3 & mb & Hms3 & HF3 & _ & Q2' & Hfr3).
  assert (HK3' : KR R3 /\ KR3 R3).
  { destruct HK2 as (K8 & K9 & K21 & K22 & K2). destruct HK32 as (K18 & K19 & K20). unfold KR, KR3.
    rewrite !(Hfr3 8%bv eq_refl), !(Hfr3 9%bv eq_refl), !(Hfr3 21%bv eq_refl), !(Hfr3 22%bv eq_refl), Q2',
            !(Hfr3 18%bv eq_refl), !(Hfr3 19%bv eq_refl), !(Hfr3 20%bv eq_refl). repeat split; assumption. }
  destruct HK3' as [HKa HK3a].
  destruct (s1phase R3 m1 mb _ HF3 HKa (proj2 (proj2 HK3a)) Hmcl Hdl1 Hl15 Hty1) as (R4 & mc4 & Hms4 & HF4 & HK4 & Q10 & Hfr4).
  assert (HK34 : KR3 R4).
  { destruct HK3a as (K18 & K19 & K20). unfold KR3. rewrite !(Hfr4 18%bv eq_refl), !(Hfr4 19%bv eq_refl), !(Hfr4 20%bv eq_refl). repeat split; assumption. }
  destruct (s2phase R4 m1 mc4 _ HF4 HK4 (proj2 (proj2 HK34)) Q10 Hmcd Hdl2 Hd15 Hty2) as (R5 & md & Hms5 & HF5 & HK5 & _ & Hfr5).
  assert (HK35 : KR3 R5).
  { destruct HK34 as (K18 & K19 & K20). unfold KR3. rewrite !(Hfr5 18%bv eq_refl), !(Hfr5 19%bv eq_refl), !(Hfr5 20%bv eq_refl). repeat split; assumption. }
  destruct (g_blk (0x1b340%bv : word) 905 0x1b34c R5 m1 md _ ltac:(right; right; repeat split; reflexivity) HF5 HK5 HK35 Hbufp)
    as (R6' & Hms6 & HK6 & HK36 & C10 & C11 & C1 & Hfr6).
  destruct (call_bt R6' m1 md _ TB (0x1b34c%bv : word) HF5 S3 ltac:(apply ret_ok_even; reflexivity) C10
              ltac:(rewrite C11; f_equal; cbn; lia) (proj2 (proj2 (proj2 (proj2 HK6)))) ltac:(rewrite C1; apply bv_eq; reflexivity))
    as (R7 & me & Hms7 & HF7 & _ & Q2'' & Hfr7).
  exists R7, me. split.
  { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5|].
    eapply msteps_trans; [exact Hms6 | exact Hms7]. }
  split; [exact HF7|].
  split.
  { destruct HK6 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr7 8%bv eq_refl), !(Hfr7 9%bv eq_refl), !(Hfr7 21%bv eq_refl), !(Hfr7 22%bv eq_refl), Q2''. repeat split; assumption. }
  split.
  { destruct HK36 as (K18 & K19 & K20). unfold KR3. rewrite !(Hfr7 18%bv eq_refl), !(Hfr7 19%bv eq_refl), !(Hfr7 20%bv eq_refl). repeat split; assumption. }
  intros r Hr.
  rewrite (Hfr7 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr6 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr5 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr1 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
End Walk.
End FXG.
