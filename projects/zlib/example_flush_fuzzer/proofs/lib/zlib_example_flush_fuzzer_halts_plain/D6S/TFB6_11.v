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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7 TFB6_8 TFB6_9 TFB6_10.
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
Local Abbreviation KR3 := (TFB6_8.KR3 S bufp len).
Local Abbreviation ZR := (TFB6_10.ZR S sp bufp len last).
Local Abbreviation call_tsb := (TFB6_1.call_tsb F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation call_ib := (TFB6_1.call_ib F mem0 mem S p PBL ds ra sp buf bufp len last HH).
Local Abbreviation call_cb := (TFB6_1.call_cb F mem0 mem S p PBL ds ra sp buf bufp len last HH).


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

Definition aC : cfg := CFG FBv [] [EVar 50%nat] [0x1abbc; 0x1aaac; 0x1c2a8; 0x1b870; 0x1b8e4] [].

Definition LPC : word := if last =? 0 then (0x1b8e4 : word) else (0x1b870 : word).

Lemma cells_prefix : forall m P st w n n' f, cells s6_segs m P st w n f -> n' <= n -> cells s6_segs m P st w n' f.
Proof. intros m P st w n n' f H Hn i Hi. apply H. lia. Qed.

Local Ltac frc a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
  rewrite (a r) by (eapply reg_in_sub; [|exact Hr]; reflexivity); apply b; eapply reg_in_sub; [|exact Hr]; reflexivity.


Lemma stb1_blk : forall regs m1 m X mb slb olb0,
  FI m1 m X -> ZR regs mb slb olb0 -> 0 <= bufp < 2 ^ 64 -> 0 <= mb <= 18 -> 0 <= slb < 2 ^ 61 -> 0 <= olb0 < 2 ^ 61 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b494 : word) m s6_rom) (mkst R (0x1abbc : word) m s6_rom)
    /\ KR R /\ getr R 10 = zw S /\ getr R 11 = zw bufp /\ getr R 12 = zw len /\ getr R 13 = zw last /\ getr R 1 = zw 0x1b4a8
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mb slb olb0 HF (HK & (P18 & P19 & P20) & P10 & P11 & P13) Hbufp Hmb Hslb Holb. open_fi HF. kd HK.
  run aC 12%nat NoDirs NoReads
      (KPN ++ [(18, EVar 38); (19, EVar 39); (20, EAdd (EVar 32) (ELit 2047)); (10, EVar 43); (11, EVar 45); (13, EVar 46)])
      [S; PB; 0; 0; 0; last; len; bufp; SP; 0; 0; mb; 0; slb; olb0] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. regs_of HR Hfr.
Qed.

Lemma ibg_blk : forall (pc : word) (ra' : Z) regs m1 m X,
  (pc = (0x1b4a8%bv : word) /\ ra' = 0x1b4b0) \/ (pc = (0x1b5d8%bv : word) /\ ra' = 0x1b5e0) \/ (pc = (0x1b864%bv : word) /\ ra' = 0x1b86c) ->
  FI m1 m X -> KR regs ->
  exists R,
    msteps s6_segs (mkst regs pc m s6_rom) (mkst R (0x1aaac : word) m s6_rom)
    /\ KR R /\ getr R 10 = zw S /\ getr R 1 = zw ra'
    /\ (forall r : reg, reg_in r [1; 10]%bv = false -> getr R r = getr regs r).
Proof.
  intros pc ra' regs m1 m X Hcase HF HK. open_fi HF. kd HK.
  destruct Hcase as [(-> & ->)|[(-> & ->)|(-> & ->)]];
    (run aC 8%nat NoDirs NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X;
     exists R; split; [exact Hms|]; split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr]).
Qed.

Lemma lt_blk : forall (pc : word) regs m1 m X,
  (pc = (0x1b4b0%bv : word) \/ pc = (0x1b5e0%bv : word) \/ pc = (0x1b86c%bv : word)) ->
  FI m1 m X -> KR regs ->
  exists R,
    msteps s6_segs (mkst regs pc m s6_rom) (mkst R LPC m s6_rom)
    /\ KR R /\ (forall r : reg, reg_in r ([] : list reg) = false -> getr R r = getr regs r).
Proof.
  intros pc regs m1 m X Hcase HF HK. open_fi HF. kd HK. unfold LPC.
  destruct (Z.eqb_spec last 0) as [El|El]; destruct Hcase as [->|[->| ->]].
  - run aC 8%nat [false] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
  - run aC 8%nat [false] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
  - run aC 8%nat [true] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
  - run aC 8%nat [true] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
  - run aC 8%nat [true] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
  - run aC 8%nat [false] NoReads KPN [S; PB; 0; 0; 0; last; 0; 0; SP] X. exists R; split; [exact Hms|]; split; [kregs HR Hfr | fr_weak Hfr].
Qed.

Lemma stored_arm : forall regs m1 m X mb slb olb0,
  FI m1 m X -> ZR regs mb slb olb0 -> 0 <= bufp < 2 ^ 64 -> 0 <= mb <= 18 -> 0 <= slb < 2 ^ 61 -> 0 <= olb0 < 2 ^ 61 ->
  BINV PBL X -> ds_pending (tr_stored_block X buf len last) <= PBL -> ds_window X = ds_window ds -> (len <> 0 -> buf <> None) ->
  let X7 := tr_stored_block X buf len last in
  exists R m',
    msteps s6_segs (mkst regs (0x1b494 : word) m s6_rom) (mkst R LPC m' s6_rom)
    /\ FI m1 m' (init_block X7) /\ KR R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mb slb olb0 HF HZ Hbufp Hmb Hslb Holb HBI Hroom EW Hb. cbv zeta.
  destruct (stb1_blk regs m1 m X mb slb olb0 HF HZ Hbufp Hmb Hslb Holb) as (R0 & Hms0 & HK0 & A10 & A11 & A12 & A13 & A1 & Hfr0).
  destruct (call_tsb R0 m1 m X (0x1b4a8%bv : word) HF HBI Hroom EW Hb ltac:(apply ret_ok_even; reflexivity)
              A10 A11 A12 A13 (proj2 (proj2 (proj2 (proj2 HK0)))) ltac:(rewrite A1; apply bv_eq; reflexivity))
    as (R1 & ma & Hms1 & HF1 & _ & Hfr1).
  assert (HK1 : KR R1).
  { destruct HK0 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr1 8%bv eq_refl), !(Hfr1 9%bv eq_refl), !(Hfr1 21%bv eq_refl), !(Hfr1 22%bv eq_refl), !(Hfr1 2%bv eq_refl). repeat split; assumption. }
  destruct (ibg_blk (0x1b4a8%bv : word) 0x1b4b0 R1 m1 ma _ ltac:(left; split; reflexivity) HF1 HK1) as (R2 & Hms2 & HK2 & B10 & B1 & Hfr2).
  destruct (call_ib R2 m1 ma _ (0x1b4b0%bv : word) HF1 ltac:(apply ret_ok_even; reflexivity) B10 ltac:(rewrite B1; apply bv_eq; reflexivity))
    as (R3 & mb' & Hms3 & HF3 & _ & Hfr3).
  assert (HK3 : KR R3).
  { destruct HK2 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr3 8%bv eq_refl), !(Hfr3 9%bv eq_refl), !(Hfr3 21%bv eq_refl), !(Hfr3 22%bv eq_refl), !(Hfr3 2%bv eq_refl). repeat split; assumption. }
  destruct (lt_blk (0x1b4b0%bv : word) R3 m1 mb' _ ltac:(left; reflexivity) HF3 HK3) as (R4 & Hms4 & HK4 & Hfr4).
  exists R4, mb'. split.
  { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3 | exact Hms4]. }
  split; [exact HF3|]. split; [exact HK4|].
  intros r Hr. rewrite (Hfr4 r eq_refl).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr1 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Lemma sta1_blk : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 12 = zw (ds_bi_valid X) -> BINV PBL X -> sb_room PBL X 3 ->
  let X1 := send_bits X (Z.shiftl STATIC_TREES 1 + last) 3 in
  exists R m',
    msteps s6_segs (mkst regs (0x1b4c0 : word) m s6_rom) (mkst R (0x1c2a8 : word) m' s6_rom)
    /\ FI m1 m' X1
    /\ (KR R /\ getr R 10 = zw S /\ getr R 11 = zw 0x11de0 /\ getr R 12 = zw 0x12260 /\ getr R 1 = zw 0x1b5d8
        /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X HF HK P12 HBI Hroom. cbv zeta. change (Z.shiftl STATIC_TREES 1 + last) with (2 + last).
  open_fi HF. kd HK. destruct HBI as (Hbv & Hbb & Hpd).
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - 3) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - run aC 60%nat [false] [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] (KPN ++ [(12, EVar 35)])
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr]).
  - run aC 60%nat [true] [RVal (EVar 36)] (KPN ++ [(12, EVar 35)])
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr|]; split; [reg1 HR Hfr | fr_weak Hfr]).
Qed.

Lemma static_arm : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 12 = zw (ds_bi_valid X) -> stat_ok PBL X last ->
  let X1 := send_bits X (Z.shiftl STATIC_TREES 1 + last) 3 in
  let X7 := compress_block X1 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl in
  exists R m',
    msteps s6_segs (mkst regs (0x1b4c0 : word) m s6_rom) (mkst R LPC m' s6_rom)
    /\ FI m1 m' (init_block X7) /\ KR R
    /\ (forall r : reg, reg_in r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P12 (HBI & Hroom & Hcb & Hsn & HLB). cbv zeta.
  destruct (sta1_blk regs m1 m X HF HK P12 HBI Hroom) as (R0 & ma & Hms0 & HF0 & HK0 & A10 & A11 & A12 & A1 & Hfr0).
  set (X1 := send_bits X _ 3) in *.
  assert (HT : forall m'' s', BR6 (Fmin S PB PBL SP 48) ma S p PBL m'' s' ->
     (forall t, tree_fc s' t = tree_fc X1 t) -> (forall t, tree_dl s' t = tree_dl X1 t) -> trees_rod_clear6 m'' ->
     cells s6_segs m'' 0x11de0 4 2 286 (arr_get static_ltree_fc) /\ cells s6_segs m'' (0x11de0 + 2) 4 2 286 (arr_get static_ltree_dl)
     /\ cells s6_segs m'' 0x12260 4 2 30 (arr_get static_dtree_fc) /\ cells s6_segs m'' (0x12260 + 2) 4 2 30 (arr_get static_dtree_dl)).
  { intros m'' s' _ _ _ HRC''.
    destruct (static_ltree_cells R6 _ _ trod_ok6 HRC'') as [L1 L2]. destruct (static_dtree_cells R6 _ _ trod_ok6 HRC'') as [D1 D2].
    cbn [tr_static_ltree tr_static_dtree R6] in L1, L2, D1, D2.
    split; [eapply cells_prefix; [exact L1 | lia]|]. split; [eapply cells_prefix; [exact L2 | lia]|]. split; [exact D1 | exact D2]. }
  destruct (call_cb R0 m1 ma X1 0x11de0 0x12260 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl (0x1b5d8%bv : word)
              HF0 ltac:(apply ret_ok_even; reflexivity) Hcb HT ltac:(lia) ltac:(lia) Hsn HLB HPBL A10 A11 A12
              (proj2 (proj2 (proj2 (proj2 HK0)))) ltac:(rewrite A1; apply bv_eq; reflexivity))
    as (R1 & mb' & Hms1 & HF1 & _ & Q2 & Hfr1).
  assert (HK1 : KR R1).
  { destruct HK0 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr1 8%bv eq_refl), !(Hfr1 9%bv eq_refl), !(Hfr1 21%bv eq_refl), !(Hfr1 22%bv eq_refl), Q2. repeat split; assumption. }
  destruct (ibg_blk (0x1b5d8%bv : word) 0x1b5e0 R1 m1 mb' _ ltac:(right; left; split; reflexivity) HF1 HK1) as (R2 & Hms2 & HK2 & B10 & B1 & Hfr2).
  destruct (call_ib R2 m1 mb' _ (0x1b5e0%bv : word) HF1 ltac:(apply ret_ok_even; reflexivity) B10 ltac:(rewrite B1; apply bv_eq; reflexivity))
    as (R3 & mc' & Hms3 & HF3 & _ & Hfr3).
  assert (HK3 : KR R3).
  { destruct HK2 as (K8 & K9 & K21 & K22 & K2). unfold KR.
    rewrite !(Hfr3 8%bv eq_refl), !(Hfr3 9%bv eq_refl), !(Hfr3 21%bv eq_refl), !(Hfr3 22%bv eq_refl), !(Hfr3 2%bv eq_refl). repeat split; assumption. }
  destruct (lt_blk (0x1b5e0%bv : word) R3 m1 mc' _ ltac:(right; left; reflexivity) HF3 HK3) as (R4 & Hms4 & HK4 & Hfr4).
  exists R4, mc'. split.
  { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
    eapply msteps_trans; [exact Hms3 | exact Hms4]. }
  split; [exact HF3|]. split; [exact HK4|].
  intros r Hr. rewrite (Hfr4 r eq_refl).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr1 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
End Walk.
End FXG.
