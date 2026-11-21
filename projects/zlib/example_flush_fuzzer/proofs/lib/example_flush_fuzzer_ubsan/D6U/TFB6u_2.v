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
  CompressBlk6u_1 CompressBlk6u_4 BuildTree6u_11 TrSmall6u TrStored6u ScanTree6u SendTree6u_1 SendTree6u_5 TFB6u_1.
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


Definition FRAME (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6u_segs m (SP + 56) 8 (bv_unsigned ra)
  /\ cell s6u_segs m (SP + 48) 8 (bv_unsigned (getr regs0 8)) /\ cell s6u_segs m (SP + 40) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6u_segs m (SP + 32) 8 (bv_unsigned (getr regs0 18)) /\ cell s6u_segs m (SP + 24) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6u_segs m (SP + 16) 8 (bv_unsigned (getr regs0 20)) /\ cell s6u_segs m (SP + 8) 8 (bv_unsigned (getr regs0 21))
  /\ cell s6u_segs m SP 8 (bv_unsigned (getr regs0 22)).

Lemma FRAME_keep : forall m m' regs0,
  (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v) ->
  FRAME m regs0 -> FRAME m' regs0.
Proof.
  intros m m' regs0 HC (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold FRAME.
  repeat split; (apply HC; [assumption | lia | cbn; lia]).
Qed.

Lemma FRAME_fi : forall m1 m X regs0, FI m1 m X -> FRAME m1 regs0 -> FRAME m regs0.
Proof.
  intros m1 m X regs0 (_ & _ & HAG & _ & _) HF.
  pose proof Hcf as (Hsp0 & _ & _ & HfS & HfP). unfold TFB_FRAME6u, dsl_SIZE in *.
  pose proof HLb as ((HS1 & HS2) & (HP1 & HP2) & _).
  apply (FRAME_keep m1 m regs0); [|exact HF].
  intros a w v Hc Ha1 Ha2. apply (cell_agree_out s6u_segs GFB m1 m a w v HAG); [| lia | lia | exact Hc].
  unfold TFB6u_1.GFB. intros x Hx [Hin|[Hin|[Hin|[]]]]; cbn in Hin; unfold dsl_SIZE in Hin; lia.
Qed.

Definition pC : cfg := CFG FBv [] [EVar 50%nat] [0x1c048; 0x1c0b0; 0x1ca0c; 0x1bc44] [].


Lemma pro_blk : forall regs,
  0 <= ds_level ds < 2 ^ 31 ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw sp -> getr regs 1 = ra -> 0 <= bufp < 2 ^ 64 ->
  exists R m1,
    msteps s6u_segs (mkst regs (0x1bff0 : word) mem s6u_rom)
           (mkst R (if 0 <? ds_level ds then (0x1c048 : word) else (0x1c0b0 : word)) m1 s6u_rom)
    /\ FI m1 m1 ds /\ FRAME m1 regs
    /\ (forall a w v, cell s6u_segs mem a w v -> 0 <= a -> (a + Z.of_nat w <= SP \/ (sp <= a /\ a + Z.of_nat w <= 2 ^ 64)) -> cell s6u_segs m1 a w v)
    /\ KR R /\ getr R 18 = zw len /\ getr R 19 = zw bufp
    /\ (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs Hlev P10 P11 P12 P13 P2 P1 Hbufp.
  pose proof HBR0 as HB. pose proof HPBL as HPBL'. pose proof HLb as HL'. destruct HL' as (HS' & HPB' & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  pose proof (dsl_level _ _ _ _ _ _ _ _ Hsc) as C196. clear Hsc.
  pose proof Hcf as (Hsp0 & HFf & Hmf & HfS & HfP). unfold TFB_FRAME6u, dsl_SIZE in Hsp0, HFf, Hmf, HfS, HfP.
  pose proof Hmf as MF. unfold mapped in MF.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19. pose proof (u64_range (getr regs 20)) as U20.
  pose proof (u64_range (getr regs 21)) as U21. pose proof (u64_range (getr regs 22)) as U22.
  open_ubt HUB.
  assert (P2' : getr regs 2 = zw (SP + 64)) by (rewrite P2; f_equal; lia).
  assert (BRfr : forall M s0, BRm M s0 -> forall b v, SP <= b -> b + 8 <= sp -> BRm (wbytes M (zw b) (Z_to_le_bytes 8 v)) s0).
  { intros M s0 HM b v Hb1 Hb2.
    apply (BR_st_other _ _ _ _ F mem0 S p PBL HLb); [exact HM | lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia
      | rewrite length_Z_to_le_bytes; eapply sub_franges_mono; [exact HFf | cbn; lia | cbn; lia] ]. }
  assert (FIN : forall R M (pc : word),
    msteps s6u_segs (mkst regs (0x1bff0 : word) mem s6u_rom) (mkst R pc M s6u_rom) ->
    M = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
          (zw (SP + 56)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 1))))
          (zw (SP + 48)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 8))))
          (zw (SP + 40)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 9))))
          (zw (SP + 32)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 18))))
          (zw (SP + 24)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 19))))
          (zw (SP + 16)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 20))))
          (zw (SP + 8)) (Z_to_le_bytes 8 (bv_unsigned (getr regs 21))))
          (zw SP) (Z_to_le_bytes 8 (bv_unsigned (getr regs 22))) ->
    KR R /\ getr R 18 = zw len /\ getr R 19 = zw bufp ->
    (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21]%bv = false -> getr R r = getr regs r) ->
    exists R' m1,
      msteps s6u_segs (mkst regs (0x1bff0 : word) mem s6u_rom) (mkst R' pc m1 s6u_rom)
      /\ FI m1 m1 ds /\ FRAME m1 regs
      /\ (forall a w v, cell s6u_segs mem a w v -> 0 <= a -> (a + Z.of_nat w <= SP \/ (sp <= a /\ a + Z.of_nat w <= 2 ^ 64)) -> cell s6u_segs m1 a w v)
      /\ KR R' /\ getr R' 18 = zw len /\ getr R' 19 = zw bufp
      /\ (forall r : reg, reg_in r [2; 8; 9; 10; 11; 18; 19; 20; 21]%bv = false -> getr R' r = getr regs r)).
  { intros R M pc Hms -> HK Hfr. eexists R, _. split; [exact Hms|].
    split.
    { split; [repeat (apply BRfr; [|lia|lia]); exact HB|].
      split.
      { apply (trees_rod_clear_wr R6u _ _ HRC0).
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
    destruct HK as (HK1 & HK2 & HK3). split; [exact HK1|]. split; [exact HK2|]. split; [exact HK3 | exact Hfr]. }
  destruct (Z.ltb_spec 0 (ds_level ds)) as [CL|CL].
  - run pC 40%nat [false; false; false] [RVal (EVar 45)]
        [(10, EVar 32); (11, EVar 39); (12, EVar 38); (13, EVar 37); (2, EAdd (EVar 40) (ELit 64))]
        [S; PB; 0; 0; 0; last; len; bufp; SP; 0; 0; 0; 0; ds_level ds] ds.
    all: match goal with |- ?g => idtac "PROLEFT1" g end.
    apply (FIN R _ _ Hms); [reflexivity | | fr_weak Hfr]. split; [kregs HR Hfr | regs_of HR Hfr].
  - run pC 40%nat [false; false; true] [RVal (EVar 45)]
        [(10, EVar 32); (11, EVar 39); (12, EVar 38); (13, EVar 37); (2, EAdd (EVar 40) (ELit 64))]
        [S; PB; 0; 0; 0; last; len; bufp; SP; 0; 0; 0; 0; ds_level ds] ds.
    apply (FIN R _ _ Hms); [reflexivity | | fr_weak Hfr]. split; [kregs HR Hfr | regs_of HR Hfr].
  all: match goal with |- ?g => idtac "PROLEFT" g end.
Qed.


Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m1 m X,
  FI m1 m X -> FRAME m regs0 -> KRW regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x1ca0c : word) m s6u_rom) (mkst R ra m s6u_rom)
    /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 m X HF (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22) HK. open_fi HF. kdw HK.
  pose proof Hret as Hret'.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20.
  pose proof (u64_range (getr regs0 21)) as U21. pose proof (u64_range (getr regs0 22)) as U22.
  run pC 20%nat NoDirs
      [RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53); RVal (EVar 54); RVal (EVar 55); RVal (EVar 56); RVal (EVar 57)]
      KPW
      [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; 0; 0; 0; 0; 0;
       bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
       bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22)] X.
  exists R. split; [exact Hms|].
  split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|].
  split; [| fr_weak Hfr].
  intros r Hr. apply FillWin6uD.reg_in_true_In in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reg1 HR Hfr.
Qed.


Lemma wind_pre : forall regs (regs0 : bvmap 5 word) m1 m X,
  FI m1 m X -> FRAME m regs0 -> KRW regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c348 : word) m s6u_rom) (mkst R (0x1bc44 : word) m s6u_rom)
    /\ getr R 10 = zw S /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 m X HF (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22) HK. open_fi HF. kdw HK.
  pose proof Hret as Hret'.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20.
  pose proof (u64_range (getr regs0 21)) as U21. pose proof (u64_range (getr regs0 22)) as U22.
  run pC 20%nat NoDirs
      [RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53); RVal (EVar 54); RVal (EVar 55); RVal (EVar 56); RVal (EVar 57)]
      KPW
      [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; 0; 0; 0; 0; 0;
       bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
       bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22)] X.
  exists R. split; [exact Hms|].
  split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|].
  split; [| fr_weak Hfr].
  intros r Hr. apply FillWin6uD.reg_in_true_In in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reg1 HR Hfr.
Qed.

Definition Fbw : franges := [(S + 40, 8); (S + 5936, 2); (S + 5940, 4); (PB, PBL); (S + 5944, 4)].
(* 1.4: (S + 5944, 4) = bi_used, stored by bi_windup; kept last so BRH_bw's four positions are unchanged *)

Lemma Fbw_bu : sub_franges Fbw (S + 5944) 4.
Proof.
  unfold Fbw. apply sub_franges_later. apply sub_franges_later. apply sub_franges_later. apply sub_franges_later.
  apply sub_franges_here; lia.
Qed.

Lemma BRH_bw : BRH Fbw S p PBL.
Proof.
  pose proof HLb as (H1 & H2 & H3 & _ & _ & _ & _). unfold BRH, Fbw.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply sub_franges_here; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; lia|].
  split; [apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; lia|].
  apply sub_franges_later. apply sub_franges_later. apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma Fbw_GFB : forall x, in_franges Fbw x -> in_franges GFB x.
Proof.
  pose proof HLb as ((HS1 & HS2) & _). unfold Fbw, TFB6u_1.GFB, dsl_SIZE.
  intros x [Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]; cbn in Hx |- *; lia.
Qed.

Lemma Fbw_sub : forall x, in_franges Fbw x -> in_franges F x.
Proof.
  pose proof HLb as (_ & _ & _ & H40 & H36 & H44 & HP). unfold Fbw.
  intros x [Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]; cbn in Hx.
  - apply H40. lia.
  - apply H36. lia.
  - apply H44. lia.
  - apply HP. exact Hx.
  - apply HFS. unfold dsl_SIZE. lia.
Qed.

Lemma wind_blk : forall regs (regs0 : bvmap 5 word) m1 m X,
  FI m1 m X -> FRAME m regs0 -> KRW regs -> BINV PBL X -> ds_pending (bi_windup X) <= PBL ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1c348 : word) m s6u_rom) (mkst R ra m' s6u_rom)
    /\ FI m1 m' (bi_windup X)
    /\ getr R 2 = zw sp /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [8; 9; 18; 19; 20; 21; 22]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 m X HF HFR HK HBI Hroom.
  destruct (wind_pre regs regs0 m1 m X HF HFR HK) as (R1 & Hms1 & Q10 & Q2 & Q1 & Hsv & Hfr1).
  pose proof HF as (HB & HRC & HAG & MF & HGR).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & MP & _).
  pose proof (bi_windup_run6u_ok Fbw m m S p PBL X ra R1 BRH_bw Fbw_bu Hret (BR_self F Fbw mem0 S p PBL m X HB) HBI Hroom HUB Q10 Q1)
    as (R & m' & Hms & HB' & Hfr).
  unfold A6U_BI_WINDUP' in Hms. replace (zw 0x1bc44) with (0x1bc44%bv : word) in Hms by (apply bv_eq; reflexivity).
  destruct (BR_back F Fbw mem0 S p PBL m m' X _ HB HB' Fbw_sub) as [HB2 Hag].
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & MS' & MP' & HGR').
  exists R, m'. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|].
  split.
  { split; [exact HB2|]. split.
    { apply (trees_rod_clear_agree R6u _ m m' HRC Hag).
      unfold Fbw. pose proof HLb as ((HS1 & HS2) & _). unfold dsl_SIZE in HS2.
      intros x [Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]; cbn in Hx;
        [apply MS; unfold dsl_SIZE; lia | apply MS; unfold dsl_SIZE; lia | apply MS; unfold dsl_SIZE; lia | apply MP; exact Hx
        | apply MS; unfold dsl_SIZE; lia]. }
    split.
    { eapply agree_out_trans; [exact HAG|]. eapply agree_out_weaken; [exact Hag|]. exact Fbw_GFB. }
    split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
    intros x Hx. apply HGR'. apply HGR. exact Hx. }
  split; [rewrite (Hfr 2%bv eq_refl); exact Q2|].
  split; [rewrite (Hfr 1%bv eq_refl); exact Q1|].
  split.
  { intros r Hr. apply FillWin6uD.reg_in_true_In in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
      (lazymatch goal with |- getr _ ?r = _ => rewrite (Hfr r eq_refl) end; apply Hsv; reflexivity). }
  intros r Hr. rewrite (Hfr r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
End Walk.
End FXG.
