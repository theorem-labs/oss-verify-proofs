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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7 TFB6_8 TFB6_9 TFB6_10 TFB6_11.
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

Definition FIx (m1 m : word -> option byte) (X : deflate_state) : Prop :=
  (exists j, BRm m (set_bi_buf X j)) /\ trees_rod_clear6 m /\ agree_out GFB m1 m /\ mapped m (SP - 144) 208
  /\ (forall x, mem x <> None -> m x <> None).

Lemma FI_FIx : forall m1 m X, FI m1 m X -> FIx m1 m X.
Proof. intros m1 m X (A & B). split; [|exact B]. exists (ds_bi_buf X). destruct X; exact A. Qed.

Local Ltac open_fix HF :=
  let j := fresh "j" in let HB := fresh "HB" in let HRC := fresh "HRC" in let HAG := fresh "HAG" in let MF := fresh "MF" in let HGR := fresh "HGR" in
  pose proof HF as HF'; destruct HF' as ((j & HB) & HRC & HAG & MF & HGR); unfold mapped in MF; open_br6 HB.

Definition hC : cfg := CFG FBv [] [EVar 50%nat] [0x1b610; 0x1b678; 0x1b6c4; 0x1b69c; 0x1b734; 0x1b7bc; 0x1b830] [].

Local Abbreviation RBr := SendTree6_1.RBr.


Definition H1R (R : bvmap 5 word) (mb : Z) (X : deflate_state) : Prop :=
  KR R /\ getr R 10 = zw mb /\ getr R 20 = zw (S + 2047) /\ RBr 13%bv R X /\ getr R 15 = zw (ds_bi_valid X)
  /\ getr R 12 = zw (ds_l_max_code X) /\ getr R 18 = zw (ds_d_max_code X) /\ getr R 14 = zw (ds_l_max_code X + 65280)
  /\ getr R 11 = zw 65535 /\ getr R 16 = zw 12.

Lemma stage1 : forall regs m1 m X mb,
  FI m1 m X -> KR regs -> getr regs 10 = zw mb -> getr regs 20 = zw (S + 2047) -> getr regs 12 = zw (ds_bi_valid X) ->
  0 <= mb <= 18 -> BINV PBL X -> sb_room PBL X 3 ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  exists R m',
    msteps s6_segs (mkst regs (0x1b534 : word) m s6_rom) (mkst R (0x1b610 : word) m' s6_rom)
    /\ FIx m1 m' X7
    /\ (H1R R mb X7 /\ (forall r : reg, reg_in r [11; 12; 13; 14; 15; 16; 18]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF HK P10 P20 P12 Hmb HBI Hroom Hlmc Hdmc. cbv zeta. change (Z.shiftl DYN_TREES 1 + last) with (4 + last).
  open_fi HF. kd HK. destruct HBI as (Hbv & Hbb & Hpd).
  pose proof (dsl_l_desc_max_code _ _ _ _ _ _ _ _ Hsc) as Clm. pose proof (dsl_d_desc_max_code _ _ _ _ _ _ _ _ Hsc) as Cdm.
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - 3) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - run hC 80%nat [false] [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RVal (EVar 41); RVal (EVar 42)]
        (KPN ++ [(12, EVar 35); (10, EVar 43); (20, EAdd (EVar 32) (ELit 2047))])
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb] X.
    site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold H1R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (13%bv : reg) HR nf | bv_flush (15%bv : reg) HR nf | reg1 HR Hfr ]).
  - run hC 80%nat [true] [RVal (EVar 36); RVal (EVar 41); RVal (EVar 42)]
        (KPN ++ [(12, EVar 35); (10, EVar 43); (20, EAdd (EVar 32) (ELit 2047))])
        [S; PB; ds_pending X; ds_bi_valid X; ds_bi_buf X; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb] X.
    site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold H1R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (13%bv : reg) HR nf | bv_keep (15%bv : reg) HR nf | reg1 HR Hfr ]).
Qed.


Definition S3PC (X : deflate_state) : word := if 12 <=? ds_bi_valid X then (0x1b6c4 : word) else (0x1b678 : word).

Definition H2R (R : bvmap 5 word) (mb : Z) (X : deflate_state) : Prop :=
  KR R /\ getr R 10 = zw mb /\ getr R 20 = zw (S + 2047) /\ RBr 13%bv R X /\ getr R 15 = zw (ds_bi_valid X)
  /\ getr R 12 = zw (ds_l_max_code X) /\ getr R 18 = zw (ds_d_max_code X) /\ getr R 11 = zw 65535.

Local Ltac h1d H := destruct H as (HK & P10 & P20 & HRB & P15 & P12 & P18 & P14 & P11 & P16).
Definition H1P : list (Z * expr) :=
  KPN ++ [(10, EVar 43); (20, EAdd (EVar 32) (ELit 2047)); (13, EVar 44); (15, EVar 35); (12, EVar 41); (18, EVar 42);
          (14, EAdd (EVar 41) (ELit 65280)); (11, ELit 65535); (16, ELit 12)].

Lemma stage2 : forall regs m1 m X mb,
  FIx m1 m X -> H1R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> sb_room PBL X 5 ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  let X8 := send_bits X (ds_l_max_code X + 1 - 257) 5 in
  exists R m',
    msteps s6_segs (mkst regs (0x1b610 : word) m s6_rom) (mkst R (S3PC X8) m' s6_rom)
    /\ FIx m1 m' X8
    /\ (H2R R mb X8 /\ (forall r : reg, reg_in r [13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF HR1 Hmb HBI Hroom Hlmc Hdmc. cbv zeta.
  open_fix HF. h1d HR1. kd HK. destruct HBI as (Hbv & Hbb & Hpd). pose proof (u64_range (getr regs 13)) as U13.
  unfold sb_room, Buf_size in Hroom. unfold S3PC.
  destruct (Z.ltb_spec (16 - 5) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - assert (Ebv : ds_bi_valid (send_bits X (ds_l_max_code X + 1 - 257) 5) = ds_bi_valid X + 5 - 16)
      by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 12 (ds_bi_valid X + 5 - 16)) as [C2|C2].
    + run hC 80%nat [false; true] [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H1P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
        ltac:(split; [| fr_weak Hfr]; unfold H2R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (13%bv : reg) HR nf | bv_flush (15%bv : reg) HR nf | reg1 HR Hfr ]).
    + run hC 80%nat [false; false] [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H1P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
        ltac:(split; [| fr_weak Hfr]; unfold H2R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (13%bv : reg) HR nf | bv_flush (15%bv : reg) HR nf | reg1 HR Hfr ]).
  - assert (Ebv : ds_bi_valid (send_bits X (ds_l_max_code X + 1 - 257) 5) = ds_bi_valid X + 5)
      by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 12 (ds_bi_valid X + 5)) as [C2|C2].
    + run hC 80%nat [true; false] NoReads H1P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
        ltac:(split; [| fr_weak Hfr]; unfold H2R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (13%bv : reg) HR nf | bv_keep (15%bv : reg) HR nf | reg1 HR Hfr ]).
    + run hC 80%nat [true; true] NoReads H1P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
        ltac:(split; [| fr_weak Hfr]; unfold H2R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (13%bv : reg) HR nf | bv_keep (15%bv : reg) HR nf | reg1 HR Hfr ]).
Qed.


Definition S4PC (X : deflate_state) : word := if 13 <=? ds_bi_valid X then (0x1b734 : word) else (0x1b69c : word).

Definition H3R (R : bvmap 5 word) (mb : Z) (X : deflate_state) : Prop :=
  KR R /\ getr R 20 = zw (S + 2047) /\ RBr 13%bv R X /\ getr R 17 = zw (ds_bi_valid X)
  /\ getr R 15 = zw (mb + 1) /\ getr R 10 = zw (mb + 65533) /\ getr R 11 = zw 65535
  /\ getr R 12 = zw (ds_l_max_code X) /\ getr R 18 = zw (ds_d_max_code X).

Local Ltac h2d H := destruct H as (HK & P10 & P20 & HRB & P15 & P12 & P18 & P11).
Definition H2P : list (Z * expr) :=
  KPN ++ [(10, EVar 43); (20, EAdd (EVar 32) (ELit 2047)); (13, EVar 44); (15, EVar 35); (12, EVar 41); (18, EVar 42); (11, ELit 65535)].

Lemma stage3 : forall regs m1 m X mb,
  FIx m1 m X -> H2R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> sb_room PBL X 5 ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  let X9 := send_bits X (ds_d_max_code X + 1 - 1) 5 in
  exists R m',
    msteps s6_segs (mkst regs (S3PC X) m s6_rom) (mkst R (S4PC X9) m' s6_rom)
    /\ FIx m1 m' X9
    /\ (H3R R mb X9 /\ (forall r : reg, reg_in r [10; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF HR2 Hmb HBI Hroom Hlmc Hdmc. cbv zeta.
  open_fix HF. h2d HR2. kd HK. destruct HBI as (Hbv & Hbb & Hpd). pose proof (u64_range (getr regs 13)) as U13.
  unfold sb_room, Buf_size in Hroom. unfold S3PC, S4PC.
  destruct (Z.ltb_spec (16 - 5) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - replace (12 <=? ds_bi_valid X) with true by (symmetry; apply Z.leb_le; lia).
    assert (Ebv : ds_bi_valid (send_bits X (ds_d_max_code X + 1 - 1) 5) = ds_bi_valid X + 5 - 16)
      by (rewrite send_bits_flush_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 13 (ds_bi_valid X + 5 - 16)) as [C2|C2].
    + run hC 80%nat [false] [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H2P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
        ltac:(split; [| fr_weak Hfr]; unfold H3R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (13%bv : reg) HR nf | bv_flush (17%bv : reg) HR nf | reg1 HR Hfr ]).
    + run hC 80%nat [true] [RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] H2P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
        ltac:(split; [| fr_weak Hfr]; unfold H3R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_flush (13%bv : reg) HR nf | bv_flush (17%bv : reg) HR nf | reg1 HR Hfr ]).
  - replace (12 <=? ds_bi_valid X) with false by (symmetry; apply Z.leb_gt; lia).
    assert (Ebv : ds_bi_valid (send_bits X (ds_d_max_code X + 1 - 1) 5) = ds_bi_valid X + 5)
      by (rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid; reflexivity).
    rewrite Ebv. destruct (Z.leb_spec 13 (ds_bi_valid X + 5)) as [C2|C2].
    + run hC 80%nat [true] NoReads H2P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
        ltac:(split; [| fr_weak Hfr]; unfold H3R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (13%bv : reg) HR nf | bv_keep (17%bv : reg) HR nf | reg1 HR Hfr ]).
    + run hC 80%nat [false] NoReads H2P
          [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
      site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
        ltac:(split; [| fr_weak Hfr]; unfold H3R; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
              first [ rb_keep (13%bv : reg) HR nf | bv_keep (17%bv : reg) HR nf | reg1 HR Hfr ]).
Qed.


Definition LR (R : bvmap 5 word) (mb r : Z) (X : deflate_state) : Prop :=
  KR R /\ getr R 20 = zw (S + 2047) /\ RBr 11%bv R X /\ getr R 17 = zw (ds_bi_valid X)
  /\ getr R 10 = zw (S + 2750) /\ getr R 14 = zw (0x12410 + r) /\ getr R 15 = zw (0x12410 + (mb + 1))
  /\ getr R 13 = zw 14 /\ getr R 16 = zw 16
  /\ getr R 12 = zw (ds_l_max_code X) /\ getr R 18 = zw (ds_d_max_code X).

Local Ltac h3d H := destruct H as (HK & P20 & HRB & P17 & P15 & P10 & P11 & P12 & P18).
Definition H3P : list (Z * expr) :=
  KPN ++ [(20, EAdd (EVar 32) (ELit 2047)); (13, EVar 44); (17, EVar 35); (15, EAdd (EVar 43) (ELit 1)); (10, EAdd (EVar 43) (ELit 65533));
          (11, ELit 65535); (12, EVar 41); (18, EVar 42)].

Lemma stage4 : forall regs m1 m X mb,
  FIx m1 m X -> H3R regs mb X -> 0 <= mb <= 18 -> BINV PBL X -> sb_room PBL X 4 ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  let X10 := send_bits X (mb + 1 - 4) 4 in
  exists R m',
    msteps s6_segs (mkst regs (S4PC X) m s6_rom) (mkst R (0x1b7bc : word) m' s6_rom)
    /\ FIx m1 m' X10
    /\ (LR R mb 0 X10 /\ (forall r : reg, reg_in r [10; 11; 13; 14; 15; 16; 17]%bv = false -> getr R r = getr regs r)).
Proof.
  intros regs m1 m X mb HF HR3 Hmb HBI Hroom Hlmc Hdmc. cbv zeta.
  open_fix HF. h3d HR3. kd HK. destruct HBI as (Hbv & Hbb & Hpd). pose proof (u64_range (getr regs 13)) as U13.
  unfold sb_room, Buf_size in Hroom. unfold S4PC.
  destruct (Z.ltb_spec (16 - 4) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - replace (13 <=? ds_bi_valid X) with true by (symmetry; apply Z.leb_le; lia).
    run hC 80%nat NoDirs [RVal (EVar 33); RVal (EVar 34); RVal (EVar 35)] H3P
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
    site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (11%bv : reg) HR nf | bv_flush (17%bv : reg) HR nf | reg1 HR Hfr ]).
  - replace (13 <=? ds_bi_valid X) with false by (symmetry; apply Z.leb_gt; lia).
    run hC 80%nat NoDirs NoReads H3P
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 13)] X.
    site_finx Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (11%bv : reg) HR nf | bv_keep (17%bv : reg) HR nf | reg1 HR Hfr ]).
Qed.


Local Ltac lrd H := destruct H as (HK & P20 & HRB & P17 & P10 & P14 & P15 & P13 & P16 & P12 & P18).
Definition LRP : list (Z * expr) :=
  KPN ++ [(20, EAdd (EVar 32) (ELit 2047)); (11, EVar 44); (17, EVar 35); (10, EAdd (EVar 32) (ELit 2750));
          (14, EAdd (ELit 0x12410) (EVar 45)); (15, EAdd (ELit 0x12410) (EAdd (EVar 43) (ELit 1))); (13, ELit 14); (16, ELit 16);
          (12, EVar 41); (18, EVar 42)].

Definition HNEXT (mb r : Z) : word := if r + 1 =? mb + 1 then (0x1b830 : word) else (0x1b7bc : word).

Lemma hiter : forall regs m1 m X mb r,
  FIx m1 m X -> LR regs mb r X -> 0 <= mb <= 18 -> 0 <= r <= mb -> BINV PBL X -> sb_room PBL X 3 ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  (forall k, 0 <= k < 39 -> 0 <= arr_get (ds_bl_tree_dl X) k < 65536) ->
  let X' := send_bits X (Len X TB (arr_get bl_order_a r)) 3 in
  exists R m',
    msteps s6_segs (mkst regs (0x1b7bc : word) m s6_rom) (mkst R (HNEXT mb r) m' s6_rom)
    /\ FI m1 m' X'
    /\ (LR R mb (r + 1) X' /\ (forall r0 : reg, reg_in r0 [5; 6; 7; 11; 14; 17]%bv = false -> getr R r0 = getr regs r0)).
Proof.
  intros regs m1 m X mb r HF HL Hmb Hr HBI Hroom Hlmc Hdmc Hty. cbv zeta.
  open_fix HF. lrd HL. kd HK. destruct HBI as (Hbv & Hbb & Hpd). pose proof (u64_range (getr regs 11)) as U11.
  pose proof (bl_order_cells R6 _ _ trod_ok6 HRC) as BO. cbn [tr_bl_order R6] in BO.
  pose proof (bl_order_bound r) as Bor.
  pose proof (Hty (arr_get bl_order_a r) ltac:(lia)) as Vc.
  unfold sb_room, Buf_size in Hroom. unfold HNEXT. unfold Len. cbn [tree_dl].
  destruct (Z.ltb_spec (16 - 3) (ds_bi_valid X)) as [CF|CF]; [specialize (Hroom ltac:(unfold Buf_size; lia))|];
    destruct (Z.eqb_spec (r + 1) (mb + 1)) as [Er|Er].
  - run hC 80%nat [false; false] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45))); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 11); r] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (11%bv : reg) HR nf | bv_flush (17%bv : reg) HR nf | reg1 HR Hfr ]).
  - run hC 80%nat [false; true] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45))); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35)] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 11); r] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_flush nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_flush (11%bv : reg) HR nf | bv_flush (17%bv : reg) HR nf | reg1 HR Hfr ]).
  - run hC 80%nat [true; true] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45)))] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 11); r] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (11%bv : reg) HR nf | bv_keep (17%bv : reg) HR nf | reg1 HR Hfr ]).
  - run hC 80%nat [true; false] [RVal (EApp1 5 (EVar 45)); RVal (EApp1 4 (EApp1 5 (EVar 45)))] LRP
        [S; PB; ds_pending X; ds_bi_valid X; 0; last; 0; 0; SP; ds_l_max_code X; ds_d_max_code X; mb; bv_unsigned (getr regs 11); r] X.
    site_fin Hms HR Hfr HB HRC HAG MF HGR MS MP ltac:(st_keep nf)
      ltac:(split; [| fr_weak Hfr]; unfold LR; rewrite ?sb_lmc, ?sb_dmc; split; [kregs HR Hfr|]; repeat split;
            first [ rb_keep (11%bv : reg) HR nf | bv_keep (17%bv : reg) HR nf | reg1 HR Hfr ]).
Qed.

Lemma hloop : forall mb, 0 <= mb <= 18 -> forall k (f : nat) r regs m1 m X,
  r + Z.of_nat k = mb + 1 -> (1 <= k)%nat -> (k <= f)%nat -> 0 <= r ->
  FIx m1 m X -> LR regs mb r X -> BINV PBL X -> sat_ok PBL f X (mb + 1) r ->
  0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X) i < 65536) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b7bc : word) m s6_rom) (mkst R (0x1b830 : word) m' s6_rom)
    /\ FI m1 m' (send_all_trees_loop f X (mb + 1) r)
    /\ LR R mb (mb + 1) (send_all_trees_loop f X (mb + 1) r)
    /\ (forall r0 : reg, reg_in r0 [5; 6; 7; 11; 14; 17]%bv = false -> getr R r0 = getr regs r0).
Proof.
  intros mb Hmb. induction k as [|k IH]; intros f r regs m1 m X Hrk Hk Hf Hr0 HF HL HBI Hok Hlmc Hdmc Hty; [lia|].
  destruct f as [|f]; [lia|]. rewrite sat_loop_step. rewrite sat_ok_step in Hok.
  replace (r <? mb + 1) with true in Hok |- * by (symmetry; apply Z.ltb_lt; lia). destruct Hok as [Hroom Hok].
  destruct (hiter regs m1 m X mb r HF HL Hmb ltac:(lia) HBI Hroom Hlmc Hdmc Hty) as (R1 & ma & Hms1 & HF1 & HL1 & Hfr1).
  unfold HNEXT in Hms1. set (X' := send_bits X _ 3) in *.
  assert (HBI' : BINV PBL X') by (apply send_bits_BINV; [exact HBI | lia | exact Hroom]).
  assert (Hty' : forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X') i < 65536).
  { intros i Hi. subst X'. pose proof (sb_tree_dl_TB X (Len X TB (arr_get bl_order_a r)) 3) as E. cbn [tree_dl] in E. rewrite E. apply Hty. exact Hi. }
  assert (Hlmc' : 0 <= ds_l_max_code X' < 600) by (subst X'; rewrite sb_lmc; exact Hlmc).
  assert (Hdmc' : 0 <= ds_d_max_code X' < 600) by (subst X'; rewrite sb_dmc; exact Hdmc).
  destruct k as [|k'].
  - replace (r + 1 =? mb + 1) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia).
    rewrite sat_loop_done by lia. replace (r + 1) with (mb + 1) in HL1 by lia.
    exists R1, ma. split; [exact Hms1|]. split; [exact HF1|]. split; [exact HL1 | exact Hfr1].
  - replace (r + 1 =? mb + 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH f (r + 1) R1 m1 ma X' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (FI_FIx _ _ _ HF1) HL1 HBI' Hok Hlmc' Hdmc' Hty')
      as (R2 & mb2 & Hms2 & HF2 & HL2 & Hfr2).
    exists R2, mb2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HF2|]. split; [exact HL2|].
    intros r0 Hq. rewrite (Hfr2 r0 Hq). exact (Hfr1 r0 Hq).
Qed.


Lemma sat_lmc : forall f s b r, ds_l_max_code (send_all_trees_loop f s b r) = ds_l_max_code s.
Proof. induction f as [|f IH]; intros; [reflexivity|]. rewrite sat_loop_step. destruct (r <? b); [|reflexivity]. rewrite IH. apply sb_lmc. Qed.
Lemma sat_dmc : forall f s b r, ds_d_max_code (send_all_trees_loop f s b r) = ds_d_max_code s.
Proof. induction f as [|f IH]; intros; [reflexivity|]. rewrite sat_loop_step. destruct (r <? b); [|reflexivity]. rewrite IH. apply sb_dmc. Qed.

Lemma dynhdr : forall regs m1 m X mb,
  FI m1 m X -> KR regs -> getr regs 10 = zw mb -> getr regs 20 = zw (S + 2047) -> getr regs 12 = zw (ds_bi_valid X) ->
  0 <= mb <= 18 -> 0 <= ds_l_max_code X < 600 -> 0 <= ds_d_max_code X < 600 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X) i < 65536) ->
  let lmc := ds_l_max_code X in
  let dmc := ds_d_max_code X in
  let X7 := send_bits X (Z.shiftl DYN_TREES 1 + last) 3 in
  let X8 := send_bits X7 (lmc + 1 - 257) 5 in
  let X9 := send_bits X8 (dmc + 1 - 1) 5 in
  let X10 := send_bits X9 (mb + 1 - 4) 4 in
  let X11 := send_all_trees_loop 19 X10 (mb + 1) 0 in
  BINV PBL X -> sb_room PBL X 3 -> sb_room PBL X7 5 -> sb_room PBL X8 5 -> sb_room PBL X9 4 -> sat_ok PBL 19 X10 (mb + 1) 0 ->
  exists R m',
    msteps s6_segs (mkst regs (0x1b534 : word) m s6_rom) (mkst R (0x1b830 : word) m' s6_rom)
    /\ FI m1 m' X11 /\ KR R /\ getr R 12 = zw lmc /\ getr R 18 = zw dmc /\ getr R 20 = zw (S + 2047)
    /\ (forall r : reg, reg_in r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X mb HF HK P10 P20 P12 Hmb Hlmc Hdmc Hty. cbv zeta. intros HBI R3 R8 R9 R10 Rsat.
  destruct (stage1 regs m1 m X mb HF HK P10 P20 P12 Hmb HBI R3 Hlmc Hdmc) as (R1 & ma & Hms1 & HF1 & HR1 & Hfr1).
  set (X7 := send_bits X _ 3) in *.
  assert (HBI7 : BINV PBL X7) by (apply send_bits_BINV; [exact HBI | lia | exact R3]).
  assert (L7 : ds_l_max_code X7 = ds_l_max_code X) by (subst X7; apply sb_lmc).
  assert (D7 : ds_d_max_code X7 = ds_d_max_code X) by (subst X7; apply sb_dmc).
  assert (T7 : ds_bl_tree_dl X7 = ds_bl_tree_dl X) by (subst X7; exact (sb_tree_dl_TB X _ 3)).
  destruct (stage2 R1 m1 ma X7 mb HF1 HR1 Hmb HBI7 R8 ltac:(rewrite L7; exact Hlmc) ltac:(rewrite D7; exact Hdmc))
    as (R2 & mb2 & Hms2 & HF2 & HR2 & Hfr2).
  rewrite L7 in Hms2, HF2, HR2.
  set (X8 := send_bits X7 _ 5) in *.
  assert (HBI8 : BINV PBL X8) by (apply send_bits_BINV; [exact HBI7 | lia | exact R8]).
  assert (L8 : ds_l_max_code X8 = ds_l_max_code X) by (subst X8; rewrite sb_lmc; exact L7).
  assert (D8 : ds_d_max_code X8 = ds_d_max_code X) by (subst X8; rewrite sb_dmc; exact D7).
  assert (T8 : ds_bl_tree_dl X8 = ds_bl_tree_dl X) by (subst X8; rewrite <- T7; exact (sb_tree_dl_TB X7 _ 5)).
  destruct (stage3 R2 m1 mb2 X8 mb HF2 HR2 Hmb HBI8 R9 ltac:(rewrite L8; exact Hlmc) ltac:(rewrite D8; exact Hdmc))
    as (R3' & mc3 & Hms3 & HF3 & HR3 & Hfr3).
  rewrite D8 in Hms3, HF3, HR3.
  set (X9 := send_bits X8 _ 5) in *.
  assert (HBI9 : BINV PBL X9) by (apply send_bits_BINV; [exact HBI8 | lia | exact R9]).
  assert (L9 : ds_l_max_code X9 = ds_l_max_code X) by (subst X9; rewrite sb_lmc; exact L8).
  assert (D9 : ds_d_max_code X9 = ds_d_max_code X) by (subst X9; rewrite sb_dmc; exact D8).
  assert (T9 : ds_bl_tree_dl X9 = ds_bl_tree_dl X) by (subst X9; rewrite <- T8; exact (sb_tree_dl_TB X8 _ 5)).
  destruct (stage4 R3' m1 mc3 X9 mb HF3 HR3 Hmb HBI9 R10 ltac:(rewrite L9; exact Hlmc) ltac:(rewrite D9; exact Hdmc))
    as (R4 & md & Hms4 & HF4 & HL4 & Hfr4).
  set (X10 := send_bits X9 _ 4) in *.
  assert (HBI10 : BINV PBL X10) by (apply send_bits_BINV; [exact HBI9 | lia | exact R10]).
  assert (L10 : ds_l_max_code X10 = ds_l_max_code X) by (subst X10; rewrite sb_lmc; exact L9).
  assert (D10 : ds_d_max_code X10 = ds_d_max_code X) by (subst X10; rewrite sb_dmc; exact D9).
  assert (T10 : ds_bl_tree_dl X10 = ds_bl_tree_dl X) by (subst X10; rewrite <- T9; exact (sb_tree_dl_TB X9 _ 4)).
  destruct (hloop mb Hmb (Z.to_nat (mb + 1)) 19%nat 0 R4 m1 md X10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              HF4 HL4 HBI10 Rsat ltac:(rewrite L10; exact Hlmc) ltac:(rewrite D10; exact Hdmc)
              ltac:(rewrite T10; exact Hty))
    as (R5 & me & Hms5 & HF5 & HL5 & Hfr5).
  exists R5, me. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
    eapply msteps_trans; [exact Hms4 | exact Hms5]. }
  split; [exact HF5|].
  destruct HL5 as (HK5 & Q20 & _ & _ & _ & _ & _ & _ & _ & Q12 & Q18).
  rewrite sat_lmc, L10 in Q12. rewrite sat_dmc, D10 in Q18.
  split; [exact HK5|]. split; [exact Q12|]. split; [exact Q18|]. split; [exact Q20|].
  intros r Hr.
  rewrite (Hfr5 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  rewrite (Hfr3 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity). rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.
End FXG.
