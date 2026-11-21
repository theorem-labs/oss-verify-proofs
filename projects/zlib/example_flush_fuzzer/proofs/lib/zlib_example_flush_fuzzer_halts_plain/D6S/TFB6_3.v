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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2.
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

Definition dC : cfg := CFG FBv [] [EVar 50%nat] [0x1afe8; 0x1aff8; 0x1b000; 0x1b008; 0x1b010; 0x1b018; 0x1b020; 0x1b028; 0x1b030; 0x1b038; 0x1b040; 0x1b048; 0x1b050; 0x1b058; 0x1b060; 0x1b068; 0x1b070; 0x1b078; 0x1b080; 0x1b088; 0x1b090; 0x1b098; 0x1b0a0; 0x1b0a8; 0x1b0b0; 0x1b0b4; 0x1b0b8; 0x1b90c; 0x1b914; 0x1b91c; 0x1b924; 0x1b92c; 0x1b934] [].

Local Ltac dregs H := destruct H as (HK & P10).

Local Ltac probe_tac n dir X :=
  lazymatch dir with
  | true => run dC 12%nat [true] [RVal (EApp1 0 (ELit n))] (KPN ++ [(10, EVar 45)]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X
  | false => run dC 12%nat [false] [RVal (EApp1 0 (ELit n))] (KPN ++ [(10, EVar 45)]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X
  end.

Lemma dprobe_0 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 0 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1aff8 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 0 =? 0 then (0x1b000 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 0 = arr_get (ds_dyn_ltree_fc X) 0) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 0) 0) as [E|E].
  - probe_tac 0 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 0 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_1 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 1 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b000 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 1 =? 0 then (0x1b008 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 1 = arr_get (ds_dyn_ltree_fc X) 1) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 1) 0) as [E|E].
  - probe_tac 1 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 1 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_2 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 2 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b008 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 2 =? 0 then (0x1b010 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 2 = arr_get (ds_dyn_ltree_fc X) 2) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 2) 0) as [E|E].
  - probe_tac 2 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 2 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_3 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 3 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b010 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 3 =? 0 then (0x1b018 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 3 = arr_get (ds_dyn_ltree_fc X) 3) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 3) 0) as [E|E].
  - probe_tac 3 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 3 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_4 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 4 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b018 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 4 =? 0 then (0x1b020 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 4 = arr_get (ds_dyn_ltree_fc X) 4) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 4) 0) as [E|E].
  - probe_tac 4 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 4 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_5 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 5 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b020 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 5 =? 0 then (0x1b028 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 5 = arr_get (ds_dyn_ltree_fc X) 5) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 5) 0) as [E|E].
  - probe_tac 5 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 5 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_6 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 6 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b028 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 6 =? 0 then (0x1b030 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 6 = arr_get (ds_dyn_ltree_fc X) 6) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 6) 0) as [E|E].
  - probe_tac 6 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 6 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_14 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 14 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b030 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 14 =? 0 then (0x1b038 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 14 = arr_get (ds_dyn_ltree_fc X) 14) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 14) 0) as [E|E].
  - probe_tac 14 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 14 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_15 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 15 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b038 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 15 =? 0 then (0x1b040 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 15 = arr_get (ds_dyn_ltree_fc X) 15) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 15) 0) as [E|E].
  - probe_tac 15 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 15 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_16 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 16 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b040 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 16 =? 0 then (0x1b048 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 16 = arr_get (ds_dyn_ltree_fc X) 16) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 16) 0) as [E|E].
  - probe_tac 16 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 16 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_17 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 17 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b048 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 17 =? 0 then (0x1b050 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 17 = arr_get (ds_dyn_ltree_fc X) 17) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 17) 0) as [E|E].
  - probe_tac 17 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 17 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_18 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 18 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b050 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 18 =? 0 then (0x1b058 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 18 = arr_get (ds_dyn_ltree_fc X) 18) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 18) 0) as [E|E].
  - probe_tac 18 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 18 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_19 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 19 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b058 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 19 =? 0 then (0x1b060 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 19 = arr_get (ds_dyn_ltree_fc X) 19) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 19) 0) as [E|E].
  - probe_tac 19 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 19 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_20 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 20 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b060 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 20 =? 0 then (0x1b068 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 20 = arr_get (ds_dyn_ltree_fc X) 20) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 20) 0) as [E|E].
  - probe_tac 20 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 20 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_21 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 21 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b068 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 21 =? 0 then (0x1b070 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 21 = arr_get (ds_dyn_ltree_fc X) 21) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 21) 0) as [E|E].
  - probe_tac 21 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 21 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_22 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 22 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b070 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 22 =? 0 then (0x1b078 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 22 = arr_get (ds_dyn_ltree_fc X) 22) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 22) 0) as [E|E].
  - probe_tac 22 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 22 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_23 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 23 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b078 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 23 =? 0 then (0x1b080 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 23 = arr_get (ds_dyn_ltree_fc X) 23) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 23) 0) as [E|E].
  - probe_tac 23 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 23 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_24 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 24 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b080 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 24 =? 0 then (0x1b088 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 24 = arr_get (ds_dyn_ltree_fc X) 24) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 24) 0) as [E|E].
  - probe_tac 24 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 24 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_25 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 25 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b088 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 25 =? 0 then (0x1b090 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 25 = arr_get (ds_dyn_ltree_fc X) 25) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 25) 0) as [E|E].
  - probe_tac 25 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 25 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_28 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 28 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b090 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 28 =? 0 then (0x1b098 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 28 = arr_get (ds_dyn_ltree_fc X) 28) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 28) 0) as [E|E].
  - probe_tac 28 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 28 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_29 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 29 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b098 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 29 =? 0 then (0x1b0a0 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 29 = arr_get (ds_dyn_ltree_fc X) 29) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 29) 0) as [E|E].
  - probe_tac 29 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 29 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_30 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 30 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b0a0 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 30 =? 0 then (0x1b0a8 : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 30 = arr_get (ds_dyn_ltree_fc X) 30) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 30) 0) as [E|E].
  - probe_tac 30 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 30 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_31 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 31 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b0a8 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 31 =? 0 then (0x1b90c : word) else (0x1b0b0 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 31 = arr_get (ds_dyn_ltree_fc X) 31) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 31) 0) as [E|E].
  - probe_tac 31 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 31 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_9 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 9 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b90c : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 9 =? 0 then (0x1b914 : word) else (0x1b924 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 9 = arr_get (ds_dyn_ltree_fc X) 9) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 9) 0) as [E|E].
  - probe_tac 9 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 9 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_10 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 10 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b914 : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 10 =? 0 then (0x1b91c : word) else (0x1b924 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 10 = arr_get (ds_dyn_ltree_fc X) 10) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 10) 0) as [E|E].
  - probe_tac 10 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 10 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dprobe_13 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= arr_get (ds_dyn_ltree_fc X) 13 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b91c : word) m s6_rom)
           (mkst R (if arr_get (ds_dyn_ltree_fc X) 13 =? 0 then (0x1b92c : word) else (0x1b924 : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_dyn_ltree_fc X) 13 = arr_get (ds_dyn_ltree_fc X) 13) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 13) 0) as [E|E].
  - probe_tac 13 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
  - probe_tac 13 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Definition dt1 (X : deflate_state) : bool := negb (arr_get (ds_dyn_ltree_fc X) 0 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 1 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 2 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 3 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 4 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 5 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 6 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 14 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 15 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 16 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 17 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 18 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 19 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 20 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 21 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 22 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 23 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 24 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 25 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 28 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 29 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 30 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 31 =? 0).
Definition dt2 (X : deflate_state) : bool := negb (arr_get (ds_dyn_ltree_fc X) 9 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 10 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 13 =? 0).

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

Lemma dt_chain1 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  (forall k, 0 <= k < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) k < 65536) ->
  exists R,
    msteps s6_segs (mkst regs (0x1aff8 : word) m s6_rom)
           (mkst R (if dt1 X then (0x1b0b0 : word) else (0x1b90c : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hty. unfold dt1.
  destruct (dprobe_0 regs m1 m X HF HK P10 Hstrm (Hty 0 ltac:(lia))) as (R0 & Hms0 & HK0 & Q0 & Hfr0).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 0) 0) as [E0|E0].
  2:{ exists R0. split; [cbn [negb orb];  exact Hms0|]. split; [exact HK0|]. split; [exact Q0|]. exact Hfr0. }
  cbn [negb orb].
  destruct (dprobe_1 R0 m1 m X HF HK0 Q0 Hstrm (Hty 1 ltac:(lia))) as (R1 & Hms1 & HK1 & Q1 & Hfr1).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 1) 0) as [E1|E1].
  2:{ exists R1. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; exact Hms1|]. split; [exact HK1|]. split; [exact Q1|]. intros r Hr. rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_2 R1 m1 m X HF HK1 Q1 Hstrm (Hty 2 ltac:(lia))) as (R2 & Hms2 & HK2 & Q2 & Hfr2).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 2) 0) as [E2|E2].
  2:{ exists R2. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; exact Hms2|]. split; [exact HK2|]. split; [exact Q2|]. intros r Hr. rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_3 R2 m1 m X HF HK2 Q2 Hstrm (Hty 3 ltac:(lia))) as (R3 & Hms3 & HK3 & Q3 & Hfr3).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 3) 0) as [E3|E3].
  2:{ exists R3. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; exact Hms3|]. split; [exact HK3|]. split; [exact Q3|]. intros r Hr. rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_4 R3 m1 m X HF HK3 Q3 Hstrm (Hty 4 ltac:(lia))) as (R4 & Hms4 & HK4 & Q4 & Hfr4).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 4) 0) as [E4|E4].
  2:{ exists R4. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; exact Hms4|]. split; [exact HK4|]. split; [exact Q4|]. intros r Hr. rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_5 R4 m1 m X HF HK4 Q4 Hstrm (Hty 5 ltac:(lia))) as (R5 & Hms5 & HK5 & Q5 & Hfr5).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 5) 0) as [E5|E5].
  2:{ exists R5. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; exact Hms5|]. split; [exact HK5|]. split; [exact Q5|]. intros r Hr. rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_6 R5 m1 m X HF HK5 Q5 Hstrm (Hty 6 ltac:(lia))) as (R6 & Hms6 & HK6 & Q6 & Hfr6).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 6) 0) as [E6|E6].
  2:{ exists R6. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; exact Hms6|]. split; [exact HK6|]. split; [exact Q6|]. intros r Hr. rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_14 R6 m1 m X HF HK6 Q6 Hstrm (Hty 14 ltac:(lia))) as (R7 & Hms7 & HK7 & Q7 & Hfr7).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 14) 0) as [E7|E7].
  2:{ exists R7. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; exact Hms7|]. split; [exact HK7|]. split; [exact Q7|]. intros r Hr. rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_15 R7 m1 m X HF HK7 Q7 Hstrm (Hty 15 ltac:(lia))) as (R8 & Hms8 & HK8 & Q8 & Hfr8).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 15) 0) as [E8|E8].
  2:{ exists R8. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; exact Hms8|]. split; [exact HK8|]. split; [exact Q8|]. intros r Hr. rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_16 R8 m1 m X HF HK8 Q8 Hstrm (Hty 16 ltac:(lia))) as (R9 & Hms9 & HK9 & Q9 & Hfr9).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 16) 0) as [E9|E9].
  2:{ exists R9. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; exact Hms9|]. split; [exact HK9|]. split; [exact Q9|]. intros r Hr. rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_17 R9 m1 m X HF HK9 Q9 Hstrm (Hty 17 ltac:(lia))) as (R10 & Hms10 & HK10 & Q10 & Hfr10).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 17) 0) as [E10|E10].
  2:{ exists R10. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; exact Hms10|]. split; [exact HK10|]. split; [exact Q10|]. intros r Hr. rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_18 R10 m1 m X HF HK10 Q10 Hstrm (Hty 18 ltac:(lia))) as (R11 & Hms11 & HK11 & Q11 & Hfr11).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 18) 0) as [E11|E11].
  2:{ exists R11. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; exact Hms11|]. split; [exact HK11|]. split; [exact Q11|]. intros r Hr. rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_19 R11 m1 m X HF HK11 Q11 Hstrm (Hty 19 ltac:(lia))) as (R12 & Hms12 & HK12 & Q12 & Hfr12).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 19) 0) as [E12|E12].
  2:{ exists R12. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; exact Hms12|]. split; [exact HK12|]. split; [exact Q12|]. intros r Hr. rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_20 R12 m1 m X HF HK12 Q12 Hstrm (Hty 20 ltac:(lia))) as (R13 & Hms13 & HK13 & Q13 & Hfr13).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 20) 0) as [E13|E13].
  2:{ exists R13. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; exact Hms13|]. split; [exact HK13|]. split; [exact Q13|]. intros r Hr. rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_21 R13 m1 m X HF HK13 Q13 Hstrm (Hty 21 ltac:(lia))) as (R14 & Hms14 & HK14 & Q14 & Hfr14).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 21) 0) as [E14|E14].
  2:{ exists R14. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; exact Hms14|]. split; [exact HK14|]. split; [exact Q14|]. intros r Hr. rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_22 R14 m1 m X HF HK14 Q14 Hstrm (Hty 22 ltac:(lia))) as (R15 & Hms15 & HK15 & Q15 & Hfr15).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 22) 0) as [E15|E15].
  2:{ exists R15. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; exact Hms15|]. split; [exact HK15|]. split; [exact Q15|]. intros r Hr. rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_23 R15 m1 m X HF HK15 Q15 Hstrm (Hty 23 ltac:(lia))) as (R16 & Hms16 & HK16 & Q16 & Hfr16).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 23) 0) as [E16|E16].
  2:{ exists R16. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; exact Hms16|]. split; [exact HK16|]. split; [exact Q16|]. intros r Hr. rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_24 R16 m1 m X HF HK16 Q16 Hstrm (Hty 24 ltac:(lia))) as (R17 & Hms17 & HK17 & Q17 & Hfr17).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 24) 0) as [E17|E17].
  2:{ exists R17. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; exact Hms17|]. split; [exact HK17|]. split; [exact Q17|]. intros r Hr. rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_25 R17 m1 m X HF HK17 Q17 Hstrm (Hty 25 ltac:(lia))) as (R18 & Hms18 & HK18 & Q18 & Hfr18).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 25) 0) as [E18|E18].
  2:{ exists R18. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; exact Hms18|]. split; [exact HK18|]. split; [exact Q18|]. intros r Hr. rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_28 R18 m1 m X HF HK18 Q18 Hstrm (Hty 28 ltac:(lia))) as (R19 & Hms19 & HK19 & Q19 & Hfr19).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 28) 0) as [E19|E19].
  2:{ exists R19. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; eapply msteps_trans; [exact Hms18|]; exact Hms19|]. split; [exact HK19|]. split; [exact Q19|]. intros r Hr. rewrite (Hfr19 r Hr). rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_29 R19 m1 m X HF HK19 Q19 Hstrm (Hty 29 ltac:(lia))) as (R20 & Hms20 & HK20 & Q20 & Hfr20).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 29) 0) as [E20|E20].
  2:{ exists R20. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; eapply msteps_trans; [exact Hms18|]; eapply msteps_trans; [exact Hms19|]; exact Hms20|]. split; [exact HK20|]. split; [exact Q20|]. intros r Hr. rewrite (Hfr20 r Hr). rewrite (Hfr19 r Hr). rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_30 R20 m1 m X HF HK20 Q20 Hstrm (Hty 30 ltac:(lia))) as (R21 & Hms21 & HK21 & Q21 & Hfr21).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 30) 0) as [E21|E21].
  2:{ exists R21. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; eapply msteps_trans; [exact Hms18|]; eapply msteps_trans; [exact Hms19|]; eapply msteps_trans; [exact Hms20|]; exact Hms21|]. split; [exact HK21|]. split; [exact Q21|]. intros r Hr. rewrite (Hfr21 r Hr). rewrite (Hfr20 r Hr). rewrite (Hfr19 r Hr). rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_31 R21 m1 m X HF HK21 Q21 Hstrm (Hty 31 ltac:(lia))) as (R22 & Hms22 & HK22 & Q22 & Hfr22).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 31) 0) as [E22|E22].
  2:{ exists R22. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; eapply msteps_trans; [exact Hms18|]; eapply msteps_trans; [exact Hms19|]; eapply msteps_trans; [exact Hms20|]; eapply msteps_trans; [exact Hms21|]; exact Hms22|]. split; [exact HK22|]. split; [exact Q22|]. intros r Hr. rewrite (Hfr22 r Hr). rewrite (Hfr21 r Hr). rewrite (Hfr20 r Hr). rewrite (Hfr19 r Hr). rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  exists R22. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; eapply msteps_trans; [exact Hms15|]; eapply msteps_trans; [exact Hms16|]; eapply msteps_trans; [exact Hms17|]; eapply msteps_trans; [exact Hms18|]; eapply msteps_trans; [exact Hms19|]; eapply msteps_trans; [exact Hms20|]; eapply msteps_trans; [exact Hms21|]; exact Hms22|]. split; [exact HK22|]. split; [exact Q22|].
  intros r Hr. rewrite (Hfr22 r Hr). rewrite (Hfr21 r Hr). rewrite (Hfr20 r Hr). rewrite (Hfr19 r Hr). rewrite (Hfr18 r Hr). rewrite (Hfr17 r Hr). rewrite (Hfr16 r Hr). rewrite (Hfr15 r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr).
Qed.

Lemma dt_chain2 : forall regs m1 m X,
  FI m1 m X -> KR regs -> getr regs 10 = zw (p_strm p) -> 0 <= p_strm p < 2 ^ 64 ->
  (forall k, 0 <= k < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) k < 65536) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b90c : word) m s6_rom)
           (mkst R (if dt2 X then (0x1b924 : word) else (0x1b92c : word)) m s6_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (forall r : reg, reg_in r [11]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK P10 Hstrm Hty. unfold dt2.
  destruct (dprobe_9 regs m1 m X HF HK P10 Hstrm (Hty 9 ltac:(lia))) as (R0 & Hms0 & HK0 & Q0 & Hfr0).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 9) 0) as [E0|E0].
  2:{ exists R0. split; [cbn [negb orb];  exact Hms0|]. split; [exact HK0|]. split; [exact Q0|]. exact Hfr0. }
  cbn [negb orb].
  destruct (dprobe_10 R0 m1 m X HF HK0 Q0 Hstrm (Hty 10 ltac:(lia))) as (R1 & Hms1 & HK1 & Q1 & Hfr1).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 10) 0) as [E1|E1].
  2:{ exists R1. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; exact Hms1|]. split; [exact HK1|]. split; [exact Q1|]. intros r Hr. rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  destruct (dprobe_13 R1 m1 m X HF HK1 Q1 Hstrm (Hty 13 ltac:(lia))) as (R2 & Hms2 & HK2 & Q2 & Hfr2).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 13) 0) as [E2|E2].
  2:{ exists R2. split; [cbn [negb orb]; eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; exact Hms2|]. split; [exact HK2|]. split; [exact Q2|]. intros r Hr. rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  cbn [negb orb].
  exists R2. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; exact Hms2|]. split; [exact HK2|]. split; [exact Q2|].
  intros r Hr. rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr).
Qed.
End Walk.
End FXG.
