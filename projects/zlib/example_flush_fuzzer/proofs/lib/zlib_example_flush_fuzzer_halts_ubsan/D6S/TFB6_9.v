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
  FillWin6D CompressBlk6_1 CompressBlk6_4 BuildTree6_10 TrFlushBits6 TrStored6 TrInit6 SendTree6_1 SendTree6_5 TFB6_1 TFB6_2 TFB6_3 TFB6_4 TFB6_5 TFB6_6 TFB6_7 TFB6_8.
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

Definition mC : cfg := CFG FBv [] [EVar 50%nat] [0x1b34c; 0x1b35c; 0x1b36c; 0x1b37c; 0x1b38c; 0x1b39c; 0x1b3ac; 0x1b3bc; 0x1b3cc; 0x1b3dc; 0x1b3ec; 0x1b3fc; 0x1b40c; 0x1b41c; 0x1b42c; 0x1b43c; 0x1b448] [].

Local Abbreviation BLL X i := (arr_get (ds_bl_tree_dl X) i).

Local Ltac mprobe_tac i dir X :=
  lazymatch dir with
  | true => run mC 12%nat [true] [RVal (EApp1 4 (ELit i))] (KPN ++ [(18, EVar 38); (19, EVar 39); (20, EAdd (EVar 32) (ELit 2047))]) [S; PB; 0; 0; 0; last; len; bufp; SP] X
  | false => run mC 12%nat [false] [RVal (EApp1 4 (ELit i))] (KPN ++ [(18, EVar 38); (19, EVar 39); (20, EAdd (EVar 32) (ELit 2047))]) [S; PB; 0; 0; 0; last; len; bufp; SP] X
  end.

Lemma mprobe_18 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 15 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b34c : word) m s6_rom)
           (mkst R (if BLL X 15 =? 0 then (0x1b35c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 15 <> 0 -> getr R 10 = zw 18)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 15 = BLL X 15) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 15) 0) as [E|E].
  - mprobe_tac 15 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 15 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_17 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 1 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b35c : word) m s6_rom)
           (mkst R (if BLL X 1 =? 0 then (0x1b36c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 1 <> 0 -> getr R 10 = zw 17)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 1 = BLL X 1) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 1) 0) as [E|E].
  - mprobe_tac 1 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 1 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_16 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 14 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b36c : word) m s6_rom)
           (mkst R (if BLL X 14 =? 0 then (0x1b37c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 14 <> 0 -> getr R 10 = zw 16)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 14 = BLL X 14) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 14) 0) as [E|E].
  - mprobe_tac 14 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 14 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_15 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 2 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b37c : word) m s6_rom)
           (mkst R (if BLL X 2 =? 0 then (0x1b38c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 2 <> 0 -> getr R 10 = zw 15)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 2 = BLL X 2) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 2) 0) as [E|E].
  - mprobe_tac 2 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 2 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_14 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 13 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b38c : word) m s6_rom)
           (mkst R (if BLL X 13 =? 0 then (0x1b39c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 13 <> 0 -> getr R 10 = zw 14)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 13 = BLL X 13) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 13) 0) as [E|E].
  - mprobe_tac 13 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 13 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_13 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 3 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b39c : word) m s6_rom)
           (mkst R (if BLL X 3 =? 0 then (0x1b3ac : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 3 <> 0 -> getr R 10 = zw 13)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 3 = BLL X 3) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 3) 0) as [E|E].
  - mprobe_tac 3 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 3 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_12 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 12 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3ac : word) m s6_rom)
           (mkst R (if BLL X 12 =? 0 then (0x1b3bc : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 12 <> 0 -> getr R 10 = zw 12)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 12 = BLL X 12) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 12) 0) as [E|E].
  - mprobe_tac 12 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 12 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_11 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 4 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3bc : word) m s6_rom)
           (mkst R (if BLL X 4 =? 0 then (0x1b3cc : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 4 <> 0 -> getr R 10 = zw 11)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 4 = BLL X 4) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 4) 0) as [E|E].
  - mprobe_tac 4 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 4 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_10 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 11 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3cc : word) m s6_rom)
           (mkst R (if BLL X 11 =? 0 then (0x1b3dc : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 11 <> 0 -> getr R 10 = zw 10)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 11 = BLL X 11) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 11) 0) as [E|E].
  - mprobe_tac 11 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 11 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_9 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 5 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3dc : word) m s6_rom)
           (mkst R (if BLL X 5 =? 0 then (0x1b3ec : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 5 <> 0 -> getr R 10 = zw 9)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 5 = BLL X 5) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 5) 0) as [E|E].
  - mprobe_tac 5 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 5 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_8 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 10 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3ec : word) m s6_rom)
           (mkst R (if BLL X 10 =? 0 then (0x1b3fc : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 10 <> 0 -> getr R 10 = zw 8)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 10 = BLL X 10) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 10) 0) as [E|E].
  - mprobe_tac 10 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 10 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_7 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 6 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b3fc : word) m s6_rom)
           (mkst R (if BLL X 6 =? 0 then (0x1b40c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 6 <> 0 -> getr R 10 = zw 7)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 6 = BLL X 6) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 6) 0) as [E|E].
  - mprobe_tac 6 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 6 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_6 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 9 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b40c : word) m s6_rom)
           (mkst R (if BLL X 9 =? 0 then (0x1b41c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 9 <> 0 -> getr R 10 = zw 6)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 9 = BLL X 9) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 9) 0) as [E|E].
  - mprobe_tac 9 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 9 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_5 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 7 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b41c : word) m s6_rom)
           (mkst R (if BLL X 7 =? 0 then (0x1b42c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 7 <> 0 -> getr R 10 = zw 5)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 7 = BLL X 7) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 7) 0) as [E|E].
  - mprobe_tac 7 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 7 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma mprobe_4 : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 8 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b42c : word) m s6_rom)
           (mkst R (if BLL X 8 =? 0 then (0x1b43c : word) else (0x1b448 : word)) m s6_rom)
    /\ KR R /\ KR3 R /\ (BLL X 8 <> 0 -> getr R 10 = zw 4)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 8 = BLL X 8) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (BLL X 8) 0) as [E|E].
  - mprobe_tac 8 true X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros NE; exfalso; exact (NE E) | fr_weak Hfr].
  - mprobe_tac 8 false X. exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
    split; [intros _; reg1 HR Hfr | fr_weak Hfr].
Qed.

Definition mbv (X : deflate_state) : Z :=
  if negb (BLL X 15 =? 0) then 18 else
  if negb (BLL X 1 =? 0) then 17 else
  if negb (BLL X 14 =? 0) then 16 else
  if negb (BLL X 2 =? 0) then 15 else
  if negb (BLL X 13 =? 0) then 14 else
  if negb (BLL X 3 =? 0) then 13 else
  if negb (BLL X 12 =? 0) then 12 else
  if negb (BLL X 4 =? 0) then 11 else
  if negb (BLL X 11 =? 0) then 10 else
  if negb (BLL X 5 =? 0) then 9 else
  if negb (BLL X 10 =? 0) then 8 else
  if negb (BLL X 6 =? 0) then 7 else
  if negb (BLL X 9 =? 0) then 6 else
  if negb (BLL X 7 =? 0) then 5 else
  if negb (BLL X 8 =? 0) then 4 else
  if negb (BLL X 0 =? 0) then 3 else 2.

Lemma bblt_step : forall f X mb,
  build_bl_tree_loop (Datatypes.S f) X mb =
    (if 3 <=? mb then if negb (Len X TB (arr_get bl_order_a mb) =? 0) then mb else build_bl_tree_loop f X (mb - 1) else mb).
Proof. reflexivity. Qed.

Lemma mbv_eq : forall X, build_bl_tree_loop 17 X 18 = mbv X.
Proof.
  intros X. unfold mbv. unfold Len, tree_dl.
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 18) with 15 by (vm_compute; reflexivity). replace (18 - 1) with 17 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 15 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 17) with 1 by (vm_compute; reflexivity). replace (17 - 1) with 16 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 1 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 16) with 14 by (vm_compute; reflexivity). replace (16 - 1) with 15 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 14 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 15) with 2 by (vm_compute; reflexivity). replace (15 - 1) with 14 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 2 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 14) with 13 by (vm_compute; reflexivity). replace (14 - 1) with 13 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 13 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 13) with 3 by (vm_compute; reflexivity). replace (13 - 1) with 12 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 3 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 12) with 12 by (vm_compute; reflexivity). replace (12 - 1) with 11 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 12 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 11) with 4 by (vm_compute; reflexivity). replace (11 - 1) with 10 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 4 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 10) with 11 by (vm_compute; reflexivity). replace (10 - 1) with 9 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 11 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 9) with 5 by (vm_compute; reflexivity). replace (9 - 1) with 8 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 5 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 8) with 10 by (vm_compute; reflexivity). replace (8 - 1) with 7 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 10 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 7) with 6 by (vm_compute; reflexivity). replace (7 - 1) with 6 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 6 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 6) with 9 by (vm_compute; reflexivity). replace (6 - 1) with 5 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 9 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 5) with 7 by (vm_compute; reflexivity). replace (5 - 1) with 4 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 7 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 4) with 8 by (vm_compute; reflexivity). replace (4 - 1) with 3 by reflexivity.
  destruct (arr_get (ds_bl_tree_dl X) 8 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. cbn [Z.leb]. unfold Len, tree_dl. replace (arr_get bl_order_a 3) with 0 by (vm_compute; reflexivity).
  destruct (arr_get (ds_bl_tree_dl X) 0 =? 0); cbn [negb]; [|reflexivity].
  rewrite bblt_step. reflexivity.
Qed.

Lemma mbv_range : forall X, 2 <= mbv X <= 18.
Proof. intros X. unfold mbv. repeat (destruct (negb _); [lia|]). lia. Qed.

Lemma mprobe_last : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 -> 0 <= BLL X 0 < 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x1b43c : word) m s6_rom) (mkst R (0x1b448 : word) m s6_rom)
    /\ KR R /\ KR3 R /\ getr R 10 = zw (if negb (BLL X 0 =? 0) then 3 else 2)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK (P18 & P19 & P20) Hbufp Hv. open_fi HF. kd HK.
  assert (Ev : pb (ds_bl_tree_dl X) 0 = BLL X 0) by (apply pb_small; exact Hv).
  run mC 12%nat NoDirs [RVal (EApp1 4 (ELit 0))] (KPN ++ [(18, EVar 38); (19, EVar 39); (20, EAdd (EVar 32) (ELit 2047))]) [S; PB; 0; 0; 0; last; len; bufp; SP] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold KR3; regs_of HR Hfr|].
  split; [| fr_weak Hfr].
  let A := fresh "A" in symex_reg HR (10%bv : reg) as A; rewrite A; f_equal; nf; rewrite Ev.
  destruct (Z.eqb_spec (BLL X 0) 0) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - replace (BLL X 0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). vm_compute. reflexivity.
Qed.

Lemma mb_chain : forall regs m1 m X,
  FI m1 m X -> KR regs -> KR3 regs -> 0 <= bufp < 2 ^ 64 ->
  (forall k, 0 <= k < 39 -> 0 <= BLL X k < 65536) ->
  exists R,
    msteps s6_segs (mkst regs (0x1b34c : word) m s6_rom) (mkst R (0x1b448 : word) m s6_rom)
    /\ KR R /\ KR3 R /\ getr R 10 = zw (mbv X)
    /\ (forall r : reg, reg_in r [10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK HKt Hbufp Hty. unfold mbv.
  destruct (mprobe_18 regs m1 m X HF HK HKt Hbufp (Hty 15 ltac:(lia))) as (R0 & Hms0 & HK0 & HKt0 & HV0 & Hfr0).
  destruct (Z.eqb_spec (BLL X 15) 0) as [E0|E0]; cbn [negb].
  2:{ exists R0. split; [ exact Hms0|]. split; [exact HK0|]. split; [exact HKt0|]. split; [exact (HV0 E0)|]. exact Hfr0. }
  destruct (mprobe_17 R0 m1 m X HF HK0 HKt0 Hbufp (Hty 1 ltac:(lia))) as (R1 & Hms1 & HK1 & HKt1 & HV1 & Hfr1).
  destruct (Z.eqb_spec (BLL X 1) 0) as [E1|E1]; cbn [negb].
  2:{ exists R1. split; [eapply msteps_trans; [exact Hms0|]; exact Hms1|]. split; [exact HK1|]. split; [exact HKt1|]. split; [exact (HV1 E1)|]. intros r Hr. rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_16 R1 m1 m X HF HK1 HKt1 Hbufp (Hty 14 ltac:(lia))) as (R2 & Hms2 & HK2 & HKt2 & HV2 & Hfr2).
  destruct (Z.eqb_spec (BLL X 14) 0) as [E2|E2]; cbn [negb].
  2:{ exists R2. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; exact Hms2|]. split; [exact HK2|]. split; [exact HKt2|]. split; [exact (HV2 E2)|]. intros r Hr. rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_15 R2 m1 m X HF HK2 HKt2 Hbufp (Hty 2 ltac:(lia))) as (R3 & Hms3 & HK3 & HKt3 & HV3 & Hfr3).
  destruct (Z.eqb_spec (BLL X 2) 0) as [E3|E3]; cbn [negb].
  2:{ exists R3. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; exact Hms3|]. split; [exact HK3|]. split; [exact HKt3|]. split; [exact (HV3 E3)|]. intros r Hr. rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_14 R3 m1 m X HF HK3 HKt3 Hbufp (Hty 13 ltac:(lia))) as (R4 & Hms4 & HK4 & HKt4 & HV4 & Hfr4).
  destruct (Z.eqb_spec (BLL X 13) 0) as [E4|E4]; cbn [negb].
  2:{ exists R4. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; exact Hms4|]. split; [exact HK4|]. split; [exact HKt4|]. split; [exact (HV4 E4)|]. intros r Hr. rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_13 R4 m1 m X HF HK4 HKt4 Hbufp (Hty 3 ltac:(lia))) as (R5 & Hms5 & HK5 & HKt5 & HV5 & Hfr5).
  destruct (Z.eqb_spec (BLL X 3) 0) as [E5|E5]; cbn [negb].
  2:{ exists R5. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; exact Hms5|]. split; [exact HK5|]. split; [exact HKt5|]. split; [exact (HV5 E5)|]. intros r Hr. rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_12 R5 m1 m X HF HK5 HKt5 Hbufp (Hty 12 ltac:(lia))) as (R6 & Hms6 & HK6 & HKt6 & HV6 & Hfr6).
  destruct (Z.eqb_spec (BLL X 12) 0) as [E6|E6]; cbn [negb].
  2:{ exists R6. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; exact Hms6|]. split; [exact HK6|]. split; [exact HKt6|]. split; [exact (HV6 E6)|]. intros r Hr. rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_11 R6 m1 m X HF HK6 HKt6 Hbufp (Hty 4 ltac:(lia))) as (R7 & Hms7 & HK7 & HKt7 & HV7 & Hfr7).
  destruct (Z.eqb_spec (BLL X 4) 0) as [E7|E7]; cbn [negb].
  2:{ exists R7. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; exact Hms7|]. split; [exact HK7|]. split; [exact HKt7|]. split; [exact (HV7 E7)|]. intros r Hr. rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_10 R7 m1 m X HF HK7 HKt7 Hbufp (Hty 11 ltac:(lia))) as (R8 & Hms8 & HK8 & HKt8 & HV8 & Hfr8).
  destruct (Z.eqb_spec (BLL X 11) 0) as [E8|E8]; cbn [negb].
  2:{ exists R8. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; exact Hms8|]. split; [exact HK8|]. split; [exact HKt8|]. split; [exact (HV8 E8)|]. intros r Hr. rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_9 R8 m1 m X HF HK8 HKt8 Hbufp (Hty 5 ltac:(lia))) as (R9 & Hms9 & HK9 & HKt9 & HV9 & Hfr9).
  destruct (Z.eqb_spec (BLL X 5) 0) as [E9|E9]; cbn [negb].
  2:{ exists R9. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; exact Hms9|]. split; [exact HK9|]. split; [exact HKt9|]. split; [exact (HV9 E9)|]. intros r Hr. rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_8 R9 m1 m X HF HK9 HKt9 Hbufp (Hty 10 ltac:(lia))) as (R10 & Hms10 & HK10 & HKt10 & HV10 & Hfr10).
  destruct (Z.eqb_spec (BLL X 10) 0) as [E10|E10]; cbn [negb].
  2:{ exists R10. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; exact Hms10|]. split; [exact HK10|]. split; [exact HKt10|]. split; [exact (HV10 E10)|]. intros r Hr. rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_7 R10 m1 m X HF HK10 HKt10 Hbufp (Hty 6 ltac:(lia))) as (R11 & Hms11 & HK11 & HKt11 & HV11 & Hfr11).
  destruct (Z.eqb_spec (BLL X 6) 0) as [E11|E11]; cbn [negb].
  2:{ exists R11. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; exact Hms11|]. split; [exact HK11|]. split; [exact HKt11|]. split; [exact (HV11 E11)|]. intros r Hr. rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_6 R11 m1 m X HF HK11 HKt11 Hbufp (Hty 9 ltac:(lia))) as (R12 & Hms12 & HK12 & HKt12 & HV12 & Hfr12).
  destruct (Z.eqb_spec (BLL X 9) 0) as [E12|E12]; cbn [negb].
  2:{ exists R12. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; exact Hms12|]. split; [exact HK12|]. split; [exact HKt12|]. split; [exact (HV12 E12)|]. intros r Hr. rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_5 R12 m1 m X HF HK12 HKt12 Hbufp (Hty 7 ltac:(lia))) as (R13 & Hms13 & HK13 & HKt13 & HV13 & Hfr13).
  destruct (Z.eqb_spec (BLL X 7) 0) as [E13|E13]; cbn [negb].
  2:{ exists R13. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; exact Hms13|]. split; [exact HK13|]. split; [exact HKt13|]. split; [exact (HV13 E13)|]. intros r Hr. rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_4 R13 m1 m X HF HK13 HKt13 Hbufp (Hty 8 ltac:(lia))) as (R14 & Hms14 & HK14 & HKt14 & HV14 & Hfr14).
  destruct (Z.eqb_spec (BLL X 8) 0) as [E14|E14]; cbn [negb].
  2:{ exists R14. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; exact Hms14|]. split; [exact HK14|]. split; [exact HKt14|]. split; [exact (HV14 E14)|]. intros r Hr. rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr). }
  destruct (mprobe_last R14 m1 m X HF HK14 HKt14 Hbufp (Hty 0 ltac:(lia))) as (RL & HmsL & HKL & HKtL & HVL & HfrL).
  exists RL. split; [eapply msteps_trans; [exact Hms0|]; eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3|]; eapply msteps_trans; [exact Hms4|]; eapply msteps_trans; [exact Hms5|]; eapply msteps_trans; [exact Hms6|]; eapply msteps_trans; [exact Hms7|]; eapply msteps_trans; [exact Hms8|]; eapply msteps_trans; [exact Hms9|]; eapply msteps_trans; [exact Hms10|]; eapply msteps_trans; [exact Hms11|]; eapply msteps_trans; [exact Hms12|]; eapply msteps_trans; [exact Hms13|]; eapply msteps_trans; [exact Hms14|]; exact HmsL|]. split; [exact HKL|]. split; [exact HKtL|]. split; [exact HVL|]. intros r Hr. rewrite (HfrL r Hr). rewrite (Hfr14 r Hr). rewrite (Hfr13 r Hr). rewrite (Hfr12 r Hr). rewrite (Hfr11 r Hr). rewrite (Hfr10 r Hr). rewrite (Hfr9 r Hr). rewrite (Hfr8 r Hr). rewrite (Hfr7 r Hr). rewrite (Hfr6 r Hr). rewrite (Hfr5 r Hr). rewrite (Hfr4 r Hr). rewrite (Hfr3 r Hr). rewrite (Hfr2 r Hr). rewrite (Hfr1 r Hr). exact (Hfr0 r Hr).
Qed.
End Walk.
End FXG.
