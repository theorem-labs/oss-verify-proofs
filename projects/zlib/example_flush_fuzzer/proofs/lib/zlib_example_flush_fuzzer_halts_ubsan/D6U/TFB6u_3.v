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
  CompressBlk6u_1 CompressBlk6u_4 BuildTree6u_11 TrSmall6u TrStored6u ScanTree6u SendTree6u_1 SendTree6u_5 TFB6u_1 TFB6u_2.
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

Definition dC : cfg := CFG FBv [] [EVar 50%nat] [0x1c090; 0x1c0bc; 0x1c0ec; 0x1c0f0; 0x1c0f4; 0x1c1c0] [].


Definition dt2 (X : deflate_state) : bool :=
  negb (arr_get (ds_dyn_ltree_fc X) 9 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 10 =? 0) || negb (arr_get (ds_dyn_ltree_fc X) 13 =? 0).

Fixpoint anynz (X : deflate_state) (n : Z) (k : nat) : bool :=
  match k with
  | O => false
  | Datatypes.S k' => negb (arr_get (ds_dyn_ltree_fc X) n =? 0) || anynz X (n + 1) k'
  end.

Lemma detect_loop2_anynz : forall k X n, n + Z.of_nat k <= 256 ->
  detect_loop2 k X n = if anynz X n k then Some Z_TEXT else None.
Proof.
  induction k as [|k IH]; intros X n Hn; [reflexivity|].
  cbn [detect_loop2 anynz]. unfold Freq, tree_fc, LITERALS.
  replace (n <? 256) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (arr_get (ds_dyn_ltree_fc X) n =? 0); cbn [negb orb]; [|reflexivity].
  apply IH. lia.
Qed.

Lemma detect_loop1_binary : forall k X n bm r, detect_loop1 k X n bm = Some r -> r = Z_BINARY.
Proof.
  induction k as [|k IH]; intros X n bm r H; cbn [detect_loop1] in H; [discriminate|].
  destruct (n <=? 31); [|discriminate].
  destruct (negb (Z.land bm 1 =? 0) && negb (Freq X TL n =? 0)); [injection H; intros; subst; reflexivity|].
  exact (IH _ _ _ _ H).
Qed.

Definition DMASK : Z := 4093624447.

Lemma detect_data_type_eq : forall X,
  detect_data_type X =
    match detect_loop1 32 X 0 DMASK with
    | Some _ => Z_BINARY
    | None => if dt2 X then Z_TEXT else if anynz X 32 224 then Z_TEXT else Z_BINARY
    end.
Proof.
  intros X. unfold detect_data_type, DMASK, dt2. rewrite detect_loop2_anynz by (cbn; lia).
  destruct (detect_loop1 32 X 0 4093624447) as [r|] eqn:E.
  - rewrite (detect_loop1_binary _ _ _ _ _ E). reflexivity.
  - unfold Freq, tree_fc. destruct (anynz X 32 224); reflexivity.
Qed.

Lemma land1_mod2 : forall a, Z.land a 1 = a mod 2.
Proof. intros a. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shiftr1_div2 : forall a, Z.shiftr a 1 = a / 2.
Proof. intros a. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.


Lemma szwrap32_u64_is2 : forall dt, - 2 ^ 31 <= dt < 2 ^ 31 -> (szwrap 32 (dt mod 2 ^ 32) mod 2 ^ 64 = 2 <-> dt = 2).
Proof.
  intros dt Hdt. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 31) with 2147483648 in Hdt.
  change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  split; intros H; Z.to_euclidean_division_equations; lia.
Qed.

Definition DR (R : bvmap 5 word) : Prop :=
  getr R 10 = zw (p_strm p) /\ getr R 11 = zw (Z.lxor (S + 212) (-1)).
Definition DRP : list (Z * expr) := KPN ++ [(10, EVar 45); (11, EXor (EAdd (EVar 32) (ELit 212)) (ELit (-1)))].

Lemma d0_blk : forall regs m1 m X dt,
  FI m1 m X -> KR regs -> cell s6u_segs m (p_strm p + 88) 4 dt -> - 2 ^ 31 <= dt < 2 ^ 31 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c048 : word) m s6u_rom)
           (mkst R (if dt =? 2 then (0x1c090 : word) else (0x1c0f4 : word)) m s6u_rom)
    /\ KR R /\ getr R 10 = zw (p_strm p)
    /\ (dt = 2 -> DR R /\ getr R 12 = zw (S + 212) /\ getr R 13 = zw (4 * 0) /\ getr R 14 = zw DMASK /\ getr R 15 = zw 128)
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X dt HF HK Cdt0 Hdt. open_fi HF. kd HK. open_ubt HUB.
  pose proof (fbh_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & Hps0 & Hps1 & HFs & Hmst & HaS & HaP & Hasp). unfold TFB_FRAME6u, dsl_SIZE in HaS, HaP, Hasp.
  assert (Cdt : cell s6u_segs m (p_strm p + 88) 4 (dt mod 2 ^ 32)).
  { apply (SymAux.cell_mod s6u_segs m _ 4%nat dt); [exact Cdt0|]. cbn [Z.of_nat Z.mul Pos.mul]. rewrite Z.mod_mod by lia. reflexivity. }
  clear Cdt0.
  assert (Hdt' : 0 <= dt mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  pose proof (dsl_strm _ _ _ _ _ _ _ _ Hsc) as Cstrm. replace (S + 0) with S in Cstrm by lia.
  assert (MSt : forall x, p_strm p + 88 <= bv_unsigned x < p_strm p + 92 -> m x <> None) by (intros x Hx; apply HGR; apply Hmst; lia).
  remember (dt mod 2 ^ 32) as dt' eqn:Edt'. unfold DMASK.
  destruct (Z.eqb_spec dt 2) as [Cd|Cd].
  - run dC 16%nat [false; false; false] [RVal (EVar 45); RVal (EVar 46)] KPN [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; dt'] X.
    all: try (rewrite Edt'; apply (proj2 (szwrap32_u64_is2 dt Hdt)); exact Cd).
    all: match goal with |- ?g => idtac "D0A" g end.
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr|]. split; [intros _; unfold DR; regs_of HR Hfr | fr_weak Hfr].
  - run dC 16%nat [false; false; true] [RVal (EVar 45); RVal (EVar 46)] KPN [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; dt'] X.
    all: try (intros Hne2; apply Cd; rewrite Edt' in Hne2; exact (proj1 (szwrap32_u64_is2 dt Hdt) Hne2)).
    all: match goal with |- ?g => idtac "D0B" g end.
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [reg1 HR Hfr|]. split; [intros E; exfalso; exact (Cd E) | fr_weak Hfr].
  all: match goal with |- ?g => idtac "D0LEFT" g end.
Qed.


Local Ltac drd H := destruct H as (Q10 & Q11).
Definition MLP : list (Z * expr) := DRP ++ [(12, EAdd (EVar 32) (ELit 212)); (13, EShl (EVar 46) 2); (14, EVar 47); (15, ELit 128)].

Lemma mstep : forall regs m1 m X (n bm : Z),
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= n < 32 -> 0 <= bm < 2 ^ 32 -> 0 <= arr_get (ds_dyn_ltree_fc X) n < 65536 ->
  getr regs 12 = zw (S + 212) -> getr regs 13 = zw (4 * n) -> getr regs 14 = zw bm -> getr regs 15 = zw 128 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c090 : word) m s6u_rom)
           (mkst R (if negb (bm mod 2 =? 0) && negb (arr_get (ds_dyn_ltree_fc X) n =? 0) then (0x1c0f0 : word)
                    else if n + 1 =? 32 then (0x1c0bc : word) else (0x1c090 : word)) m s6u_rom)
    /\ KR R /\ DR R
    /\ (negb (bm mod 2 =? 0) && negb (arr_get (ds_dyn_ltree_fc X) n =? 0) = true -> getr R 15 = zw 0)
    /\ (negb (bm mod 2 =? 0) && negb (arr_get (ds_dyn_ltree_fc X) n =? 0) = false ->
        getr R 12 = zw (S + 212) /\ getr R 13 = zw (4 * (n + 1)) /\ getr R 14 = zw (bm / 2) /\ getr R 15 = zw 128)
    /\ (forall r : reg, reg_in r [13; 14; 15; 16]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X n bm HF HK HD Hstrm Hn Hbm Hv P12 P13 P14 P15. open_fi HF. kd HK. drd HD. open_ubt HUB.
  assert (Ev : pb (ds_dyn_ltree_fc X) n = arr_get (ds_dyn_ltree_fc X) n) by (apply pb_small; exact Hv).
  assert (Hm2 : 0 <= bm mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eqb_spec (bm mod 2) 0) as [Eb|Eb]; cbn [negb andb].
  -
    destruct (Z.eqb_spec (n + 1) 32) as [En|En].
    + run dC 20%nat [true; true] NoReads MLP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; n; bm] X.
      all: match goal with |- ?g => idtac "MSA1" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|].
      split; [intros; discriminate|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
    + run dC 20%nat [true; false] NoReads MLP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; n; bm] X.
      all: match goal with |- ?g => idtac "MSA2" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|].
      split; [intros; discriminate|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
  - destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) n) 0) as [Ez|Ez]; cbn [negb andb].
    +
      destruct (Z.eqb_spec (n + 1) 32) as [En|En].
      * run dC 20%nat [false; false; true; true] [RVal (EApp1 0 (EVar 46))] MLP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; n; bm] X.
        all: match goal with |- ?g => idtac "MSB1" g end.
        exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|].
        split; [intros; discriminate|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
      * run dC 20%nat [false; false; true; false] [RVal (EApp1 0 (EVar 46))] MLP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; n; bm] X.
        all: match goal with |- ?g => idtac "MSB2" g end.
        exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|].
        split; [intros; discriminate|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
    +
      run dC 20%nat [false; false; false] [RVal (EApp1 0 (EVar 46))] MLP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; n; bm] X.
      all: match goal with |- ?g => idtac "MSC" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|].
      split; [intros _; reg1 HR Hfr|]. split; [intros; discriminate | fr_weak Hfr].
  all: match goal with |- ?g => idtac "MSLEFT" g end.
Qed.

Lemma mloop : forall k (n : Z) regs m1 m X bm,
  n + Z.of_nat k = 32 -> (1 <= k)%nat -> 0 <= n ->
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 -> 0 <= bm < 2 ^ 32 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  getr regs 12 = zw (S + 212) -> getr regs 13 = zw (4 * n) -> getr regs 14 = zw bm -> getr regs 15 = zw 128 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c090 : word) m s6u_rom)
           (mkst R (match detect_loop1 k X n bm with Some _ => (0x1c0f0 : word) | None => (0x1c0bc : word) end) m s6u_rom)
    /\ KR R /\ DR R
    /\ (forall r, detect_loop1 k X n bm = Some r -> getr R 15 = zw 0)
    /\ (detect_loop1 k X n bm = None -> getr R 12 = zw (S + 212))
    /\ (forall r : reg, reg_in r [12; 13; 14; 15; 16]%bv = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros n regs m1 m X bm Hnk Hk Hn0 HF HK HD Hstrm Hbm Hty P12 P13 P14 P15; [lia|].
  assert (Hbm2 : 0 <= bm / 2 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (mstep regs m1 m X n bm HF HK HD Hstrm ltac:(lia) Hbm (Hty n ltac:(lia)) P12 P13 P14 P15)
    as (R1 & Hms1 & HK1 & HD1 & HZ1 & HC1 & Hfr1).
  cbn [detect_loop1]. replace (n <=? 31) with true by (symmetry; apply Z.leb_le; lia).
  unfold Freq, tree_fc. rewrite land1_mod2, shiftr1_div2.
  destruct (negb (bm mod 2 =? 0) && negb (arr_get (ds_dyn_ltree_fc X) n =? 0)) eqn:CC.
  - exists R1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HD1|].
    split; [intros _ _; exact (HZ1 eq_refl)|]. split; [intros; discriminate | fr_weak Hfr1].
  - destruct (HC1 eq_refl) as (Q12 & Q13 & Q14 & Q15).
    destruct k as [|k'].
    + replace (n + 1 =? 32) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia). cbn [detect_loop1].
      exists R1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HD1|].
      split; [intros; discriminate|]. split; [intros _; exact Q12 | fr_weak Hfr1].
    + replace (n + 1 =? 32) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
      destruct (IH (n + 1) R1 m1 m X (bm / 2) ltac:(lia) ltac:(lia) ltac:(lia) HF HK1 HD1 Hstrm Hbm2 Hty Q12 Q13 Q14 Q15)
        as (R2 & Hms2 & HK2 & HD2 & HZ2 & HC2 & Hfr2).
      exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HK2|]. split; [exact HD2|].
      split; [exact HZ2|]. split; [exact HC2|].
      intros r Hr. rewrite (Hfr2 r Hr). apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Lemma probes_blk : forall regs m1 m X,
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536) ->
  getr regs 12 = zw (S + 212) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c0bc : word) m s6u_rom)
           (mkst R (if dt2 X then (0x1c0ec : word) else (0x1c1c0 : word)) m s6u_rom)
    /\ KR R /\ DR R
    /\ (dt2 X = false -> getr R 12 = zw (S + 340 + 4 * 0) /\ getr R 13 = zw (224 - 0) /\ getr R 14 = zw (128 + 4 * 0))
    /\ (forall r : reg, reg_in r [12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK HD Hstrm Hty P12. open_fi HF. kd HK. drd HD. open_ubt HUB.
  pose proof (Hty 9 ltac:(lia)) as V9. pose proof (Hty 10 ltac:(lia)) as V10. pose proof (Hty 13 ltac:(lia)) as V13.
  assert (E9 : pb (ds_dyn_ltree_fc X) 9 = arr_get (ds_dyn_ltree_fc X) 9) by (apply pb_small; exact V9).
  assert (E10 : pb (ds_dyn_ltree_fc X) 10 = arr_get (ds_dyn_ltree_fc X) 10) by (apply pb_small; exact V10).
  assert (E13 : pb (ds_dyn_ltree_fc X) 13 = arr_get (ds_dyn_ltree_fc X) 13) by (apply pb_small; exact V13).
  unfold dt2.
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 9) 0) as [E9z|E9z]; cbn [negb orb].
  2:{ run dC 20%nat [false; true] [RVal (EApp1 0 (ELit 9))] (DRP ++ [(12, EAdd (EVar 32) (ELit 212))])
          [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X.
      all: match goal with |- ?g => idtac "PB9" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros; discriminate | fr_weak Hfr]. }
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 10) 0) as [E10z|E10z]; cbn [negb orb].
  2:{ run dC 20%nat [false; false; false; true] [RVal (EApp1 0 (ELit 9)); RVal (EApp1 0 (ELit 10))] (DRP ++ [(12, EAdd (EVar 32) (ELit 212))])
          [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X.
      all: match goal with |- ?g => idtac "PB10" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros; discriminate | fr_weak Hfr]. }
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) 13) 0) as [E13z|E13z]; cbn [negb orb].
  2:{ run dC 24%nat [false; false; false; false; false; false] [RVal (EApp1 0 (ELit 9)); RVal (EApp1 0 (ELit 10)); RVal (EApp1 0 (ELit 13))]
          (DRP ++ [(12, EAdd (EVar 32) (ELit 212))]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X.
      all: match goal with |- ?g => idtac "PB13" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros; discriminate | fr_weak Hfr]. }
  run dC 28%nat [false; false; false; false; false; true] [RVal (EApp1 0 (ELit 9)); RVal (EApp1 0 (ELit 10)); RVal (EApp1 0 (ELit 13))]
      (DRP ++ [(12, EAdd (EVar 32) (ELit 212))]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X.
  all: match goal with |- ?g => idtac "PB0" g end.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
  all: match goal with |- ?g => idtac "PBLEFT" g end.
Qed.


Definition SLP : list (Z * expr) :=
  DRP ++ [(12, EAdd (EAdd (EVar 32) (ELit 340)) (EShl (EVar 46) 2)); (13, ESub (ELit 224) (EVar 46)); (14, EAdd (ELit 128) (EShl (EVar 46) 2))].

Lemma dstep : forall regs m1 m X (i : Z),
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 ->
  0 <= i < 224 -> 0 <= arr_get (ds_dyn_ltree_fc X) (32 + i) < 65536 ->
  getr regs 12 = zw (S + 340 + 4 * i) -> getr regs 13 = zw (224 - i) -> getr regs 14 = zw (128 + 4 * i) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c1c0 : word) m s6u_rom)
           (mkst R (if negb (arr_get (ds_dyn_ltree_fc X) (32 + i) =? 0) then (0x1c0ec : word)
                    else if i + 1 =? 224 then (0x1c0f0 : word) else (0x1c1c0 : word)) m s6u_rom)
    /\ KR R /\ DR R
    /\ (arr_get (ds_dyn_ltree_fc X) (32 + i) = 0 ->
        getr R 15 = zw 0 /\ getr R 12 = zw (S + 340 + 4 * (i + 1)) /\ getr R 13 = zw (224 - (i + 1)) /\ getr R 14 = zw (128 + 4 * (i + 1)))
    /\ (forall r : reg, reg_in r [12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X i HF HK HD Hstrm Hi Hv P12 P13 P14. open_fi HF. kd HK. drd HD. open_ubt HUB.
  assert (Ev : pb (ds_dyn_ltree_fc X) (32 + i) = arr_get (ds_dyn_ltree_fc X) (32 + i)) by (apply pb_small; exact Hv).
  destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) (32 + i)) 0) as [E|E]; cbn [negb].
  - destruct (Z.eqb_spec (i + 1) 224) as [Ei|Ei].
    + run dC 20%nat [false; false; false] [RVal (EApp1 0 (EAdd (ELit 32) (EVar 46)))] SLP
          [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; i] X.
      all: match goal with |- ?g => idtac "DS1" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
    + run dC 20%nat [false; false; true] [RVal (EApp1 0 (EAdd (ELit 32) (EVar 46)))] SLP
          [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; i] X.
      all: match goal with |- ?g => idtac "DS2" g end.
      exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros _; regs_of HR Hfr | fr_weak Hfr].
  - run dC 20%nat [false; true] [RVal (EApp1 0 (EAdd (ELit 32) (EVar 46)))] SLP
        [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; i] X.
    all: match goal with |- ?g => idtac "DS3" g end.
    exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [intros E'; exfalso; exact (E E') | fr_weak Hfr].
  all: match goal with |- ?g => idtac "DSLEFT" g end.
Qed.

Lemma dloop : forall k (i : Z) regs m1 m X,
  i + Z.of_nat k = 224 -> (1 <= k)%nat -> 0 <= i ->
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 ->
  (forall n, 0 <= n < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) n < 65536) ->
  getr regs 12 = zw (S + 340 + 4 * i) -> getr regs 13 = zw (224 - i) -> getr regs 14 = zw (128 + 4 * i) ->
  exists R,
    msteps s6u_segs (mkst regs (0x1c1c0 : word) m s6u_rom)
           (mkst R (if anynz X (32 + i) k then (0x1c0ec : word) else (0x1c0f0 : word)) m s6u_rom)
    /\ KR R /\ DR R
    /\ (anynz X (32 + i) k = false -> getr R 15 = zw 0)
    /\ (forall r : reg, reg_in r [12; 13; 14; 15]%bv = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros i regs m1 m X Hik Hk Hi0 HF HK HD Hstrm Hty P12 P13 P14; [lia|].
  destruct (dstep regs m1 m X i HF HK HD Hstrm ltac:(lia) (Hty (32 + i) ltac:(lia)) P12 P13 P14) as (R1 & Hms1 & HK1 & HD1 & HZ1 & Hfr1).
  cbn [anynz]. destruct (Z.eqb_spec (arr_get (ds_dyn_ltree_fc X) (32 + i)) 0) as [E|E]; cbn [negb orb] in Hms1 |- *.
  - destruct (HZ1 E) as (Q15 & Q12 & Q13 & Q14).
    destruct k as [|k'].
    + replace (i + 1 =? 224) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia). cbn [anynz].
      exists R1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HD1|]. split; [intros _; exact Q15 | exact Hfr1].
    + replace (i + 1 =? 224) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
      destruct (IH (i + 1) R1 m1 m X ltac:(lia) ltac:(lia) ltac:(lia) HF HK1 HD1 Hstrm Hty Q12 Q13 Q14) as (R2 & Hms2 & HK2 & HD2 & HZ2 & Hfr2).
      replace (32 + (i + 1)) with (32 + i + 1) in Hms2, HZ2 by lia.
      exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HK2|]. split; [exact HD2|].
      split; [exact HZ2|]. intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - exists R1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HD1|]. split; [intros X0; discriminate | exact Hfr1].
Qed.


Lemma BR_set_strm : forall m X c, BRm m X -> BRm m (set_strm X c).
Proof. intros m X c H. destruct X. exact H. Qed.


Definition DPOST (m : word -> option byte) (X : deflate_state) (v : Z) (R : bvmap 5 word) (regs : bvmap 5 word) (m' : word -> option byte) : Prop :=
  FI m' m' (set_strm X (cset_data_type (ds_strm X) v))
  /\ (forall a w v0, cell s6u_segs m a w v0 -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v0)
  /\ cell s6u_segs m' (p_strm p + 88) 4 v
  /\ KR R
  /\ (forall r : reg, reg_in r [15]%bv = false -> getr R r = getr regs r).

Lemma dstore_fin : forall m1 m X v R regs,
  FI m1 m X -> 0 <= v < 2 ^ 32 -> KR R ->
  (forall r : reg, reg_in r [15]%bv = false -> getr R r = getr regs r) ->
  DPOST m X v R regs (wbytes m (zw (p_strm p + 88)) (Z_to_le_bytes 4 v)).
Proof.
  intros m1 m X v R regs HF Hv HK Hfr. open_fi HF.
  pose proof (fbh_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & Hps0 & Hps1 & HFs & Hmst & HaS & HaP & Hasp). unfold TFB_FRAME6u, dsl_SIZE in HaS, HaP, Hasp.
  unfold DPOST. split.
  - split.
    { apply BR_set_strm. apply (BR_st_other _ _ _ _ F mem0 S p PBL HLb); [exact HB | lia | rewrite length_Z_to_le_bytes; cbn; lia
        | rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; exact HFs]. }
    split.
    { apply (trees_rod_clear_wr R6u _ _ HRC). apply wr_ok_wbytes; [apply wr_ok_refl | | lia | rewrite length_Z_to_le_bytes; cbn; lia].
      intros x Hx. rewrite length_Z_to_le_bytes in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply HGR. apply Hmst. lia. }
    split; [apply agree_out_refl|].
    split; [intros x Hx; apply wbytes_grows; apply MF; exact Hx|].
    intros x Hx. apply wbytes_grows. apply HGR. exact Hx.
  - split.
    { intros a w v0 Hc Ha1 Ha2. apply cell_write_other; [exact Hc | lia | cbn; lia | lia | |];
        rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia. }
    split; [apply cell_write_same; [lia | cbn; lia]|].
    split; [exact HK | exact Hfr].
Qed.

Lemma d_li1 : forall regs m1 m X,
  FI m1 m X -> KR regs -> DR regs -> 0 <= p_strm p < 2 ^ 64 ->
  exists R, msteps s6u_segs (mkst regs (0x1c0ec : word) m s6u_rom) (mkst R (0x1c0f0 : word) m s6u_rom)
    /\ KR R /\ DR R /\ getr R 15 = zw 1
    /\ (forall r : reg, reg_in r [15]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK HD Hstrm. open_fi HF. kd HK. drd HD.
  run dC 8%nat NoDirs NoReads DRP [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p] X.
  exists R. split; [exact Hms|]. split; [kregs HR Hfr|]. split; [unfold DR; regs_of HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma dstore : forall regs m1 m X v,
  FI m1 m X -> KR regs -> DR regs -> getr regs 15 = zw v -> 0 <= v < 2 ->
  exists R m', msteps s6u_segs (mkst regs (0x1c0f0 : word) m s6u_rom) (mkst R (0x1c0f4 : word) m' s6u_rom) /\ DPOST m X v R regs m'.
Proof.
  intros regs m1 m X v HF HK HD P15 Hv. pose proof HF as HF0. open_fi HF. kd HK. drd HD. open_ubt HUB.
  pose proof (fbh_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & Hps0 & Hps1 & HFs & Hmst & HaS & HaP & Hasp). unfold TFB_FRAME6u, dsl_SIZE in HaS, HaP, Hasp.
  assert (MSt : forall x, p_strm p + 88 <= bv_unsigned x < p_strm p + 92 -> m x <> None) by (intros x Hx; apply HGR; apply Hmst; lia).
  run dC 8%nat NoDirs NoReads (DRP ++ [(15, EVar 46)]) [S; PB; 0; 0; 0; last; 0; 0; SP; 0; 0; 0; 0; p_strm p; v] X.
  all: match goal with |- ?g => idtac "DSTORE" g end.
  exists R, (wbytes m (zw (p_strm p + 88)) (Z_to_le_bytes 4 v)). split; [exact Hms|].
  apply (dstore_fin m1 m X v R regs HF0 ltac:(lia)); [kregs HR Hfr | fr_weak Hfr].
Qed.


Definition dt_st (X : deflate_state) : deflate_state :=
  if cs_data_type (ds_strm X) =? 2 then set_strm X (cset_data_type (ds_strm X) (detect_data_type X)) else X.

Lemma dt_st_data_type : forall X,
  cs_data_type (ds_strm (dt_st X)) = (if cs_data_type (ds_strm X) =? 2 then detect_data_type X else cs_data_type (ds_strm X)).
Proof. intros X. unfold dt_st. destruct (_ =? 2); [|reflexivity]. destruct X as [st]; cbn. destruct st; reflexivity. Qed.

Local Ltac frw a Hr := rewrite (a _) by (eapply reg_in_sub; [|exact Hr]; reflexivity).

Lemma dt_phase : forall regs m1 m X,
  FI m1 m X -> KR regs ->
  cell s6u_segs m (p_strm p + 88) 4 (cs_data_type (ds_strm X)) -> - 2 ^ 31 <= cs_data_type (ds_strm X) < 2 ^ 31 ->
  (cs_data_type (ds_strm X) = 2 -> forall k, 0 <= k < 573 -> 0 <= arr_get (ds_dyn_ltree_fc X) k < 65536) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1c048 : word) m s6u_rom) (mkst R (0x1c0f4 : word) m' s6u_rom)
    /\ FI m' m' (dt_st X)
    /\ (forall a w v, cell s6u_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6u_segs m' a w v)
    /\ cell s6u_segs m' (p_strm p + 88) 4 (cs_data_type (ds_strm (dt_st X)))
    /\ KR R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14; 15; 16]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HF HK Cdt Hdt Hty.
  pose proof (fbh_strm _ _ _ _ _ _ _ _ _ _ _ _ _ HH) as (_ & Hps0 & Hps1 & _).
  assert (Hstrm : 0 <= p_strm p < 2 ^ 64) by lia.
  rewrite dt_st_data_type. unfold dt_st.
  destruct (d0_blk regs m1 m X _ HF HK Cdt Hdt) as (R0 & Hms0 & HK0 & HQ10 & HS0 & Hfr0).
  destruct (Z.eqb_spec (cs_data_type (ds_strm X)) 2) as [Cd|Cd].
  2:{ exists R0, m. split; [exact Hms0|]. split; [exact (FI_self _ _ _ _ _ _ _ m1 m X HF)|].
      split; [intros; assumption|]. split; [exact Cdt|]. split; [exact HK0|]. fr_weak Hfr0. }
  specialize (Hty Cd). destruct (HS0 Cd) as (HD0 & Q12 & Q13 & Q14 & Q15). rewrite detect_data_type_eq.
  destruct (mloop 32%nat 0 R0 m1 m X DMASK ltac:(lia) ltac:(lia) ltac:(lia) HF HK0 HD0 Hstrm ltac:(unfold DMASK; lia) Hty Q12 Q13 Q14 Q15)
    as (R1 & Hms1 & HK1 & HD1 & HZ1 & HC1 & Hfr1).
  destruct (detect_loop1 32 X 0 DMASK) as [r|].
  -
    destruct (dstore R1 m1 m X 0 HF HK1 HD1 (HZ1 r eq_refl) ltac:(lia)) as (R2 & m2 & Hms2 & (HF2 & HC2 & Cd2 & HK2 & Hfr2)).
    exists R2, m2. split.
    { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1 | exact Hms2]. }
    split; [exact HF2|]. split; [exact HC2|]. split; [exact Cd2|]. split; [exact HK2|].
    intros r' Hr. frw Hfr2 Hr. frw Hfr1 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
  - destruct (probes_blk R1 m1 m X HF HK1 HD1 Hstrm Hty (HC1 eq_refl)) as (R2 & Hms2 & HK2 & HD2 & HS2 & Hfr2).
    destruct (dt2 X).
    + destruct (d_li1 R2 m1 m X HF HK2 HD2 Hstrm) as (R3 & Hms3 & HK3 & HD3 & Z3 & Hfr3).
      destruct (dstore R3 m1 m X 1 HF HK3 HD3 Z3 ltac:(lia)) as (R4 & m4 & Hms4 & (HF4 & HC4 & Cd4 & HK4 & Hfr4)).
      exists R4, m4. split.
      { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
        eapply msteps_trans; [exact Hms3 | exact Hms4]. }
      split; [exact HF4|]. split; [exact HC4|]. split; [exact Cd4|]. split; [exact HK4|].
      intros r' Hr. frw Hfr4 Hr. frw Hfr3 Hr. frw Hfr2 Hr. frw Hfr1 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
    + destruct (HS2 eq_refl) as (P12 & P13 & P14).
      destruct (dloop 224%nat 0 R2 m1 m X ltac:(lia) ltac:(lia) ltac:(lia) HF HK2 HD2 Hstrm Hty P12 P13 P14) as (R3 & Hms3 & HK3 & HD3 & Z3 & Hfr3).
      replace (32 + 0) with 32 in Hms3, Z3 by lia.
      destruct (anynz X 32 224).
      * destruct (d_li1 R3 m1 m X HF HK3 HD3 Hstrm) as (R4 & Hms4 & HK4 & HD4 & Z4 & Hfr4).
        destruct (dstore R4 m1 m X 1 HF HK4 HD4 Z4 ltac:(lia)) as (R5 & m5 & Hms5 & (HF5 & HC5 & Cd5 & HK5 & Hfr5)).
        exists R5, m5. split.
        { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
          eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
        split; [exact HF5|]. split; [exact HC5|]. split; [exact Cd5|]. split; [exact HK5|].
        intros r' Hr. frw Hfr5 Hr. frw Hfr4 Hr. frw Hfr3 Hr. frw Hfr2 Hr. frw Hfr1 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
      * destruct (dstore R3 m1 m X 0 HF HK3 HD3 (Z3 eq_refl) ltac:(lia)) as (R4 & m4 & Hms4 & (HF4 & HC4 & Cd4 & HK4 & Hfr4)).
        exists R4, m4. split.
        { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
          eapply msteps_trans; [exact Hms3 | exact Hms4]. }
        split; [exact HF4|]. split; [exact HC4|]. split; [exact Cd4|]. split; [exact HK4|].
        intros r' Hr. frw Hfr4 Hr. frw Hfr3 Hr. frw Hfr2 Hr. frw Hfr1 Hr. apply Hfr0. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
End Walk.
End FXG.
