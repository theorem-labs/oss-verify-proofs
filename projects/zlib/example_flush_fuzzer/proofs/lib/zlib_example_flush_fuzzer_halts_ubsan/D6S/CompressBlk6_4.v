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
  RomRead TreesRod BitsLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab CompressModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6 CompressBlk6_1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import BuildTreeLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import CompressBlk6_2 CompressBlk6_3.
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
Variables (LT DT : Z) (lfc ldl dfc ddl : arr).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation LB := (ds_lit_bufsize ds).
Local Abbreviation sn := (ds_sym_next ds).
Local Abbreviation SP := (sp - 48).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).

Hypothesis HH : CBH F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl.

Let Hret : ret_ok ra := cbh_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := cbh_L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 48 := cbh_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := cbh_br _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6 mem := cbh_rod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hok : compress_block_ok PBL ds lfc ldl dfc ddl := cbh_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HT := cbh_T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLT : 0 <= LT /\ LT + 1144 <= 2 ^ 63 := cbh_LT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HDT : 0 <= DT /\ DT + 120 <= 2 ^ 63 := cbh_DT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsn : 0 <= sn /\ sn + 3 < 2 ^ 31 := cbh_sn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HLBr : 0 <= LB < 2 ^ 32 := cbh_LB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let HPBL : 0 < PBL := cbh_PBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 48 <= sp <= 2 ^ 63 := proj1 Hcf.

Local Abbreviation PURE := (CompressBlk6_1.PURE PBL ds).
Local Abbreviation GI := (CompressBlk6_1.GI S p PBL).
Local Abbreviation CI := (CompressBlk6_1.CI F mem0 S p PBL ds).
Local Abbreviation KREGS := (CompressBlk6_1.KREGS S sp LT DT).
Local Abbreviation cbF := (CompressBlk6_1.cbF lfc ldl dfc ddl).
Local Abbreviation PURE_send := (CompressBlk6_1.PURE_send F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation lit_site := (CompressBlk6_1.lit_site F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation lt_blk := (CompressBlk6_1.lt_blk F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation head_blk := (CompressBlk6_1.head_blk F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation lcode_site := (CompressBlk6_2.lcode_site F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation lx_site := (CompressBlk6_2.lx_site F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation dd_blk := (CompressBlk6_3.dd_blk F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation dcode_site := (CompressBlk6_3.dcode_site F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).
Local Abbreviation dextra_site := (CompressBlk6_3.dextra_site F mem0 mem S p PBL ds ra sp LT DT lfc ldl dfc ddl HH).



Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [CompressBlk6_1.cbF].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; cb_read
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; tab_range ].

Local Ltac run fuel dirs rds pins pv A :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs cbC fuel dirs rdv pinsv vbv NoRegions pv NoVals (cbF A) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Local Ltac run_dbg fuel dirs rds pins pv :=
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex_dbg s6_segs cbC fuel dirs rdv pinsv vbv NoRegions pv (mkst regs pc m s6_rom)
  end.

Local Ltac open_br HB HRC HP :=
  let P1 := fresh "Ppb" in let P2 := fresh "Pbinv" in let P3 := fresh "Pfc" in let P4 := fresh "Pdl" in
  let P5 := fresh "PLB" in let P6 := fresh "Psn" in let P7 := fresh "Plen" in
  pose proof HP as HP'; destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7); unfold PBB in P1;
  let Hbv := fresh "Hbv" in let Hbb := fresh "Hbb" in let Hpd := fresh "Hpd" in
  pose proof P2 as HBI'; destruct HBI' as (Hbv & Hbb & Hpd);
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & _ & _ & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let Csn := fresh "Csn" in let Csb := fresh "Csb" in
  pose proof (dsl_sym_next _ _ _ _ _ _ _ _ Hsc) as Csn; pose proof (dsl_sym_buf _ _ _ _ _ _ _ _ Hsc) as Csb;
  dsred in Csn; dsred in Csb; try rewrite P6 in Csn; try rewrite P5 in Csb; clear Hsc;
  let C40 := fresh "C40" in let C16 := fresh "C16" in let C5936 := fresh "C5936" in let C5940 := fresh "C5940" in
  let Cpb := fresh "Cpb" in
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB) as (C40 & C16 & C5936 & C5940 & Cpb); dsred in C40; dsred in C5936; dsred in C5940; dsred in Cpb;
  let TL1 := fresh "TL1" in let TL2 := fresh "TL2" in let TD1 := fresh "TD1" in let TD2 := fresh "TD2" in
  destruct (HT _ _ HB P3 P4 HRC) as (TL1 & TL2 & TD1 & TD2);
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let HLT' := fresh "HLT'" in pose proof HLT as HLT';
  let HDT' := fresh "HDT'" in pose proof HDT as HDT';
  let RODS := fresh "RODS" in let RODP := fresh "RODP" in
  pose proof (proj1 (mapped_rod_apart R6 _ _ S 5968 trod_ok6 HRC MS ltac:(lia) ltac:(lia))) as RODS;
  pose proof (proj1 (mapped_rod_apart R6 _ _ (p_pending_buf p) PBL trod_ok6 HRC MP ltac:(lia) ltac:(lia))) as RODP;
  cbn [tr_lo tr_hi R6] in RODS, RODP;
  let Tlc := fresh "Tlc" in let Tdc := fresh "Tdc" in let Txl := fresh "Txl" in let Tbl := fresh "Tbl" in
  let Txd := fresh "Txd" in let Tbd := fresh "Tbd" in
  pose proof (length_code_cells R6 _ _ trod_ok6 HRC) as Tlc; pose proof (dist_code_cells R6 _ _ trod_ok6 HRC) as Tdc;
  pose proof (extra_lbits_cells R6 _ _ trod_ok6 HRC) as Txl; pose proof (base_length_cells R6 _ _ trod_ok6 HRC) as Tbl;
  pose proof (extra_dbits_cells R6 _ _ trod_ok6 HRC) as Txd; pose proof (base_dist_cells R6 _ _ trod_ok6 HRC) as Tbd;
  cbn [tr_length_code tr_dist_code tr_extra_lbits tr_base_length tr_extra_dbits tr_base_dist R6] in Tlc, Tdc, Txl, Tbl, Txd, Tbd.

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
            | rewrite ?length_Z_to_le_bytes; unfold GI;
              first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac kregs HR Hfr :=
  unfold KREGS; repeat split;
  lazymatch goal with |- getr ?R ?r = _ =>
    first [ rewrite (Hfr r eq_refl); assumption
          | let A := fresh "A" in symex_reg HR r as A; rewrite A;
            first [ reflexivity | f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b =>
                      lazymatch isZcst a with true => lazymatch isZcst b with true =>
                        apply bv_eq; vm_compute; reflexivity end end end ] ]
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [reflexivity | f_equal; lia | f_equal; f_equal; lia | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption ] end
        | idtac ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac vcongr := first [ reflexivity | apply pb_mod16 | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite szwrap32_mod16, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vwrap := first [ reflexivity | apply pb_wrap16 | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vrange := first [ apply pb_range | lia | apply Z.mod_pos_bound; lia ].
Local Ltac rbm := first [ assumption | apply szwrap16_mod; assumption | apply szwrap16_mod; lia ].

Local Ltac st_flush vnorm :=
  rewrite send_bits_flush_eq by (unfold Buf_size; lia); st_eq;
  [ vnorm; f_equal;
    [ f_equal; [lia | apply byte0_eq; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr]]
    | lia
    | apply byte1_eq2; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr] ]
  | lia
  | first [reflexivity | vnorm; apply srl_eq'; [vrange | vwrap | lia]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); unfold Buf_size; lia] ].
Local Ltac rb_flush r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
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
  | first [reflexivity | vnorm; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr]]
  | first [reflexivity | vnorm; repeat (rewrite (szwrap_small 32) by lia); lia] ].
Local Ltac rb_keep r HR vnorm :=
  unfold RBr; let A := fresh "A" in symex_reg HR r as A; rewrite A, u_zw, mod_pow2_mod_pow2 by lia;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_buf;
  vnorm; unfold sb_nb; eapply nb_eqm2; [lia | rbm | vnorm; vcongr].
Local Ltac bv_keep r HR vnorm :=
  let A := fresh "A" in symex_reg HR r as A; rewrite A; f_equal;
  rewrite send_bits_keep_eq by (unfold Buf_size; lia); rewrite upd4_bi_valid;
  vnorm; repeat (rewrite (szwrap_small 32) by lia); lia.
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac site_fin Hms HR Hfr HB HRC HP HAG MS MP tst tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HB M;
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [eapply BR_eqst; [exact HB2|]; clear HB2; tst
                        | split; [ apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP
                                 | split; [pure_fin HP | ag_tower HAG] ] ]
                 | tregs ]
      end
  end.


Local Ltac oth HFf :=
  rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul];
  first [ lia | unfold dsl_SIZE in *; lia | eapply sub_franges_mono; [exact HFf | lia | lia] ].

Local Ltac br_fwdF HB M HFf :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      br_fwdF HB M1 HFf;
      lazymatch goal with
      | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 ?s1, HL : BRH ?F ?S ?p ?PBL |- _ =>
          let H2 := fresh "HBR" in
          pose proof (BR_st_other sg AL AD AB F mem0 S p PBL HL M1 s1 a bs H1) as H2;
          specialize (H2 ltac:(oth HFf) ltac:(oth HFf) ltac:(oth HFf) ltac:(oth HFf) ltac:(oth HFf)); clear H1
      end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Definition FRM (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6_segs m (SP + 40) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6_segs m (SP + 32) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6_segs m (SP + 24) 8 (bv_unsigned (getr regs0 18))
  /\ cell s6_segs m (SP + 16) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6_segs m (SP + 8) 8 (bv_unsigned (getr regs0 20))
  /\ cell s6_segs m SP 8 (bv_unsigned (getr regs0 21)).

Lemma frame_cell_keep : forall m1 m2 a v,
  agree_out GI m1 m2 -> cell s6_segs m1 a 8 v -> SP <= a -> a + 8 <= sp ->
  cell s6_segs m2 a 8 v.
Proof.
  intros m1 m2 a v Hag Hc Ha1 Ha2.
  pose proof Hcf as (Hsp0 & _ & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HLb as (HS' & HPB' & _). unfold dsl_SIZE in HS'.
  apply (cell_agree_out s6_segs GI m1 m2 a 8 v Hag); [| lia | cbn; lia | exact Hc].
  unfold CompressBlk6_1.GI. apply disj_franges_cons; [cbn; lia|]. apply disj_franges_cons; [cbn; lia|]. apply disj_franges_nil.
Qed.

Lemma FRM_keep : forall m1 m2 regs0, agree_out GI m1 m2 -> FRM m1 regs0 -> FRM m2 regs0.
Proof.
  intros m1 m2 regs0 Hag (C1 & C2 & C3 & C4 & C5 & C6). pose proof (proj1 Hcf) as Hsp0. unfold FRM.
  repeat split; (eapply frame_cell_keep; [exact Hag | eassumption | lia | lia]).
Qed.


Definition END_CH : list reg := [2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%bv.

Lemma end_blk : forall regs m1 m s regs0,
  CI m1 m s -> FRM m regs0 -> sb_room PBL s (arr_get ldl 256) -> 0 <= arr_get ldl 256 <= 15 ->
  getr regs 10 = zw S -> getr regs 13 = zw (S + 5888) -> getr regs 11 = zw LT -> getr regs 2 = zw SP ->
  getr regs 1 = ra -> getr regs 28 = zw (ds_bi_valid s) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c660 : word) m s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (send_bits s (arr_get lfc 256) (arr_get ldl 256))
    /\ trees_rod_clear6 m'
    /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9 /\ getr R 18 = getr regs0 18
    /\ getr R 19 = getr regs0 19 /\ getr R 20 = getr regs0 20 /\ getr R 21 = getr regs0 21
    /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r END_CH = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m s regs0 (HB & HRC & HP & HAG) (F8 & F9 & F18 & F19 & F20 & F21) Hroom Vdl P10 P13 P11 P2 P1 P28.
  open_br HB HRC HP.
  assert (Edl : pb ldl 256 = arr_get ldl 256) by (apply pb_small; lia).
  pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof (u64_range (getr regs0 20)) as U20. pose proof (u64_range (getr regs0 21)) as U21.
  pose proof Hret as Hret'. pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - arr_get ldl 256) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - run 80%nat [false]
        [RVal (EApp1 2 (ELit 256)); RVal (EApp1 1 (ELit 256)); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33); RVal (EVar 36);
         RVal (EVar 48); RVal (EVar 49); RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53)]
        [(10, EVar 32); (13, EAdd (EVar 32) (ELit 5888)); (11, EVar 37); (2, EVar 44); (28, EVar 36)]
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; 0; sn; 0; SP; 0; 0; ds_bi_buf s;
         bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
         bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21)] (ds_pending_buf s).
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        br_fwd HB M;
        lazymatch goal with
        | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
            exists R, M; split; [rewrite P1 in Hms; exact Hms|]; clear Hms;
            split; [eapply BR_eqst; [exact HB2|]; clear HB2; st_flush nf|];
            split; [apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP|]
        end
    end.
    regs_of HR Hfr.
  - run 80%nat [true]
        [RVal (EApp1 2 (ELit 256)); RVal (EApp1 1 (ELit 256)); RVal (EVar 47);
         RVal (EVar 48); RVal (EVar 49); RVal (EVar 50); RVal (EVar 51); RVal (EVar 52); RVal (EVar 53)]
        [(10, EVar 32); (13, EAdd (EVar 32) (ELit 5888)); (11, EVar 37); (2, EVar 44); (28, EVar 36)]
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; 0; 0; 0; sn; 0; SP; 0; 0; ds_bi_buf s;
         bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
         bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21)] (ds_pending_buf s).
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        br_fwd HB M;
        lazymatch goal with
        | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
            exists R, M; split; [rewrite P1 in Hms; exact Hms|]; clear Hms;
            split; [eapply BR_eqst; [exact HB2|]; clear HB2; st_keep nf|];
            split; [apply (trees_rod_clear_wr R6 _ _ HRC); wr_tower MS MP|]
        end
    end.
    regs_of HR Hfr.
Qed.



Lemma PURE0 : PURE ds.
Proof.
  destruct Hok as (HBI & HPB & _).
  destruct HBR0 as (_ & _ & _ & _ & Hlen & _).
  unfold CompressBlk6_1.PURE. split; [exact HPB|]. split; [exact HBI|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. exact Hlen.
Qed.

Local Ltac wr_towerF MS MP MF :=
  repeat (apply wr_ok_wbytes;
          [ | let x := fresh "x" in let Hx := fresh "Hx" in
              intros x Hx; rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
              first [ apply MS; lia | apply MP; lia | apply MF; lia ]
            | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]);
  apply wr_ok_refl.

Definition PRO_CH : list reg := [2; 5; 6; 7; 13; 14; 15; 16; 17; 28]%bv.

Lemma pro_blk : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw LT -> getr regs 12 = zw DT -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m1,
    msteps s6_segs (mkst regs (0x1c2a8 : word) mem s6_rom)
           (mkst R (if sn =? 0 then (0x1c660 : word) else (0x1c314 : word)) m1 s6_rom)
    /\ CI m1 m1 ds /\ FRM m1 regs
    /\ (sn <> 0 -> KREGS R /\ getr R 14 = zw 0)
    /\ (sn = 0 -> getr R 13 = zw (S + 5888) /\ getr R 28 = zw (ds_bi_valid ds))
    /\ getr R 10 = zw S /\ getr R 11 = zw LT /\ getr R 2 = zw SP /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r PRO_CH = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1.
  pose proof PURE0 as HP0. pose proof HBR0 as HB. pose proof HRC0 as HRC.
  open_br HB HRC HP0.
  pose proof Hcf as (_ & HFf & MF & HfS & HfP). unfold dsl_SIZE in HfS. unfold mapped in MF.
  pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19.
  pose proof (u64_range (getr regs 20)) as U20. pose proof (u64_range (getr regs 21)) as U21.
  assert (P8 : getr regs 8 = zw (bv_unsigned (getr regs 8))) by (symmetry; apply zw_u).
  assert (P9 : getr regs 9 = zw (bv_unsigned (getr regs 9))) by (symmetry; apply zw_u).
  assert (P18 : getr regs 18 = zw (bv_unsigned (getr regs 18))) by (symmetry; apply zw_u).
  assert (P19 : getr regs 19 = zw (bv_unsigned (getr regs 19))) by (symmetry; apply zw_u).
  assert (P20 : getr regs 20 = zw (bv_unsigned (getr regs 20))) by (symmetry; apply zw_u).
  assert (P21 : getr regs 21 = zw (bv_unsigned (getr regs 21))) by (symmetry; apply zw_u).
  assert (P2' : getr regs 2 = zw (SP + 48)) by (rewrite P2; f_equal; lia).
  pose proof Hsn as Hsn'.
  destruct (Z.eqb_spec sn 0) as [CZ|CZ].
  - run 60%nat [true] [RVal (EVar 42); RVal (EVar 36)]
        [(10, EVar 32); (11, EVar 37); (12, EVar 38); (2, EAdd (EVar 44) (ELit 48));
         (8, EVar 48); (9, EVar 49); (18, EVar 50); (19, EVar 51); (20, EVar 52); (21, EVar 53)]
        [S; PB; ds_pending ds; LB; ds_bi_valid ds; LT; DT; 0; 0; 0; sn; 0; SP; 0; 0; ds_bi_buf ds;
         bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
         bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21)] (ds_pending_buf ds).
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        br_fwdF HB M HFf;
        lazymatch goal with
        | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [ split; [exact HB2 | split; [apply (trees_rod_clear_wr R6 _ _ HRC); wr_towerF MS MP MF
                                              | split; [exact HP0 | apply agree_out_refl]]] |]
        end
    end.
    split; [unfold FRM; repeat split; frame_cells|].
    split; [intros HH'; exfalso; exact (HH' CZ)|].
    split; [intros _; regs_of HR Hfr|].
    regs_of HR Hfr.
  - run 60%nat [false] [RVal (EVar 42)]
        [(10, EVar 32); (11, EVar 37); (12, EVar 38); (2, EAdd (EVar 44) (ELit 48));
         (8, EVar 48); (9, EVar 49); (18, EVar 50); (19, EVar 51); (20, EVar 52); (21, EVar 53)]
        [S; PB; ds_pending ds; LB; ds_bi_valid ds; LT; DT; 0; 0; 0; sn; 0; SP; 0; 0; ds_bi_buf ds;
         bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
         bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21)] (ds_pending_buf ds).
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        br_fwdF HB M HFf;
        lazymatch goal with
        | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [ split; [exact HB2 | split; [apply (trees_rod_clear_wr R6 _ _ HRC); wr_towerF MS MP MF
                                              | split; [exact HP0 | apply agree_out_refl]]] |]
        end
    end.
    split; [unfold FRM; repeat split; frame_cells|].
    split; [intros _; split; [unfold CompressBlk6_1.KREGS; change (2 ^ 64 - 20) with 18446744073709551596; kregs HR Hfr | regs_of HR Hfr]|].
    split; [intros HH'; exfalso; exact (CZ HH')|].
    regs_of HR Hfr.
Qed.



Local Ltac frw H1 H2 := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (H2 r Hr); exact (H1 r Hr).

Lemma lcode_lx : forall regs m0 m s sx lc d1,
  CI m0 m s -> 0 <= lc < 256 -> 0 <= sx /\ sx + 3 < 2 ^ 31 -> 0 <= d1 < 32768 ->
  let code := arr_get length_code_a lc in
  let extra := arr_get extra_lbits_a code in
  let s2 := send_bits s (arr_get lfc (code + 257)) (arr_get ldl (code + 257)) in
  let s3 := if extra =? 0 then s2 else send_bits s2 (lc - arr_get base_length_a code) extra in
  sb_room PBL s (arr_get ldl (code + 257)) -> 0 <= arr_get ldl (code + 257) <= 15 ->
  (extra <> 0 -> sb_room PBL s2 extra) ->
  KREGS regs -> getr regs 14 = zw sx -> getr regs 31 = zw lc -> getr regs 28 = zw (d1 + 1) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c35c : word) m s6_rom) (mkst R (0x1c514 : word) m' s6_rom)
    /\ CI m0 m' s3
    /\ KREGS R /\ getr R 14 = zw sx /\ RBr 29%bv R s3 /\ getr R 30 = zw (ds_bi_valid s3)
    /\ getr R 28 = zw (d1 + 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s sx lc d1 HCI Hlc Hsx Hd1. cbv zeta. intros Hroom Vdl Hroom2 HK P14 P31 P28.
  destruct (arr_get extra_lbits_a (arr_get length_code_a lc) =? 0) eqn:CZ;
    destruct (lcode_site regs m0 m s sx lc d1 HCI Hlc Hsx Hd1 Hroom Vdl HK P14 P31 P28)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T14 & RB2 & T30 & T8 & T31 & T28 & Hfr2);
    rewrite CZ in Hms2.
  - exists R2, m2. split; [exact Hms2|]. split; [exact HCI2|]. split; [exact K2|]. split; [exact T14|].
    split; [exact RB2|]. split; [exact T30|]. split; [exact T28|]. exact Hfr2.
  - apply Z.eqb_neq in CZ.
    destruct (lx_site R2 m0 m2 _ sx lc d1 HCI2 Hlc Hsx Hd1 CZ (Hroom2 CZ) K2 T14 RB2 T30 T8 T31 T28)
      as (R3 & m3 & Hms3 & HCI3 & K3 & U14 & RB3 & U30 & U28 & Hfr3).
    exists R3, m3. split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
    split; [exact HCI3|]. split; [exact K3|]. split; [exact U14|]. split; [exact RB3|]. split; [exact U30|].
    split; [exact U28|]. frw Hfr2 Hfr3.
Qed.

Lemma dcode_dx : forall regs m0 m s sx d1,
  CI m0 m s -> 0 <= sx /\ sx + 3 < 2 ^ 31 -> 0 <= d1 < 32768 ->
  let dc := d_code d1 in
  let extra := arr_get extra_dbits_a dc in
  let s2 := send_bits s (arr_get dfc dc) (arr_get ddl dc) in
  let s3 := if extra =? 0 then s2 else send_bits s2 (wrap32 (d1 - arr_get base_dist_a dc)) extra in
  sb_room PBL s (arr_get ddl dc) -> 0 <= arr_get ddl dc <= 15 ->
  (extra <> 0 -> sb_room PBL s2 extra) ->
  KREGS regs -> getr regs 14 = zw sx -> RBr 29%bv regs s -> getr regs 30 = zw (ds_bi_valid s) ->
  getr regs 8 = zw (dc_idx d1) -> getr regs 31 = zw d1 ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c528 : word) m s6_rom) (mkst R (0x1c308 : word) m' s6_rom)
    /\ CI m0 m' s3
    /\ KREGS R /\ getr R 14 = zw sx /\ getr R 28 = zw (ds_bi_valid s3)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s sx d1 HCI Hsx Hd1. rewrite (d_code_idx d1) by lia. cbv zeta. intros Hroom Vdl Hroom2 HK P14 HRB P30 P8 P31.
  pose proof (dc_idx_range d1 Hd1) as Hidx.
  pose proof (dist_code_bound (dc_idx d1)) as Hdc.
  destruct (arr_get extra_dbits_a (arr_get dist_code_a (dc_idx d1)) =? 0) eqn:CZ;
    destruct (dcode_site regs m0 m s sx (dc_idx d1) d1 HCI Hidx Hsx Hd1 Hroom Vdl HK P14 HRB P30 P8 P31)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T14 & RB2 & T28 & T8 & T31 & Hfr2);
    rewrite CZ in Hms2.
  - exists R2, m2. split; [exact Hms2|]. split; [exact HCI2|]. split; [exact K2|]. split; [exact T14|].
    split; [exact T28|]. exact Hfr2.
  - apply Z.eqb_neq in CZ.
    destruct (dextra_site R2 m0 m2 _ sx (arr_get dist_code_a (dc_idx d1)) d1 HCI2 Hdc Hsx Hd1 CZ (Hroom2 CZ)
                K2 T14 RB2 T28 T8 T31)
      as (R3 & m3 & Hms3 & HCI3 & K3 & U14 & U28 & Hfr3).
    exists R3, m3. split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
    split; [exact HCI3|]. split; [exact K3|]. split; [exact U14|]. split; [exact U28|]. frw Hfr2 Hfr3.
Qed.


Lemma sbs_if1 : forall s (c : bool) v l,
  sbs_run s (if negb c then [(v, l)] else []) = (if c then s else send_bits s v l).
Proof. intros s [|] v l; reflexivity. Qed.

Lemma room_if1 : forall s (c : bool) v l,
  sbs_ok PBL s (if negb c then [(v, l)] else []) -> c = false -> sb_room PBL s l.
Proof. intros s [|] v l H E; [discriminate|]. cbn in H. tauto. Qed.

Lemma CI_bv : forall m0 m s, CI m0 m s -> 0 <= ds_bi_valid s <= 16.
Proof. intros m0 m s (_ & _ & HP & _). destruct HP as (_ & (H & _) & _). exact H. Qed.

Lemma sym_step : forall regs m0 m s sx,
  CI m0 m s -> sym_ok PBL s lfc ldl dfc ddl sx -> sx + 3 < 2 ^ 31 ->
  KREGS regs -> getr regs 14 = zw sx ->
  let s' := sbs_run s (sym_calls s lfc ldl dfc ddl sx) in
  exists R m',
    msteps s6_segs (mkst regs (0x1c314 : word) m s6_rom)
           (mkst R (if sx + 1 + 1 + 1 <? sn then (0x1c314 : word) else (0x1c660 : word)) m' s6_rom)
    /\ CI m0 m' s'
    /\ KREGS R /\ getr R 14 = zw (sx + 1 + 1 + 1) /\ getr R 28 = zw (ds_bi_valid s')
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m0 m s sx HCI Hsok Hsx3 HK P14. cbv zeta.
  destruct Hsok as (Hsx0 & Hroom & Hdist & Hlenl & Hlend & Hsbs).
  pose proof HCI as (HB & HRC & HP & HAG). pose proof HP as (Ppb & Pbinv & Pfc & Pdl & PLB & Psn & Plen).
  rewrite PLB in Hroom.
  destruct (head_blk regs m0 m s sx HCI Hsx0 Hroom Hsx3 HK P14) as (R1 & Hms1 & K1 & Q14 & Q31 & Q28 & Hfr1).
  pose proof (sym_dist_range s sx) as Hdr.
  assert (Hlc : 0 <= sym_lc s sx < 256).
  { rewrite sym_lc_eq; [apply wb_range | exact Ppb | rewrite Plen, PLB; lia]. }
  replace (sx + 1 + 1 + 1) with (sx + 3) by lia.
  unfold sym_calls in *. cbv zeta in Hsbs. cbv zeta. revert Hsbs.
  destruct (Z.eqb_spec (sym_dist s sx) 0) as [CD|CD]; intros Hsbs.
  -
    cbn [sbs_run] in *. destruct Hsbs as (Hl & Hr & _). specialize (Hlenl CD).
    destruct (lit_site R1 m0 m s sx (sym_lc s sx) HCI Hlc (conj Hsx0 Hsx3) Hr Hlenl K1 Q14 Q31)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T14 & T28 & Hfr2).
    destruct (lt_blk R2 m0 m2 _ sx HCI2 (conj Hsx0 Hsx3) K2 T14 T28) as (R3 & Hms3 & K3 & U14 & U28 & Hfr3).
    exists R3, m2. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
    split; [exact HCI2|]. split; [exact K3|]. split; [exact U14|]. split; [exact U28|].
    intros r Hr'. rewrite (Hfr3 r Hr'), (Hfr2 r Hr'). exact (Hfr1 r Hr').
  -
    unfold LITERALS in *.
    replace (arr_get length_code_a (sym_lc s sx) + 256 + 1) with (arr_get length_code_a (sym_lc s sx) + 257) in * by lia.
    rewrite !sbs_run_app. cbn [sbs_run]. rewrite !sbs_if1.
    pose proof (length_code_bound (sym_lc s sx)) as Hcode.
    assert (Hd1 : 0 <= sym_dist s sx - 1 < 32768) by (specialize (Hdist CD); lia).
    replace (sym_dist s sx) with (sym_dist s sx - 1 + 1) in Q28 by lia.
    specialize (Hlend CD). destruct Hlend as [HLENl HLENd].
    apply sbs_ok_app in Hsbs as (Hs1 & Hsbs). cbn [sbs_run sbs_ok] in Hs1. destruct Hs1 as (Hl1 & Hr1 & _).
    apply sbs_ok_app in Hsbs as (Hs2 & Hsbs).
    apply sbs_ok_app in Hsbs as (Hs3 & Hs4).
    rewrite ?sbs_run_app in Hs3. rewrite ?sbs_run_app in Hs4. cbn [sbs_run] in Hs2, Hs3, Hs4.
    rewrite ?sbs_if1 in Hs3. rewrite ?sbs_if1 in Hs4.
    cbn [sbs_ok] in Hs3. destruct Hs3 as (Hl3 & Hr3 & _).
    destruct (lcode_lx R1 m0 m s sx (sym_lc s sx) (sym_dist s sx - 1) HCI Hlc (conj Hsx0 Hsx3) Hd1 Hr1 HLENl
                ltac:(intros CZ; eapply room_if1; [exact Hs2 | apply Z.eqb_neq; exact CZ])
                K1 Q14 Q31 Q28)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T14 & RB2 & T30 & T28 & Hfr2).
    destruct (dd_blk R2 m2 _ sx (sym_dist s sx - 1) (conj Hsx0 Hsx3) Hd1 K2 T14 RB2 T30 T28 (CI_bv _ _ _ HCI2))
      as (R3 & Hms3 & K3 & U14 & RB3 & U30 & U8 & U31 & Hfr3).
    destruct (dcode_dx R3 m0 m2 _ sx (sym_dist s sx - 1) HCI2 (conj Hsx0 Hsx3) Hd1 Hr3 HLENd
                ltac:(intros CZ; eapply room_if1; [exact Hs4 | apply Z.eqb_neq; exact CZ])
                K3 U14 RB3 U30 U8 U31)
      as (R4 & m4 & Hms4 & HCI4 & K4 & V14 & V28 & Hfr4).
    destruct (lt_blk R4 m0 m4 _ sx HCI4 (conj Hsx0 Hsx3) K4 V14 V28) as (R5 & Hms5 & K5 & W14 & W28 & Hfr5).
    exists R5, m4. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
      eapply msteps_trans; [exact Hms4 | exact Hms5]. }
    split; [exact HCI4|]. split; [exact K5|]. split; [exact W14|]. split; [exact W28|].
    intros r Hr'. rewrite (Hfr5 r Hr'), (Hfr4 r Hr'), (Hfr3 r Hr'), (Hfr2 r Hr'). exact (Hfr1 r Hr').
Qed.


Lemma loop_run : forall fuel regs m0 m s sx,
  CI m0 m s -> cb_ok PBL fuel s lfc ldl dfc ddl sx -> 0 <= sx < sn -> sn - sx <= 3 * Z.of_nat fuel ->
  KREGS regs -> getr regs 14 = zw sx ->
  let s' := compress_block_loop fuel s lfc ldl dfc ddl sx in
  exists R m',
    msteps s6_segs (mkst regs (0x1c314 : word) m s6_rom) (mkst R (0x1c660 : word) m' s6_rom)
    /\ CI m0 m' s' /\ KREGS R /\ getr R 28 = zw (ds_bi_valid s')
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction fuel as [|f IH]; intros regs m0 m s sx HCI Hcok Hsx Hf HK P14; [lia|].
  cbv zeta. rewrite cb_loop_S. cbv zeta.
  cbn [cb_ok] in Hcok. destruct Hcok as (Hsym & Hrest).
  pose proof Hsn as Hsn'.
  destruct (sym_step regs m0 m s sx HCI Hsym ltac:(lia) HK P14) as (R1 & m1 & Hms1 & HCI1 & K1 & Q14 & Q28 & Hfr1).
  assert (Esn : ds_sym_next (sbs_run s (sym_calls s lfc ldl dfc ddl sx)) = sn).
  { destruct HCI1 as (_ & _ & HP1 & _). destruct HP1 as (_ & _ & _ & _ & _ & Psn1 & _). exact Psn1. }
  rewrite Esn in Hrest |- *.
  destruct (Z.ltb_spec (sx + 1 + 1 + 1) sn) as [CL|CL].
  - destruct (IH R1 m0 m1 _ (sx + 1 + 1 + 1) HCI1 Hrest ltac:(lia) ltac:(lia) K1 Q14)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T28 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HCI2|]. split; [exact K2|]. split; [exact T28|]. frw Hfr1 Hfr2.
  - exists R1, m1. split; [exact Hms1|]. split; [exact HCI1|]. split; [exact K1|]. split; [exact Q28|]. exact Hfr1.
Qed.


Theorem compress_block_run : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw LT -> getr regs 12 = zw DT -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c2a8 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ BRm m' (compress_block ds lfc ldl dfc ddl)
    /\ trees_rod_clear6 m'
    /\ getr R 2 = getr regs 2
    /\ (forall r : reg, reg_in r CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P2 P1.
  destruct Hok as (HBI & HPB & Hcb & Hendl & Hend).
  destruct (pro_blk regs P10 P11 P12 P2 P1) as (R1 & m1 & Hms1 & HCI1 & HF1 & HKl & HKx & Q10 & Q11 & Q2 & Q1 & Hfr1).
  unfold compress_block. unfold END_BLOCK in *.
  destruct (Z.eqb_spec sn 0) as [CZ|CZ].
  -
    cbn [negb] in Hend |- *. cbn [sbs_ok] in Hend. destruct Hend as (_ & Hroom0 & _).
    destruct (HKx CZ) as (Q13 & Q28).
    destruct (end_blk R1 m1 m1 ds regs HCI1 HF1 Hroom0 Hendl Q10 Q13 Q11 Q2 Q1 Q28)
      as (R2 & m2 & Hms2 & HB2 & HRC2 & E8 & E9 & E18 & E19 & E20 & E21 & E2 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [unfold send_code; exact HB2|]. split; [exact HRC2|].
    split; [rewrite E2, P2; reflexivity|].
    apply (frame_fix R2 regs 2%bv); [rewrite E2, P2; reflexivity|].
    apply (frame_fix R2 regs 8%bv); [exact E8|]. apply (frame_fix R2 regs 9%bv); [exact E9|].
    apply (frame_fix R2 regs 18%bv); [exact E18|]. apply (frame_fix R2 regs 19%bv); [exact E19|].
    apply (frame_fix R2 regs 20%bv); [exact E20|]. apply (frame_fix R2 regs 21%bv); [exact E21|].
    intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
  -
    destruct (HKl CZ) as (K1 & Q14). specialize (Hcb CZ).
    replace (negb false) with true by reflexivity. cbn [negb] in Hend.
    pose proof Hsn as Hsn'.
    destruct (loop_run (Z.to_nat sn) R1 m1 m1 ds 0 HCI1 Hcb ltac:(lia) ltac:(lia) K1 Q14)
      as (R2 & m2 & Hms2 & HCI2 & K2 & T28 & Hfr2).
    set (sL := compress_block_loop (Z.to_nat sn) ds lfc ldl dfc ddl 0) in *.
    pose proof HCI2 as (_ & _ & _ & HAG2).
    pose proof (FRM_keep m1 m2 regs HAG2 HF1) as HF2.
    destruct K2 as (W10 & W13 & W11 & W12 & W15 & W5 & W6 & W16 & W17 & W7 & W2).
    cbn [sbs_ok] in Hend. destruct Hend as (_ & Hroom0 & _).
    destruct (end_blk R2 m1 m2 sL regs HCI2 HF2 Hroom0 Hendl W10 W13 W11 W2
                ltac:(rewrite (Hfr2 1%bv eq_refl); exact Q1) T28)
      as (R4 & m4 & Hms4 & HB4 & HRC4 & E8 & E9 & E18 & E19 & E20 & E21 & E2 & Hfr4).
    exists R4, m4. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms4]. }
    split; [unfold send_code; exact HB4|]. split; [exact HRC4|].
    split; [rewrite E2, P2; reflexivity|].
    apply (frame_fix R4 regs 2%bv); [rewrite E2, P2; reflexivity|].
    apply (frame_fix R4 regs 8%bv); [exact E8|]. apply (frame_fix R4 regs 9%bv); [exact E9|].
    apply (frame_fix R4 regs 18%bv); [exact E18|]. apply (frame_fix R4 regs 19%bv); [exact E19|].
    apply (frame_fix R4 regs 20%bv); [exact E20|]. apply (frame_fix R4 regs 21%bv); [exact E21|].
    intros r Hr. rewrite (Hfr4 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
    rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

End Walk.
End FXG.
