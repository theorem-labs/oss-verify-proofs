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


Lemma mod64_neg : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros x Hx. rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Local Ltac umod1 := first [ rewrite mod64_neg by lia; lia | rewrite Z.mod_small by lia; lia ].
Local Ltac umod := first [ umod1 | match goal with Hc : _ \/ _ |- _ => destruct Hc; umod1 end ].


Lemma lcode_site : forall regs m0 m s sx lc d1,
  CI m0 m s -> 0 <= lc < 256 -> 0 <= sx /\ sx + 3 < 2 ^ 31 -> 0 <= d1 < 32768 ->
  let code := arr_get length_code_a lc in
  let extra := arr_get extra_lbits_a code in
  sb_room PBL s (arr_get ldl (code + 257)) -> 0 <= arr_get ldl (code + 257) <= 15 ->
  KREGS regs -> getr regs 14 = zw sx -> getr regs 31 = zw lc -> getr regs 28 = zw (d1 + 1) ->
  let s2 := send_bits s (arr_get lfc (code + 257)) (arr_get ldl (code + 257)) in
  exists R m',
    msteps s6_segs (mkst regs (0x1c35c : word) m s6_rom)
           (mkst R (if extra =? 0 then (0x1c514 : word) else (0x1c478 : word)) m' s6_rom)
    /\ CI m0 m' s2
    /\ (KREGS R /\ getr R 14 = zw sx /\ RBr 29%bv R s2 /\ getr R 30 = zw (ds_bi_valid s2)
        /\ getr R 8 = zw (code * 4) /\ getr R 31 = zw lc /\ getr R 28 = zw (d1 + 1)
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s sx lc d1 (HB & HRC & HP & HAG) Hlc Hsx Hd1. cbv zeta. intros Hroom Vdl HK P14 P31 P28.
  open_br HB HRC HP.
  destruct HK as (P10 & P13 & P11 & P12 & P15 & P5 & P6 & P16 & P17 & P7 & P2).
  pose proof (length_code_bound lc) as Hcode.
  assert (Edl : pb ldl (arr_get length_code_a lc + 257) = arr_get ldl (arr_get length_code_a lc + 257)) by (apply pb_small; lia).
  pose proof (extra_lbits_zero_iff (arr_get length_code_a lc) Hcode) as Hz.
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - arr_get ldl (arr_get length_code_a lc + 257)) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|];
    destruct (arr_get extra_lbits_a (arr_get length_code_a lc) =? 0);
    [ assert (Hc : arr_get length_code_a lc < 8 \/ arr_get length_code_a lc = 28) by (symmetry in Hz; apply orb_prop in Hz; destruct Hz as [Hz|Hz]; [left; apply Z.ltb_lt in Hz | right; apply Z.eqb_eq in Hz]; lia)
    | assert (Hc : 8 <= arr_get length_code_a lc <= 27) by (symmetry in Hz; apply orb_false_elim in Hz; destruct Hz as [Hz1 Hz2]; apply Z.ltb_ge in Hz1; apply Z.eqb_neq in Hz2; lia)
    | assert (Hc : arr_get length_code_a lc < 8 \/ arr_get length_code_a lc = 28) by (symmetry in Hz; apply orb_prop in Hz; destruct Hz as [Hz|Hz]; [left; apply Z.ltb_lt in Hz | right; apply Z.eqb_eq in Hz]; lia)
    | assert (Hc : 8 <= arr_get length_code_a lc <= 27) by (symmetry in Hz; apply orb_false_elim in Hz; destruct Hz as [Hz1 Hz2]; apply Z.ltb_ge in Hz1; apply Z.eqb_neq in Hz2; lia) ];
    clear Hz.
  -
    run 80%nat [false; false]
        [RVal (EApp1 5 (EVar 39)); RVal (EApp1 1 (EAdd (EApp1 5 (EVar 39)) (ELit 257)));
         RVal (EApp1 2 (EAdd (EApp1 5 (EVar 39)) (ELit 257))); RVal (EVar 36); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
        (KP ++ [(14, EVar 41); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    all: try (nf; umod).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_flush nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_flush (29%bv : reg) HR nf|];
            split; [bv_flush (30%bv : reg) HR nf |]; regs_of HR Hfr).
  -
    run 80%nat [false; true]
        [RVal (EApp1 5 (EVar 39)); RVal (EApp1 1 (EAdd (EApp1 5 (EVar 39)) (ELit 257)));
         RVal (EApp1 2 (EAdd (EApp1 5 (EVar 39)) (ELit 257))); RVal (EVar 36); RVal (EVar 47); RVal (EVar 34); RVal (EVar 33)]
        (KP ++ [(14, EVar 41); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    all: try (nf; umod).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_flush nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_flush (29%bv : reg) HR nf|];
            split; [bv_flush (30%bv : reg) HR nf |]; regs_of HR Hfr).
  -
    run 80%nat [true; true]
        [RVal (EApp1 5 (EVar 39)); RVal (EApp1 1 (EAdd (EApp1 5 (EVar 39)) (ELit 257)));
         RVal (EApp1 2 (EAdd (EApp1 5 (EVar 39)) (ELit 257))); RVal (EVar 36); RVal (EVar 47)]
        (KP ++ [(14, EVar 41); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    all: try (nf; umod).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_keep nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_keep (29%bv : reg) HR nf|];
            split; [bv_keep (30%bv : reg) HR nf |]; regs_of HR Hfr).
  -
    run 80%nat [true; false]
        [RVal (EApp1 5 (EVar 39)); RVal (EApp1 1 (EAdd (EApp1 5 (EVar 39)) (ELit 257)));
         RVal (EApp1 2 (EAdd (EApp1 5 (EVar 39)) (ELit 257))); RVal (EVar 36); RVal (EVar 47)]
        (KP ++ [(14, EVar 41); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; 0; SP; 0; 0; ds_bi_buf s] (ds_pending_buf s).
    all: try (nf; umod).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_keep nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_keep (29%bv : reg) HR nf|];
            split; [bv_keep (30%bv : reg) HR nf |]; regs_of HR Hfr).
Qed.



Lemma lx_site : forall regs m0 m s sx lc d1,
  CI m0 m s -> 0 <= lc < 256 -> 0 <= sx /\ sx + 3 < 2 ^ 31 -> 0 <= d1 < 32768 ->
  let code := arr_get length_code_a lc in
  let extra := arr_get extra_lbits_a code in
  extra <> 0 -> sb_room PBL s extra ->
  KREGS regs -> getr regs 14 = zw sx -> RBr 29%bv regs s -> getr regs 30 = zw (ds_bi_valid s) ->
  getr regs 8 = zw (code * 4) -> getr regs 31 = zw lc -> getr regs 28 = zw (d1 + 1) ->
  let s2 := send_bits s (lc - arr_get base_length_a code) extra in
  exists R m',
    msteps s6_segs (mkst regs (0x1c478 : word) m s6_rom) (mkst R (0x1c514 : word) m' s6_rom)
    /\ CI m0 m' s2
    /\ (KREGS R /\ getr R 14 = zw sx /\ RBr 29%bv R s2 /\ getr R 30 = zw (ds_bi_valid s2)
        /\ getr R 28 = zw (d1 + 1)
        /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)).
Proof.
  intros regs m0 m s sx lc d1 (HB & HRC & HP & HAG) Hlc Hsx Hd1. cbv zeta. intros Hxz Hroom HK P14 HRB P30 P8 P31 P28.
  open_br HB HRC HP.
  destruct HK as (P10 & P13 & P11 & P12 & P15 & P5 & P6 & P16 & P17 & P7 & P2).
  pose proof (length_code_bound lc) as Hcode.
  pose proof (extra_lbits_bound (arr_get length_code_a lc)) as Hxl.
  pose proof (base_length_bound (arr_get length_code_a lc)) as Hbl.
  pose proof (base_length_le lc Hlc) as Hlb.
  pose proof (u64_range (getr regs 29)) as U29. unfold RBr in HRB.
  assert (P29 : getr regs 29 = zw (bv_unsigned (getr regs 29))) by (symmetry; apply zw_u).
  assert (P8' : getr regs 8 = zw (arr_get length_code_a lc * 2 ^ 2)) by (rewrite P8; f_equal; lia).
  unfold sb_room, Buf_size in Hroom.
  destruct (Z.ltb_spec (16 - arr_get extra_lbits_a (arr_get length_code_a lc)) (ds_bi_valid s)) as [CF|CF];
    [specialize (Hroom ltac:(unfold Buf_size; lia))|].
  - run 80%nat [false] [RVal (EApp1 8 (EVar 43)); RVal (EApp1 7 (EVar 43)); RVal (EVar 34); RVal (EVar 33); RVal (EVar 36)]
        (KP ++ [(14, EVar 41); (29, EVar 45); (30, EVar 36); (8, EShl (EVar 43) 2); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; arr_get length_code_a lc; SP;
         bv_unsigned (getr regs 29); 0; 0] (ds_pending_buf s).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_flush nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_flush (29%bv : reg) HR nf|];
            split; [bv_flush (30%bv : reg) HR nf |]; regs_of HR Hfr).
  - run 80%nat [true] [RVal (EApp1 8 (EVar 43)); RVal (EApp1 7 (EVar 43))]
        (KP ++ [(14, EVar 41); (29, EVar 45); (30, EVar 36); (8, EShl (EVar 43) 2); (31, EVar 39); (28, EAdd (EVar 40) (ELit 1))])
        [S; PB; ds_pending s; LB; ds_bi_valid s; LT; DT; lc; d1; sx; sn; arr_get length_code_a lc; SP;
         bv_unsigned (getr regs 29); 0; 0] (ds_pending_buf s).
    site_fin Hms HR Hfr HB HRC HP HAG MS MP ltac:(st_keep nf)
      ltac:(split; [kregs HR Hfr|]; split; [reg1 HR Hfr|]; split; [rb_keep (29%bv : reg) HR nf|];
            split; [bv_keep (30%bv : reg) HR nf |]; regs_of HR Hfr).
Qed.

End Walk.
End FXG.
