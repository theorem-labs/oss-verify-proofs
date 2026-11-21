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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 MemFill
  RomRead TreesRod BitsLib BuildTreeLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab BuildTreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2 BuildTree6_3 BuildTree6_4 BuildTree6_5.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variable (t : tree_id).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation T := (S + toff t).
Local Abbreviation E := (sd_elems t).
Local Abbreviation SP := (sp - 144).
Local Abbreviation BRm := (BR6 F mem0 S p PBL).
Local Abbreviation U := (bt_upd ds t).
Local Abbreviation SDA := (SDA R6).
Local Abbreviation STP := (STP R6).
Local Abbreviation EXP := (EXP R6).

Hypothesis HH : BTH F mem0 mem S p PBL ds ra sp.

Let Hret : ret_ok ra := bth_ret _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := bth_L _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := bth_FS _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 144 := bth_fr _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := bth_br _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6 mem := bth_rod _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 144 <= sp <= 2 ^ 63 := proj1 Hcf.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Abbreviation GB := (BuildTree6_1.GB S sp).
Local Abbreviation CI := (BuildTree6_1.CI F mem0 S p PBL sp).
Local Abbreviation FRM := (BuildTree6_1.FRM sp).
Local Abbreviation stree_dl := (BuildTree6_1.stree_dl t).
Local Abbreviation stF := (BuildTree6_1.stF t).
Local Abbreviation L1REGS := (BuildTree6_1.L1REGS S sp t).
Local Abbreviation X0 := (BuildTree6_1.X0 ds t).
Local Abbreviation L1 := (BuildTree6_1.L1 t).
Local Abbreviation tsize_elems := (BuildTree6_1.tsize_elems t).
Local Abbreviation elems_range := (BuildTree6_1.elems_range t).
Local Abbreviation dsc_off_val := (BuildTree6_1.dsc_off_val t).
Local Abbreviation SDA_range := (BuildTree6_1.SDA_range t).
Local Abbreviation STP_range := (BuildTree6_1.STP_range t).
Local Abbreviation EXP_range := (BuildTree6_1.EXP_range t).
Local Abbreviation pqF3 := BuildTree6_3.pqF3.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [BuildTree6_1.stF].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; symex_read_auto
            | nf; symex_store_auto
            | nf; symex_sok_auto
            | intros; nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia] ].

Local Ltac run_with C vb fuel dirs rds pins pv FC DL HP DP BC :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals ((BuildTree6_1.stF t) FC DL HP DP BC) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac open_ci_gen thin HC :=
  let HB := fresh "HB" in let HRC := fresh "HRC" in let HAG := fresh "HAG" in let MF := fresh "MF" in
  destruct HC as (HB & HRC & HAG & MF); unfold mapped in MF;
  let HS' := fresh "HS'" in let HPB' := fresh "HPB'" in let HD := fresh "HD" in
  pose proof HLb as HL'; destruct HL' as (HS' & HPB' & HD & _); unfold dsl_SIZE in HS', HD;
  let MS := fresh "MS" in let MP := fresh "MP" in let Hsc := fresh "Hsc" in let Har := fresh "Har" in let HTL := fresh "HTL" in
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & HTL & _ & _ & MS & MP & _); unfold mapped, dsl_SIZE in MS, MP;
  let C := fresh "C" in
  pose proof (BRT_cells _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB) as C;
  let CFC := fresh "CFC" in let CDL := fresh "CDL" in let CHP := fresh "CHP" in let CDP := fresh "CDP" in let CBC := fresh "CBC" in
  let Chl := fresh "Chl" in let Chm := fresh "Chm" in let Copt := fresh "Copt" in let Cstat := fresh "Cstat" in let Cmc := fresh "Cmc" in
  destruct C as (CFC & CDL & CHP & CDP & CBC & Chl & Chm & Copt & Cstat & Cmc);
  let Cdyn := fresh "Cdyn" in let Csd := fresh "Csd" in
  destruct (BRT_desc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB) as (Cdyn & Csd);
  replace (match t with TL => 168672 | TD => 168704 | TB => 168736 end) with (SDA t) in Csd by (destruct t; reflexivity);
  let Cst := fresh "Cst" in let Cex := fresh "Cex" in let Cbase := fresh "Cbase" in let Celems := fresh "Celems" in let Cml := fresh "Cml" in
  destruct (sdesc_cells R6 _ _ trod_ok6 HRC t) as (Cst & Cex & Cbase & Celems & Cml);
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let He := fresh "He" in pose proof elems_range as He;
  let Hte := fresh "Hte" in pose proof tsize_elems as Hte;
  let Hdo := fresh "Hdo" in pose proof dsc_off_val as Hdo;
  let Hsda := fresh "Hsda" in pose proof SDA_range as Hsda;
  let Hstp := fresh "Hstp" in pose proof STP_range as Hstp;
  let RODS := fresh "RODS" in
  pose proof (mapped_rod_apart R6 _ _ S 5968 trod_ok6 HRC MS ltac:(lia) ltac:(lia)) as RODS;
  let RODF := fresh "RODF" in
  pose proof (mapped_rod_apart R6 _ _ (sp - 144) 144 trod_ok6 HRC MF ltac:(lia) ltac:(lia)) as RODF;
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODF;
  lazymatch thin with
  | true => clear RODS RODF HD Cst Cex Cbase Celems Cml Cdyn Csd; try clear HPB'
  | false => idtac
  end.
Local Ltac open_ci HC := open_ci_gen false HC.
Local Ltac open_ciT HC := open_ci_gen true HC.


Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold BuildTree6_1.GB;
              first [ apply sub_franges_here; unfold dsl_SIZE; cbn; lia
                    | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac rod_tower HRC MS MP MF :=
  apply (trees_rod_clear_wr R6 _ _ HRC);
  repeat (apply wr_ok_wbytes;
          [ | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
              rewrite ?length_Z_to_le_bytes in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length] in Hx;
              first [apply MS; lia | apply MP; lia | apply MF; lia]
            | lia | rewrite ?length_Z_to_le_bytes; cbn; lia ]);
  apply wr_ok_refl.

Local Ltac oth HFf :=
  rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul];
  first [ lia | unfold dsl_SIZE in *; lia | eapply sub_franges_mono; [exact HFf | lia | lia] ].

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
            first [assumption | reflexivity | f_equal; lia | f_equal; f_equal; lia | f_equal; repeat (rewrite (szwrap_small 32) by lia); lia
                  | rewrite zw_u; assumption ] end ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M ks ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; try reflexivity
                          | split; [ rod_tower HRC MS MP MF
                                   | split; [ ag_tower HAG
                                            | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                              repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                 | tregs ]
      end
  end.


Local Abbreviation stC5 := BuildTree6_5.stC5.
Local Abbreviation VB5 := BuildTree6_5.VB5.
Local Abbreviation EP5 := BuildTree6_5.EP5.
Local Abbreviation HB5 := BuildTree6_5.HB5.
Local Abbreviation HP5 := BuildTree6_5.HP5.
Local Abbreviation MP5 := BuildTree6_5.MP5.

Section PhaseE.
Variables (BC : arr) (OL SL MC : Z).
Local Abbreviation W6 FC DL HP HL HM DP := (U FC DL HP HL HM DP BC OL SL MC).
Hypothesis Hmc : 0 <= MC < 600.

Local Abbreviation BASE4 := (BuildTree6_4.BASE4 S sp t MC).
Local Abbreviation EREGS := (BuildTree6_4.EREGS S sp t MC).
Local Abbreviation X2REGS := (BuildTree6_4.X2REGS S sp t MC).
Local Abbreviation RNG := (BuildTree6_4.RNG t).
Local Abbreviation PQ4 := (BuildTree6_4.PQ4 t).
Local Abbreviation EI := (BuildTree6_4.EI F mem0 S p PBL ds sp t BC OL SL MC).

Local Ltac nflor :=
  cbn [BuildTree6_3.pqF3];
  repeat match goal with H : Z.lor ?a 1 = _ |- context [Z.lor ?a 1] => rewrite !H end.
Local Ltac nf3 :=
  nflor;
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac side_closer5 :=
  try solve [ assumption
            | nf3; first [ assumption | lia | rewrite ?Z.mod_small by lia; lia
                         | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; nf3; lia end
            | nflor; symex_read_auto
            | nf3; symex_store_auto
            | nf3; symex_sok_auto
            | intros; cbn [BuildTree6_3.pqF3]; first [apply pb_range | apply hv_range | apply wb_range] ].

Local Ltac run5 fuel dirs rds pins pv FC HP DP :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB5 in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs stC5 fuel dirs rdv pinsv vbv NoRegions pv NoVals (pqF3 FC HP DP) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer5
  end.

Local Ltac regs5 HR Hfr :=
  unfold BuildTree6_4.EREGS, BuildTree6_4.X2REGS, BuildTree6_4.BASE4;
  repeat split;
  (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ =>
     first [ rewrite (Hfr r eq_refl); assumption
           | symex_reg HR r as A; rewrite A; cbn [BuildTree6_3.pqF3];
             first [reflexivity | assumption | f_equal; nf3; repeat (rewrite (szwrap_small 32) by lia); lia | nf3; assumption
                   | rewrite zw_u; assumption ] ] end).

Local Ltac nodef FC DP x PF PD :=
  assert (PF : pb FC x = arr_get FC x)
    by (apply (pb_get FC); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 Hr); rewrite <- (proj1 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj1 (proj2 (proj2 Hr))); lia end]);
  assert (PD : wb DP x = arr_get DP x)
    by (apply (wb_get DP); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 (proj2 Hr)); rewrite <- (proj2 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj2 (proj2 (proj2 Hr))); lia end]).

Local Ltac blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M ks ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; try reflexivity
                                   | split; [ rod_tower HRC MS MP MF
                                            | split; [ ag_tower HAG
                                                     | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                                       repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                          | ]
                 | tregs ]
      end
  end.

Local Ltac nf_in H :=
  let T := type of H in let T' := eval cbn [BuildTree6_3.pqF3] in T in symex_recast H T'.

Local Abbreviation H3B := (BuildTree6_5.H3B S sp t MC).
Local Abbreviation H3REGS := (BuildTree6_5.H3REGS S sp t MC).
Local Abbreviation M3REGS := (BuildTree6_5.M3REGS S sp t MC).
Local Abbreviation X3REGS := (BuildTree6_5.X3REGS S sp t MC).
Local Abbreviation FREGS := (BuildTree6_5.FREGS S sp t MC).
Local Abbreviation dmax := BuildTree6_5.dmax.
Local Abbreviation e2_blk := (BuildTree6_5.e2_blk F mem0 mem S p PBL ds ra sp t HH BC OL SL MC Hmc).


Section Pq3.
Variables (FC DL : arr) (HLc HM : Z) (DP : arr) (node : Z).
Local Abbreviation W h := (W6 FC DL h HLc HM DP).
Hypothesis Hhl : 1 <= HLc <= 571.
Hypothesis Hnode : 0 <= node < tsize t.

Local Abbreviation smal := (BuildTree6_3.smal FC DP).
Local Abbreviation sel := (BuildTree6_3.sel3 FC HLc DP).

Definition DI3 (m1 m : word -> option byte) (h : arr) : Prop := EI m1 m FC DL h HLc HM DP.

Local Ltac open_di HD :=
  let HC := fresh "HC" in let HPQ := fresh "HPQ" in let HRN := fresh "HRN" in let LDL := fresh "LDL" in let C0 := fresh "C0" in
  let HPQ1 := fresh "HPQ1" in let LHP := fresh "LHP" in
  let RFC := fresh "RFC" in let RDP := fresh "RDP" in let LFC := fresh "LFC" in let LDP := fresh "LDP" in
  destruct HD as (HC & HPQ & HRN & LDL & C0); pose proof HPQ as [HPQ1 LHP]; pose proof HRN as (RFC & RDP & LFC & LDP); open_ciT HC.

Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : forall q, 1 <= q <= HLc -> 0 <= arr_get h q < tsize t |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  nodef FC DP (arr_get h i) PF PD.

Local Ltac open_b5 H :=
  let H' := fresh "BR'" in pose proof H as H';
  destruct H' as ((P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10) & P16 & P17).

Local Ltac regs5' HR Hfr :=
  unfold H3REGS, M3REGS, X3REGS, H3B, BuildTree6_4.BASE4;
  repeat split;
  (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ =>
     first [ rewrite (Hfr r eq_refl); assumption
           | symex_reg HR r as A; rewrite A; cbn [BuildTree6_3.pqF3];
             first [reflexivity | assumption | f_equal; nf3; repeat (rewrite (szwrap_small 32) by lia); lia | nf3; assumption
                   | rewrite zw_u; assumption ] ] end).

Lemma h3b_step : forall regs m1 m h j k,
  DI3 m1 m h -> H3REGS regs node HLc j k -> 1 <= k -> j = k * 2 -> j <= HLc ->
  exists R, msteps s6_segs (mkst regs (0x1bd6c : word) m s6_rom) (mkst R (0x1bdd8 : word) m s6_rom)
    /\ M3REGS R node j k (sel h j)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h j k HD HRg Hk Hjk Hj. open_di HD. destruct HRg as (HBx & P6 & P5 & P28). open_b5 HBx.
  assert (P8' : getr regs 8 = zw (S + 2976)) by exact P8.
  nodef FC DP node PFv PDv.
  pose proof (lor1_even k ltac:(lia)) as Hj1. rewrite <- Hjk in Hj1.
  node h j Vj Rj PFj PDj.
  unfold BuildTree6_3.sel3.
  destruct (Z.ltb_spec j HLc) as [Cj|Cj]; cbn [andb].
  - node h (j + 1) Vj1 Rj1 PFj1 PDj1.
    assert (Vj1' : hv h (Z.lor j 1) = arr_get h (j + 1)) by (rewrite Hj1; exact Vj1).
    unfold BuildTree6_3.smal.
    destruct (Z.ltb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C1|C1]; cbn [orb].
    + run5 40%nat [false; false] NoReads HP5 [S; T; j; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
      exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
    + destruct (Z.eqb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C2|C2]; cbn [andb].
      * destruct (Z.leb_spec (arr_get DP (arr_get h (j + 1))) (arr_get DP (arr_get h j))) as [C3|C3].
        -- run5 40%nat [false; true; false; true] NoReads HP5 [S; T; j; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
           exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
        -- run5 40%nat [false; true; false; false] NoReads HP5 [S; T; j; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
           exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
      * run5 40%nat [false; true; true] NoReads HP5 [S; T; j; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
        exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
  - run5 40%nat [true] NoReads HP5 [S; T; j; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
    exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h3b_step OK". exact I. Qed.

Lemma DI3_write : forall m1 m h i x x' a,
  DI3 m1 m h -> trees_rod_clear6 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  agree_out GB m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  1 <= i <= HLc -> 0 <= x < tsize t -> a = S + 3008 + 4 * i -> x' = x ->
  DI3 m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) (arr_set h i x).
Proof.
  intros m1 m h i x x' a (HC & HPQ & HRN & LDL & C0) HRC' HAG' Hi Hx Ha ->. destruct HC as (HB & HRC & HAG & MF).
  pose proof HPQ as [HPQ1 HLh].
  pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'. pose proof HLb as (HS' & _). unfold dsl_SIZE in HS'.
  split; [|split; [|split; [exact HRN|split; [exact LDL|]]]].
  - split; [| split; [exact HRC' | split; [exact HAG' | apply mapped_wbytes; exact MF]]].
    apply (BRT_heap _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | exact Ha | lia].
  - split; [| rewrite arr_len_set; exact HLh].
    intros q Hq. rewrite arr_get_set. unfold arr_inb. rewrite HLh.
    destruct (i =? q), (0 <=? i), (i <? 573); cbn [andb]; try lia; apply HPQ1; lia.
  - subst a. frame_cells.
Qed.

Local Ltac rod1 HRC MS := apply (trees_rod_clear_wbytes R6 _ _ _ HRC); [intros x Hx; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia].
Local Ltac ag1 HAG := apply agree_out_wbytes; [exact HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia].
Local Ltac write1 m1 m h k x HD0 HRC MS HAG :=
  apply (DI3_write m1 m h k x); [exact HD0 | rod1 HRC MS | ag1 HAG | lia | lia | lia | nf3; first [reflexivity | lia]].

Lemma m3b_step : forall regs m1 m h j k j',
  DI3 m1 m h -> M3REGS regs node j k j' -> 1 <= k < j -> j <= j' <= HLc -> j' <= j + 1 ->
  if smal node (arr_get h j') then
    exists R, msteps s6_segs (mkst regs (0x1bdd8 : word) m s6_rom) (mkst R (0x1bb90 : word) m s6_rom)
      /\ X3REGS R node k
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else if j' * 2 <=? HLc then
    exists R m', msteps s6_segs (mkst regs (0x1bdd8 : word) m s6_rom) (mkst R (0x1bd6c : word) m' s6_rom)
      /\ DI3 m1 m' (arr_set h k (arr_get h j'))
      /\ H3REGS R node HLc (j' * 2) j'
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else
    exists R m', msteps s6_segs (mkst regs (0x1bdd8 : word) m s6_rom) (mkst R (0x1bb90 : word) m' s6_rom)
      /\ DI3 m1 m' (arr_set h k (arr_get h j'))
      /\ X3REGS R node j'
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h j k j' HD HMR Hkj Hj Hj1. pose proof HD as HD0. open_di HD.
  destruct HMR as (HBx & P5 & P6 & P7). open_b5 HBx.
  assert (P8' : getr regs 8 = zw (S + 2976)) by exact P8.
  nodef FC DP node PFv PDv.
  node h j' Vj' Rj' PFj' PDj'.
  unfold BuildTree6_3.smal.
  destruct (Z.ltb_spec (arr_get FC node) (arr_get FC (arr_get h j'))) as [C1|C1]; cbn [orb].
  - run5 40%nat [true] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
    exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
  - destruct (Z.eqb_spec (arr_get FC node) (arr_get FC (arr_get h j'))) as [C2|C2]; cbn [andb].
    + destruct (Z.leb_spec (arr_get DP node) (arr_get DP (arr_get h j'))) as [C3|C3].
      * run5 40%nat [false; false; false] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
        exists R. split; [exact Hms|]. split; [regs5' HR Hfr | fr_weak Hfr].
      * destruct (Z.leb_spec (j' * 2) HLc) as [C4|C4].
        -- run5 40%nat [false; false; true; false] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [regs5' HR Hfr | fr_weak Hfr]
           end.
        -- run5 40%nat [false; false; true; true] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [regs5' HR Hfr | fr_weak Hfr]
           end.
    + destruct (Z.leb_spec (j' * 2) HLc) as [C4|C4].
      * run5 40%nat [false; true; false] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [regs5' HR Hfr | fr_weak Hfr]
        end.
      * run5 40%nat [false; true; true] [RVal (EVar 37)] MP5 [S; T; j; 0; k; HLc; j'; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [regs5' HR Hfr | fr_weak Hfr]
        end.
Qed.

Goal True. idtac "m3b_step OK". exact I. Qed.

Lemma smaller_W3 : forall h a b, smaller (W h) t a b = smal a b.
Proof. intros. unfold smaller, BuildTree6_3.smal. autorewrite with btupd. reflexivity. Qed.

Lemma loop3b_S_sel : forall f h v k j, j <= HLc ->
  pqdownheap_loop (Datatypes.S f) (W h) t v k j =
    if smal v (arr_get h (sel h j)) then (W h, k)
    else pqdownheap_loop f (W (arr_set h k (arr_get h (sel h j)))) t v (sel h j) (sel h j * 2).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. autorewrite with btupd.
  replace (j <=? HLc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  autorewrite with btupd. rewrite !smaller_W3. unfold BuildTree6_3.sel3.
  destruct ((j <? HLc) && smal (arr_get h (j + 1)) (arr_get h j)).
  - destruct (smal v (arr_get h (j + 1))); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
  - destruct (smal v (arr_get h j)); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
Qed.

Lemma inner3b : forall fuel regs m1 m h j k,
  DI3 m1 m h -> H3REGS regs node HLc j k -> 1 <= k -> j = k * 2 -> j <= HLc ->
  HLc < j * 2 ^ Z.of_nat fuel ->
  let '(s', k') := pqdownheap_loop fuel (W h) t node k j in
  exists R m', msteps s6_segs (mkst regs (0x1bd6c : word) m s6_rom) (mkst R (0x1bb90 : word) m' s6_rom)
    /\ DI3 m1 m' (ds_heap s') /\ 1 <= k' <= HLc
    /\ X3REGS R node k'
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction fuel as [|f IH]; intros regs m1 m h j k HD HRg Hk Hjk Hj Hfuel.
  - exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
    rewrite loop3b_S_sel by lia.
    pose proof (BuildTree6_3.sel3_range FC HLc DP h j ltac:(lia)) as Hsel.
    destruct (h3b_step regs m1 m h j k HD HRg Hk Hjk Hj) as (R1 & Hms1 & HM1 & Hfr1).
    pose proof (m3b_step R1 m1 m h j k (sel h j) HD HM1 ltac:(lia) ltac:(lia) ltac:(lia)) as HB.
    destruct (smal node (arr_get h (sel h j))).
    + destruct HB as (R2 & Hms2 & HO2 & Hfr2). autorewrite with btupd.
      exists R2, m. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HD|]. split; [lia|]. split; [exact HO2|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (Z.leb_spec (sel h j * 2) HLc) as [C4|C4].
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HR2 & Hfr2).
        specialize (IH R2 m1 m2 (arr_set h k (arr_get h (sel h j))) (sel h j * 2) (sel h j)
                       HD2 HR2 ltac:(lia) ltac:(lia) C4 ltac:(nia)).
        destruct (pqdownheap_loop f _ t node (sel h j) (sel h j * 2)) as [s' k'].
        destruct IH as (R3 & m3 & Hms3 & HD3 & Hk3 & HO3 & Hfr3).
        exists R3, m3. split.
        { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
        split; [exact HD3|]. split; [exact Hk3|]. split; [exact HO3|].
        intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HO2 & Hfr2).
        rewrite pqdownheap_loop_out by (autorewrite with btupd; lia). autorewrite with btupd.
        exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HD2|]. split; [lia|]. split; [exact HO2|].
        intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma x3_blk : forall regs m1 m h k,
  DI3 m1 m h -> X3REGS regs node k -> 1 <= k <= HLc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1bb90 : word) m s6_rom)
           (mkst R (if 1 <? HLc then (0x1bba8 : word) else (0x1be14 : word)) m' s6_rom)
    /\ DI3 m1 m' (arr_set h k node)
    /\ EREGS R HLc (node + 1) /\ FREGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h k HD HX Hk. pose proof HD as HD0. open_di HD.
  destruct HX as (HBx & P7). destruct HBx as (P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10).
  assert (P8' : getr regs 8 = zw (S + 2976)) by exact P8.
  destruct (Z.ltb_spec 1 HLc) as [C|C].
  - run5 20%nat [false] [RVal (EVar 37)] (EP5 ++ [(7, EVar 36)]) [S; T; 0; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [write1 m1 m h k node HD0 HRC MS HAG |];
        split; [unfold BuildTree6_4.EREGS; regs5' HR Hfr | split; [unfold FREGS; regs5' HR Hfr | fr_weak Hfr]]
    end.
  - run5 20%nat [true] [RVal (EVar 37)] (EP5 ++ [(7, EVar 36)]) [S; T; 0; 0; k; HLc; 0; 0; SP; MC; dsc_off t; node; 0; S + 2976; 0] FC h DP.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [write1 m1 m h k node HD0 HRC MS HAG |];
        split; [unfold BuildTree6_4.EREGS; regs5' HR Hfr | split; [unfold FREGS; regs5' HR Hfr | fr_weak Hfr]]
    end.
Qed.

Goal True. idtac "x3 OK". exact I. Qed.

End Pq3.


Lemma pq_flat : forall FC DL HP HL HM DP,
  pqdownheap (W6 FC DL HP HL HM DP) t 1 = W6 FC DL (ds_heap (pqdownheap (W6 FC DL HP HL HM DP) t 1)) HL HM DP.
Proof.
  intros. rewrite (pqdownheap_shape (W6 FC DL HP HL HM DP) t 1) at 1. rewrite bt_set_heap. reflexivity.
Qed.

Section Trip.
Variables (FC DL HP : arr) (HL HM : Z) (DP : arr) (node : Z).
Let n := arr_get HP 1.
Let HP1 := arr_set HP 1 (arr_get HP HL).
Let HP2 := ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM DP) t 1).
Let m_ := arr_get HP2 1.
Let FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)).
Let DL' := arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node).
Let HP3 := arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node.
Let DP' := arr_set DP node (wrap8 (dmax DP n m_ + 1)).
Definition trip : deflate_state := pqdownheap (W6 FC' DL' HP3 (HL - 1) (HM - 2) DP') t 1.

Lemma trip_flat : trip = W6 FC' DL' (ds_heap trip) (HL - 1) (HM - 2) DP'.
Proof. unfold trip. apply pq_flat. Qed.

Lemma L4_step : forall f,
  build_tree_loop4 (Datatypes.S f) (W6 FC DL HP HL HM DP) t node =
    if 2 <=? HL - 1 then build_tree_loop4 f trip t (node + 1) else trip.
Proof.
  intros f. cbn [build_tree_loop4]. unfold SMALLEST. autorewrite with btupd.
  rewrite (pq_flat FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP).
  fold HP1. fold HP2. autorewrite with btupd.
  unfold trip. subst n m_ FC' DL' HP3 DP'. fold HP1. fold HP2.
  rewrite pqdownheap_heap_len, bt_heap_len. unfold dmax.
  replace (HM - 1 - 1) with (HM - 2) by lia. reflexivity.
Qed.

Lemma e_trip : forall regs m1 m,
  EI m1 m FC DL HP HL HM DP -> 2 <= HL <= 572 -> 3 <= HM <= 573 -> 0 <= node < tsize t ->
  EREGS regs HL node ->
  exists R m',
    msteps s6_segs (mkst regs (0x1bba8 : word) m s6_rom)
           (mkst R (if 1 <? HL - 1 then (0x1bba8 : word) else (0x1be14 : word)) m' s6_rom)
    /\ EI m1 m' FC' DL' (ds_heap trip) (HL - 1) (HM - 2) DP'
    /\ EREGS R (HL - 1) (node + 1) /\ FREGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m HE Hhl Hhm Hnode HRE.
  pose proof Htt as Htt'. pose proof elems_range as He. pose proof tsize_elems as Hte.
  assert (Hn : 0 <= n < tsize t) by (subst n; apply (proj1 (proj1 (proj2 HE))); lia).
  destruct (e_remove _ _ _ _ _ _ _ _ _ _ HH BC OL SL MC Hmc regs m1 m FC DL HP HL HM DP node HE Hhl ltac:(lia) HRE)
    as (R1 & ma & Hms1 & HE1 & HR1 & Hfr1).
  fold HP1 in HE1. fold HP2 in HE1.
  assert (Hm : 0 <= m_ < tsize t) by (subst m_; apply (proj1 (proj1 (proj2 HE1))); lia).
  destruct (e2_blk R1 m1 ma FC DL HP2 (HL - 1) HM DP node n HE1 ltac:(lia) Hnode Hhm Hn HR1) as (R2 & mb & Hms2 & HE2 & HR2 & Hfr2).
  fold m_ in HE2, HR2. fold FC' in HE2. fold DL' in HE2. fold HP3 in HE2. fold DP' in HE2.
  unfold trip, pqdownheap. autorewrite with btupd.
  rewrite Z.shiftl_mul_pow2 by lia. change (1 * 2 ^ 1) with 2.
  assert (E31 : arr_get HP3 1 = node).
  { subst HP3. rewrite arr_get_set. unfold arr_inb. rewrite !arr_len_set.
    rewrite (proj2 (proj1 (proj2 HE1))). reflexivity. }
  rewrite E31.
  destruct (Z.ltb_spec (HL - 1) 2) as [C2|C2].
  -
    rewrite pqdownheap_loop_out by (autorewrite with btupd; lia). autorewrite with btupd.
    destruct (x3_blk FC' DL' (HL - 1) (HM - 2) DP' node ltac:(lia) Hnode R2 m1 mb HP3 1 HE2 HR2 ltac:(lia))
      as (R3 & mc & Hms3 & HE3 & HR3 & HF3 & Hfr3).
    exists R3, mc. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
    split; [exact HE3|]. split; [exact HR3|]. split; [exact HF3|].
    intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
  - pose proof (inner3b FC' DL' (HL - 1) (HM - 2) DP' node ltac:(lia) Hnode 32 R2 m1 mb HP3 2 1
                  HE2 HR2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(change (2 ^ Z.of_nat 32) with 4294967296; lia)) as HI.
    destruct (pqdownheap_loop 32 _ t node 1 2) as [s' k'].
    destruct HI as (R3 & mc & Hms3 & HD3 & Hk3 & HX3 & Hfr3).
    rewrite heap_set_shape, ds_heap_set_heap.
    destruct (x3_blk FC' DL' (HL - 1) (HM - 2) DP' node ltac:(lia) Hnode R3 m1 mc (ds_heap s') k' HD3 HX3 Hk3)
      as (R4 & md & Hms4 & HE4 & HR4 & HF4 & Hfr4).
    exists R4, md. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
    split; [exact HE4|]. split; [exact HR4|]. split; [exact HF4|].
    intros r Hr. rewrite (Hfr4 r Hr), (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.
End Trip.

Goal True. idtac "e_trip OK". exact I. Qed.


Lemma e_loop : forall f regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> EREGS regs HL node ->
  2 <= HL -> 2 * HL - 1 <= HM <= 573 -> 0 <= node -> node + HL <= tsize t ->
  HL - 1 <= Z.of_nat f ->
  exists R m' FC' DL' HP' HM' DP',
    build_tree_loop4 f (W6 FC DL HP HL HM DP) t node = W6 FC' DL' HP' 1 HM' DP'
    /\ msteps s6_segs (mkst regs (0x1bba8 : word) m s6_rom) (mkst R (0x1be14 : word) m' s6_rom)
    /\ EI m1 m' FC' DL' HP' 1 HM' DP'
    /\ FREGS R /\ HM' = HM - 2 * (HL - 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros regs m1 m FC DL HP HL HM DP node HE HRE Hhl Hhm Hn0 Hnh Hf; [lia|].
  pose proof Htt as Htt'. pose proof tsize_elems as Hte. pose proof elems_range as He.
  rewrite L4_step.
  destruct (e_trip FC DL HP HL HM DP node regs m1 m HE ltac:(lia) ltac:(lia) ltac:(lia) HRE)
    as (R1 & m2 & Hms1 & HE1 & HR1 & HF1 & Hfr1).
  destruct (Z.leb_spec 2 (HL - 1)) as [C|C].
  - replace (1 <? HL - 1) with true in Hms1 by (symmetry; apply Z.ltb_lt; lia).
    rewrite (trip_flat FC DL HP HL HM DP node).
    destruct (IH R1 m1 m2 _ _ _ (HL - 1) (HM - 2) _ (node + 1) HE1 HR1 C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & m3 & FC' & DL' & HP' & HM' & DP' & E2 & Hms2 & HE2 & HF2 & EHM & Hfr2).
    exists R2, m3, FC', DL', HP', HM', DP'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HE2|]. split; [exact HF2|]. split; [lia|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - replace (1 <? HL - 1) with false in Hms1 by (symmetry; apply Z.ltb_ge; lia).
    rewrite (trip_flat FC DL HP HL HM DP node). replace (HL - 1) with 1 in * by lia.
    eexists R1, m2, _, _, _, (HM - 2), _. split; [reflexivity|].
    split; [exact Hms1|]. split; [exact HE1|]. split; [exact HF1|]. split; [lia|]. exact Hfr1.
Qed.

End PhaseE.
End Walk.
End FXG.
