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
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 MemFill
  RomRead TreesRod BitsLib BuildTreeLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel TreesTab BuildTreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u TreesRod6u TreesApi6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_2b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word) (sp : Z).
Variable (t : tree_id).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation T := (S + toff t).
Local Abbreviation E := (sd_elems t).
Local Abbreviation SP := (sp - 208).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).
Local Abbreviation U := (bt_upd ds t).
Local Abbreviation SDA := (SDA R6u).
Local Abbreviation STP := (STP R6u).
Local Abbreviation EXP := (EXP R6u).
Local Abbreviation NT := (2 ^ 64 - 1 - (S + toff t)).
Local Abbreviation NHP := (2 ^ 64 - 1 - (S + 3008)).
Local Abbreviation NDP := (2 ^ 64 - 1 - (S + 5308)).

Hypothesis HH : BTH F mem0 mem S p PBL ds ra sp.

Let Hret : ret_ok ra := bth_ret _ _ _ _ _ _ _ _ _ HH.
Let HLb : BRH F S p PBL := bth_L _ _ _ _ _ _ _ _ _ HH.
Let HFS : sub_franges F S dsl_SIZE := bth_FS _ _ _ _ _ _ _ _ _ HH.
Let HS8 : S mod 8 = 0 := bth_al _ _ _ _ _ _ _ _ _ HH.
Let Hcf : call_frame F mem S PB PBL sp 272 := bth_fr _ _ _ _ _ _ _ _ _ HH.
Let HBR0 : BRm mem ds := bth_br _ _ _ _ _ _ _ _ _ HH.
Let HRC0 : trees_rod_clear6u mem := bth_rod _ _ _ _ _ _ _ _ _ HH.
Let Hsp : 272 <= sp <= 2 ^ 63 := proj1 Hcf.
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Abbreviation GB := (BuildTree6u_1.GB S sp).
Local Abbreviation CI := (BuildTree6u_1.CI F mem0 S p PBL sp).
Local Abbreviation FRM := (BuildTree6u_1.FRM sp).
Local Abbreviation LOC := (BuildTree6u_1.LOC S sp t).
Local Abbreviation stree_dl := (BuildTree6u_1.stree_dl t).
Local Abbreviation stF := (BuildTree6u_1.stF t).
Local Abbreviation L1REGS := (BuildTree6u_1.L1REGS S sp t).
Local Abbreviation X0 := (BuildTree6u_1.X0 ds t).
Local Abbreviation L1 := (BuildTree6u_1.L1 t).
Local Abbreviation tsize_elems := (BuildTree6u_1.tsize_elems t).
Local Abbreviation elems_range := (BuildTree6u_1.elems_range t).
Local Abbreviation dsc_off_val := (BuildTree6u_1.dsc_off_val t).
Local Abbreviation toff_mod4 := (BuildTree6u_1.toff_mod4 t).
Local Abbreviation SDA_range := (BuildTree6u_1.SDA_range t).
Local Abbreviation STP_range := (BuildTree6u_1.STP_range t).
Local Abbreviation EXP_range := (BuildTree6u_1.EXP_range t).
Local Abbreviation LOC_keep := (BuildTree6u_1.LOC_keep F mem0 mem S p PBL ds ra sp t HH).
Local Abbreviation L2 := (BuildTree6u_2.L2 t).
Local Abbreviation DREGS := (BuildTree6u_2.DREGS S sp t).
Local Abbreviation stree_Len_dl := (BuildTree6u_2.stree_Len_dl t).
Local Abbreviation c_disp := (BuildTree6u_2.c_disp F mem0 mem S p PBL ds ra sp t HH).
Local Abbreviation c_h1 := (BuildTree6u_2.c_h1 F mem0 mem S p PBL ds ra sp t HH).
Local Abbreviation c_h1n := (BuildTree6u_2.c_h1n F mem0 mem S p PBL ds ra sp t HH).
Local Abbreviation c_h2 := (BuildTree6u_2b.c_h2 F mem0 mem S p PBL ds ra sp t HH).
Local Abbreviation L2_hl1 := (BuildTree6u_2.L2_hl1 S ds t).
Local Abbreviation L2_hl0 := (BuildTree6u_2.L2_hl0 S ds t).
Local Abbreviation L2_ge2 := (BuildTree6u_2.L2_ge2 S ds t).
Local Abbreviation l2node := (BuildTree6u_2.l2node).


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac nf := cbn [BuildTree6u_1.stF].

Local Ltac vfix :=
  repeat match goal with H : hv ?hh ?e = _ |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with
         | H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H
         | H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H
         end.

Local Ltac zc :=
  change (2 ^ 3) with 8 in *;
  first [ lazymatch goal with
          | |- _ mod _ = 0 => keep_mod_facts; Z.to_euclidean_division_equations; lia
          end
        | zcond_close ].

Local Ltac side_closer :=
  try solve [ assumption
            | nf; vfix; first [ assumption | lia
                        | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; nf; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | nf; symex_read_auto
            | nf; vfix; symex_read_auto
            | nf; vfix; symex_store_auto
            | nf; vfix; symex_sok_auto
            | nf; vfix; zc
            | intros; nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia] ].

Local Ltac run_with C vb fuel dirs rds pins pv FC DL HP DP BC :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in vb in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs C fuel dirs rdv pinsv vbv NoRegions pv NoVals ((BuildTree6u_1.stF t) FC DL HP DP BC) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
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
  replace (match t with TL => 180992 | TD => 181024 | TB => 181056 end) with (SDA t) in Csd by (destruct t; reflexivity);
  let Cst := fresh "Cst" in let Cex := fresh "Cex" in let Cbase := fresh "Cbase" in let Celems := fresh "Celems" in let Cml := fresh "Cml" in
  destruct (sdesc_cells R6u _ _ trod_ok6u HRC t) as (Cst & Cex & Cbase & Celems & Cml);
  clear Hsc Har;
  let Hsp' := fresh "Hsp'" in pose proof Hsp as Hsp';
  let HS8' := fresh "HS8'" in pose proof HS8 as HS8';
  let Htt' := fresh "Htt'" in pose proof Htt as Htt';
  let Htm := fresh "Htm" in pose proof toff_mod4 as Htm;
  let He := fresh "He" in pose proof elems_range as He;
  let Hte := fresh "Hte" in pose proof tsize_elems as Hte;
  let Hdo := fresh "Hdo" in let Hdo8 := fresh "Hdo8" in pose proof dsc_off_val as Hdo; destruct Hdo as [Hdo Hdo8];
  let Hsda := fresh "Hsda" in let Hsda8 := fresh "Hsda8" in pose proof SDA_range as Hsda; destruct Hsda as [Hsda Hsda8];
  let Hstp := fresh "Hstp" in pose proof STP_range as Hstp;
  let RODS := fresh "RODS" in
  pose proof (mapped_rod_apart R6u _ _ S 5968 trod_ok6u HRC MS ltac:(lia) ltac:(lia)) as RODS;
  let RODF := fresh "RODF" in
  pose proof (mapped_rod_apart R6u _ _ (SP - 64) 272 trod_ok6u HRC MF ltac:(lia) ltac:(lia)) as RODF;
  cbn [tr_lo tr_hi tr_sdesc R6u] in RODS, RODF;
  lazymatch thin with
  | true => clear RODS RODF HD Cst Cex Cbase Celems Cml Cdyn Csd Hsda Hsda8; try clear HPB'
  | false => idtac
  end.
Local Ltac open_ci HC := open_ci_gen false HC.
Local Ltac open_ciT HC := open_ci_gen true HC.

Local Ltac ag_tower HAG :=
  repeat (apply agree_out_wbytes;
          [ | lia | rewrite ?length_Z_to_le_bytes; cbn; lia
            | rewrite ?length_Z_to_le_bytes; unfold BuildTree6u_1.GB;
              first [ apply sub_franges_here; unfold dsl_SIZE; cbn; lia
                    | apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia
                    | apply sub_franges_later; apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; cbn; lia ] ]);
  exact HAG.

Local Ltac rod_tower HRC MS MP MF :=
  apply (trees_rod_clear_wr R6u _ _ HRC);
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
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf; vfix;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; assumption
                  | apply zw_not; lia
                  | rewrite zw_not by lia; f_equal; lia
                  | lazymatch goal with |- zw ?a = zw ?b => lazymatch isZcst a with true => lazymatch isZcst b with true =>
                      apply bv_eq; vm_compute; reflexivity end end end
                  | idtac ] end ].
Local Ltac regs_of HR Hfr := repeat split; reg1 HR Hfr.

Local Ltac ci_tower HB HRC HAG MS MP MF HFf M ks :=
  br_fwdT HB M ks ltac:(oth HFf);
  lazymatch goal with
  | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
      split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; try reflexivity
             | split; [ rod_tower HRC MS MP MF
                      | split; [ ag_tower HAG
                               | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                 repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
  end.

Local Ltac blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf ks tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ ci_tower HB HRC HAG MS MP MF HFf M ks | tregs ]
  end.

Local Ltac nf_in H :=
  let T := type of H in let T' := eval cbn [BuildTree6u_1.stF] in T in symex_recast H T'.



Lemma c_phase : forall regs m1 m DL HP HL DP mc,
  let FC := tree_fc ds t in let BC := ds_bl_count ds in let OL := ds_opt_len ds in let SL := ds_static_len ds in
  let MC0 := max_code ds t in
  CI m1 m (U FC DL HP HL 573 DP BC OL SL MC0) -> LOC m1 ->
  0 <= HL <= E -> (mc = -1 /\ HL = 0 \/ 0 <= mc < E /\ 1 <= HL) ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536) ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  L1REGS regs E mc ->
  exists R m' FC2 HP2 HL2 DP2 OL2 SL2 mc2,
    L2 (U FC DL HP HL 573 DP BC OL SL MC0) mc = (U FC2 DL HP2 HL2 573 DP2 BC OL2 SL2 MC0, mc2)
    /\ msteps s6u_segs (mkst regs (0x1cbc4 : word) m s6u_rom) (mkst R (0x1cbd0 : word) m' s6u_rom)
    /\ CI m1 m' (U FC2 DL HP2 HL2 573 DP2 BC OL2 SL2 MC0)
    /\ DREGS R HL2 mc2
    /\ 2 <= HL2 <= E /\ 0 <= mc2 < E
    /\ arr_len FC2 = tsize t /\ arr_len HP2 = 573 /\ arr_len DP2 = 573
    /\ 0 <= OL2 < 2 ^ 64 /\ 0 <= SL2 < 2 ^ 64
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP HL DP mc FC BC OL SL MC0 HC HLOC Hhl Hinv RFC LFC LHP LDP ROL RSL HR0.
  pose proof elems_range as He. pose proof tsize_elems as Hte.
  assert (W64 : forall z, 0 <= wrap64 z < 2 ^ 64) by (intros z; apply wrap64_range).
  assert (FRT : forall (R1 R2 : bvmap 5 word) rs,
            (forall r : reg, reg_in r CLOBI = false -> getr R1 r = getr rs r) ->
            (forall r : reg, reg_in r CLOBI = false -> getr R2 r = getr R1 r) ->
            forall r : reg, reg_in r CLOBI = false -> getr R2 r = getr rs r).
  { intros R1 R2 rs H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). }
  destruct (c_disp DL 573 BC MC0 regs m1 m FC HP HL DP OL SL mc HC HLOC ltac:(lia) HR0) as (R0 & Hms0 & HX0 & Hfr0).
  destruct (Z.ltb_spec HL 2) as [Chl|Chl].
  2: {
    exists R0, m, FC, HP, HL, DP, OL, SL, mc. split; [apply L2_ge2; lia|].
    split; [exact Hms0|]. split; [exact HC|]. split; [exact HX0|].
    split; [lia|]. split; [lia|]. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [exact ROL|]. split; [exact RSL|]. exact Hfr0. }
  destruct (Z.eq_dec HL 1) as [Chl1|Chl1].
  -
    subst HL. assert (Hmc : 0 <= mc < E) by lia.
    rewrite (L2_hl1 DL 573 BC MC0 FC HP DP OL SL mc). unfold l2node.
    destruct (c_h1 DL 573 BC MC0 R0 m1 m FC HP 1 DP OL SL mc HC ltac:(lia) Hmc HX0) as (R1 & m2 & Hms1 & HC1 & HM1 & Hfr1).
    destruct (Z.ltb_spec mc 2) as [Cm|Cm]; cbv beta iota zeta; rewrite ?stree_Len_dl.
    + replace (mc <? 2) with true in HM1 by (symmetry; apply Z.ltb_lt; lia). cbv iota in HM1.
      destruct (c_h2 DL 573 BC MC0 R1 m1 m2 FC HP 1 DP OL SL (mc + 1) (mc + 1) HC1 HLOC ltac:(lia) ltac:(lia) ltac:(lia) LFC LHP LDP ROL RSL HM1)
        as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
      change (1 + 1 <? 2) with false in Hms2, HD2. change (1 + 1) with 2 in HC2, HD2. cbv iota in Hms2, HD2.
      eexists R2, m3, _, _, 2, _, _, _, (mc + 1). split; [reflexivity|].
      split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [exact Hms1 | exact Hms2]]|].
      split; [exact HC2|]. split; [exact HD2|].
      split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
      split; [apply W64|]. split; [destruct (stree_has t); [apply W64 | exact RSL]|].
      exact (FRT _ _ _ (FRT _ _ _ Hfr0 Hfr1) Hfr2).
    + replace (mc <? 2) with false in HM1 by (symmetry; apply Z.ltb_ge; lia). cbv iota in HM1.
      destruct (c_h2 DL 573 BC MC0 R1 m1 m2 FC HP 1 DP OL SL mc 0 HC1 HLOC ltac:(lia) ltac:(lia) ltac:(lia) LFC LHP LDP ROL RSL HM1)
        as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
      change (1 + 1 <? 2) with false in Hms2, HD2. change (1 + 1) with 2 in HC2, HD2. cbv iota in Hms2, HD2.
      eexists R2, m3, _, _, 2, _, _, _, mc. split; [reflexivity|].
      split; [eapply msteps_trans; [exact Hms0 | eapply msteps_trans; [exact Hms1 | exact Hms2]]|].
      split; [exact HC2|]. split; [exact HD2|].
      split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
      split; [apply W64|]. split; [destruct (stree_has t); [apply W64 | exact RSL]|].
      exact (FRT _ _ _ (FRT _ _ _ Hfr0 Hfr1) Hfr2).
  -
    assert (HL = 0) by lia. subst HL. assert (mc = -1) by lia. subst mc.
    rewrite (L2_hl0 DL 573 BC MC0 FC HP DP OL SL).
    destruct (c_h1n DL 573 BC MC0 R0 m1 m FC HP DP OL SL HC HX0) as (R1 & m2 & Hms1 & HC1 & HM1 & Hfr1).
    destruct (c_h2 DL 573 BC MC0 R1 m1 m2 FC HP 0 DP OL SL 0 0 HC1 HLOC ltac:(lia) ltac:(lia) ltac:(lia) LFC LHP LDP ROL RSL HM1)
      as (R2 & m3 & Hms2 & HC2 & HX2 & Hfr2).
    change (0 + 1 <? 2) with true in Hms2, HX2. change (0 + 1) with 1 in HC2, HX2. cbv iota in Hms2, HX2.
    assert (RSL1 : 0 <= (if stree_has t then wrap64 (SL - arr_get stree_dl 0) else SL) < 2 ^ 64) by (destruct (stree_has t); [apply W64 | exact RSL]).
    destruct (c_h1 DL 573 BC MC0 R2 m1 m3 _ _ 1 _ _ _ 0 HC2 ltac:(lia) ltac:(lia) HX2) as (R3 & m4 & Hms3 & HC3 & HM3 & Hfr3).
    change (0 <? 2) with true in HM3. cbv iota in HM3. change (0 + 1) with 1 in HM3.
    destruct (c_h2 DL 573 BC MC0 R3 m1 m4 _ _ 1 _ _ _ 1 1 HC3 HLOC ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite arr_len_set; exact LFC) ltac:(rewrite arr_len_set; exact LHP) ltac:(rewrite arr_len_set; exact LDP)
                (W64 _) RSL1 HM3)
      as (R4 & m5 & Hms4 & HC4 & HD4 & Hfr4).
    change (1 + 1 <? 2) with false in Hms4, HD4. change (1 + 1) with 2 in HC4, HD4. cbv iota in Hms4, HD4.
    rewrite !stree_Len_dl.
    eexists R4, m5, _, _, 2, _, _, _, 1. split; [reflexivity|].
    split.
    { eapply msteps_trans; [exact Hms0|]. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|].
      eapply msteps_trans; [exact Hms3 | exact Hms4]. }
    split; [exact HC4|]. split; [exact HD4|].
    split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
    split; [apply W64|]. split; [destruct (stree_has t); [apply W64 | exact RSL1]|].
    exact (FRT _ _ _ (FRT _ _ _ (FRT _ _ _ (FRT _ _ _ Hfr0 Hfr1) Hfr2) Hfr3) Hfr4).
Qed.

Goal True. idtac "c_phase OK". exact I. Qed.

End Walk.
End FXG.
