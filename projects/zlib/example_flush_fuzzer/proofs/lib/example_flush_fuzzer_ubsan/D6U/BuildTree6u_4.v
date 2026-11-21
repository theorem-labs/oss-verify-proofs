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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_3 BuildTree6u_pq BuildTree6u_pq2.
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
      split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT;
               try (first [reflexivity | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia])
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

Local Ltac dbg_left := idtac.

Local Ltac nf_in H :=
  let T := type of H in let T' := eval cbn [BuildTree6u_1.stF] in T in symex_recast H T'.



Definition stC4 : cfg :=
  CFG FB [] [EVar 1%nat] [0x1cc40; 0x1de0c; 0x1cdcc]
      [AV (EAdd (EVar 32) (EShl (EVar 37) 2)) 3008 4 2 (EVar 37);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 2 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EVar 39) 2)) 0 2 0 (EVar 39);
       AV (EAdd (EVar 33) (EShl (EVar 40) 2)) 0 2 0 (EVar 40);
       AV (EAdd (EVar 32) (EVar 39)) 5308 1 3 (EVar 39);
       AV (EAdd (EVar 32) (EVar 40)) 5308 1 3 (EVar 40);
       AV (EAdd (EVar 32) (EVar 36)) 5308 1 3 (EVar 36)].
Definition VB4 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300);
   (36%nat, 600); (37%nat, 600); (38%nat, 600); (39%nat, 600); (40%nat, 600); (41%nat, 2 ^ 63);
   (42%nat, 65536); (43%nat, 65536); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64);
   (47%nat, 2 ^ 64); (48%nat, 2 ^ 32); (49%nat, 3000); (50%nat, 2 ^ 64); (51%nat, 2 ^ 64)].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC4 VB4 fuel dirs rds pins pv FC DL HP DP BC.

Section PhaseE.
Variables (BC : arr) (OL SL MC : Z).
Local Abbreviation W6 FC DL HP HL HM DP := (U FC DL HP HL HM DP BC OL SL MC).
Hypothesis Hmc : 0 <= MC < 600.

Definition EB (R : bvmap 5 word) : Prop :=
  getr R 9 = zw 572 /\ getr R 18 = zw (S + 5308) /\ getr R 19 = zw (S + 3008) /\ getr R 22 = zw T
  /\ getr R 24 = zw (S + 2976) /\ getr R 25 = zw (S + 5300) /\ getr R 27 = zw NDP /\ getr R 2 = zw SP.
Definition EBP : list (Z * expr) :=
  [(9, ELit 572); (18, EAdd (EVar 32) (ELit 5308)); (19, EAdd (EVar 32) (ELit 3008)); (22, EVar 33);
   (24, EVar 41); (25, EAdd (EVar 32) (ELit 5300)); (27, EVar 45); (2, EVar 34)].
Definition EREGS (R : bvmap 5 word) (hl node : Z) : Prop :=
  EB R /\ getr R 10 = zw hl /\ getr R 8 = zw (T + node * 4) /\ getr R 21 = zw (T + node * 4)
  /\ getr R 20 = zw node /\ getr R 26 = zw node.
Definition ERP : list (Z * expr) :=
  EBP ++ [(10, EVar 37); (8, EAdd (EVar 33) (EShl (EVar 36) 2)); (21, EAdd (EVar 33) (EShl (EVar 36) 2)); (20, EVar 36); (26, EVar 36)].
Definition Q2REGS (R : bvmap 5 word) (node n : Z) : Prop :=
  EB R /\ getr R 8 = zw (T + node * 4) /\ getr R 21 = zw (T + node * 4) /\ getr R 20 = zw node /\ getr R 26 = zw node
  /\ getr R 23 = zw n
  /\ getr R 10 = zw S /\ getr R 11 = zw T /\ getr R 12 = zw 1 /\ getr R 1 = zw 0x1cc7c.
Definition X2REGS (R : bvmap 5 word) (node n : Z) : Prop :=
  EB R /\ getr R 8 = zw (T + node * 4) /\ getr R 21 = zw (T + node * 4) /\ getr R 20 = zw node /\ getr R 26 = zw node
  /\ getr R 23 = zw n.
Definition FREGS (R : bvmap 5 word) : Prop := EB R.

Definition RNG (FC DP : arr) : Prop :=
  (forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256)
  /\ arr_len FC = tsize t /\ arr_len DP = 573.

Definition PQ4 (HP : arr) (HL : Z) : Prop := (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < tsize t) /\ arr_len HP = 573.

Definition EI (m1 m : word -> option byte) (FC DL HP : arr) (HL HM : Z) (DP : arr) : Prop :=
  CI m1 m (W6 FC DL HP HL HM DP) /\ PQ4 HP HL /\ RNG FC DP /\ arr_len DL = tsize t.

Definition LOC2 (m : word -> option byte) : Prop := LOC m /\ cell s6u_segs m (SP + 64) 8 NHP /\ cell s6u_segs m (SP + 8) 8 MC.

Lemma LOC2_keep : forall m1 m, agree_out GB m1 m -> LOC2 m1 -> LOC2 m.
Proof.
  intros m1 m HAG (HL0 & C64 & C8). split; [exact (LOC_keep m1 m HAG HL0)|].
  pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'.
  split; (eapply BuildTree6u_1.loc_cell; [exact HH | exact HAG | unfold dsl_SIZE; lia | lia | assumption]).
Qed.

Lemma FRM_keep : forall m1 m regs0, agree_out GB m1 m -> FRM m1 regs0 -> FRM m regs0.
Proof.
  intros m1 m regs0 HAG HF.
  pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'.
  assert (K : forall a v, cell s6u_segs m1 a 8 v -> SP + 104 <= a /\ a + 8 <= SP + 208 -> cell s6u_segs m a 8 v).
  { intros a v Hc Ha. eapply BuildTree6u_1.loc_cell; [exact HH | exact HAG | unfold dsl_SIZE; lia | lia | exact Hc]. }
  unfold BuildTree6u_1.FRM in HF |- *.
  repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- cell _ _ ?a 8 _ =>
      apply K; [ (repeat match type of HF with _ /\ _ => let X := fresh in destruct HF as [X HF]; try exact X end); try exact HF | lia ] end.
Qed.

Local Ltac eregs HR Hfr := unfold EREGS, Q2REGS, X2REGS, FREGS, EB; repeat split; reg1 HR Hfr.


Lemma e0_blk : forall regs m1 m FC DL HP HL HM DP regs0,
  CI m1 m (W6 FC DL HP HL HM DP) -> LOC m1 -> cell s6u_segs m1 (SP + 8) 8 MC -> FRM m1 regs0 -> PQ4 HP HL -> RNG FC DP -> arr_len DL = tsize t -> 2 <= HL <= 572 ->
  BuildTree6u_3.EREGS S sp t regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1cc08 : word) m s6u_rom) (mkst R (0x1cc40 : word) m' s6u_rom)
    /\ EI m' m' FC DL HP HL HM DP
    /\ LOC2 m' /\ FRM m' regs0
    /\ EREGS R HL E
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP regs0 HC HLOC C8 HFRM HPQ HRN LDL Hhl HO.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC_keep m1 m HAG0 HLOC) as HLOCm. pose proof (FRM_keep m1 m regs0 HAG0 HFRM) as HFRMm.
  assert (C8m : cell s6u_segs m (SP + 8) 8 MC).
  { pose proof Hcf as (_ & _ & _ & HfS0 & _). unfold dsl_SIZE in HfS0. pose proof Hsp as Hsp0.
    eapply BuildTree6u_1.loc_cell; [exact HH | exact HAG0 | unfold dsl_SIZE; lia | lia | exact C8]. }
  pose proof HLOCm as (C16 & C56 & C40 & C32 & C24 & C48). clear HAG0.
  open_ciT HC. destruct HO as (P20 & P22 & P24 & P25 & P26 & P2).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run 30%nat NoDirs [RVal (EVar 37); RVal (EVar 35)]
      [(20, EVar 32); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976)); (25, EAdd (EVar 32) (ELit 5300)); (26, EAdd (EVar 32) (ELit 2047)); (2, EVar 34)]
      [S; T; SP; E; E; HL; 0; 0; 0; 0; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      br_fwdT HB M [KOther] ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
          split; [ split; [ split; [exact HB2 | split; [rod_tower HRC MS MP MF | split; [apply agree_out_refl | intros x Hx; apply wbytes_grows; apply MF; exact Hx]]]
                          | split; [exact HPQ | split; [exact HRN | exact LDL]] ] |]
      end
  end.
  split.
  { split.
    - unfold BuildTree6u_1.LOC in HLOCm |- *. repeat match goal with |- _ /\ _ => split end;
        (apply cell_write_other; [ | lia | cbn; lia | lia | cbn; lia | cbn; lia ]);
        repeat match type of HLOCm with _ /\ _ => let X := fresh in destruct HLOCm as [X HLOCm]; try exact X end; try exact HLOCm.
    - split.
      + apply cell_write_same_eqm; [lia | lia | cbn; lia|].
        apply Z_to_le_bytes_eqm. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). nf.
        rewrite lxor_m1_mod64 by lia. rewrite !Z.mod_small by lia. lia.
      + apply cell_write_other; [ exact C8m | lia | cbn; lia | lia | cbn; lia | cbn; lia ]. }
  split.
  { unfold BuildTree6u_1.FRM in HFRMm |- *. repeat match goal with |- _ /\ _ => split end;
      (apply cell_write_other; [ | lia | cbn; lia | lia | cbn; lia | cbn; lia ]);
      repeat match type of HFRMm with _ /\ _ => let X := fresh in destruct HFRMm as [X HFRMm]; try exact X end; try exact HFRMm. }
  split; [eregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "e0_blk OK". exact I. Qed.


Lemma e1_blk : forall regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> LOC2 m1 -> 2 <= HL <= 572 -> 0 <= node < 600 ->
  EREGS regs HL node ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1cc40 : word) m s6u_rom) (mkst R (0x1de0c : word) m' s6u_rom)
    /\ EI m1 m' FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP
    /\ Q2REGS R node (arr_get HP 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP node (HC & HPQ & HRN & LDL) HLOC Hhl Hnode HE.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ciT HC. destruct HE as ((P9 & P18 & P19 & P22 & P24 & P25 & P27 & P2) & P10 & P8 & P21 & P20 & P26).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HPQ as [HPQ1 LHP]. pose proof HRN as (RFC & RDP & LFC & LDP).
  assert (Rh : 0 <= arr_get HP HL < tsize t) by (apply HPQ1; lia).
  assert (R1 : 0 <= arr_get HP 1 < tsize t) by (apply HPQ1; lia).
  assert (Vh : hv HP HL = arr_get HP HL) by (apply hv_get; lia).
  assert (V1 : hv HP 1 = arr_get HP 1) by (apply hv_get; lia).
  run 40%nat [false; false; false] [RVal (EApp1 2 (ELit 1)); RVal (EVar 44); RVal (EVar 32)] ERP
      [S; T; SP; E; node; HL; 0; 0; 0; S + 2976; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
  nf_in Hms. rewrite !Vh in Hms.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M [KHl; KHeap 1] | ] |]
  end.
  { split.
    { split; [|rewrite arr_len_set; exact LHP]. intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite LHP.
      destruct (1 =? i), (0 <=? 1), (1 <? 573); cbn [andb]; apply HPQ1; lia. }
    split; [exact HRN | exact LDL]. }
  split; [eregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "e1_blk OK". exact I. Qed.

Lemma pq_flat : forall FC DL HP HL HM DP k,
  pqdownheap (W6 FC DL HP HL HM DP) t k = W6 FC DL (ds_heap (pqdownheap (W6 FC DL HP HL HM DP) t k)) HL HM DP.
Proof.
  intros. rewrite (pqdownheap_shape (W6 FC DL HP HL HM DP) t k) at 1. rewrite bt_set_heap. reflexivity.
Qed.

Lemma e_remove : forall regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> LOC2 m1 -> 2 <= HL <= 572 -> 0 <= node < 600 ->
  EREGS regs HL node ->
  let HP1 := arr_set HP 1 (arr_get HP HL) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1cc40 : word) m s6u_rom) (mkst R (0x1cc7c : word) m' s6u_rom)
    /\ EI m1 m' FC DL (ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM DP) t 1)) (HL - 1) HM DP
    /\ X2REGS R node (arr_get HP 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP node HE HLOC Hhl Hnode HRE. cbv zeta.
  destruct (e1_blk regs m1 m FC DL HP HL HM DP node HE HLOC Hhl Hnode HRE) as (R1 & ma & Hms1 & HE1 & HR1 & Hfr1).
  destruct HE1 as (HC1 & [HPQ1 LHP1] & HRN1 & LDL1). pose proof HRN1 as (RFC & RDP & LFC & LDP).
  destruct HR1 as (HB1 & P8 & P21 & P20 & P26 & P23 & P10 & P11 & P12 & P1).
  pose proof HB1 as (Q9 & Q18 & Q19 & Q22 & Q24 & Q25 & Q27 & Q2).
  assert (Hrq : ret_ok (zw 0x1cc7c)) by (apply ret_ok_lit; [lia | reflexivity]).
  destruct (BuildTree6u_pq2.pq_run _ _ _ _ _ _ _ _ _ _ HH FC DL (HL - 1) HM DP BC OL SL MC RFC RDP ltac:(lia) LFC LDP
              R1 m1 ma (arr_set HP 1 (arr_get HP HL)) 1 (zw 0x1cc7c)
              (conj HC1 (conj HPQ1 LHP1)) ltac:(lia) P10 P11 P12 Q2 P1 Hrq)
    as (R2 & mb & Hms2 & (HC2 & HPQ2 & LHP2) & W2 & Hfr2).
  symex_pc_lit_in Hms2.
  lazymatch type of Hms2 with
  | msteps _ _ (mkst _ _ _ (set_heap ?X ?hh)) => idtac
  | _ => idtac
  end.
  rewrite <- (pq_flat FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP 1) in HC2 |- * || idtac.
  exists R2, mb. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split.
  { split; [exact HC2|]. split; [split; [exact HPQ2 | exact LHP2]|]. split; [exact HRN1 | exact LDL1]. }
  split.
  { unfold X2REGS, EB. rewrite !Hfr2 by reflexivity. repeat split; assumption. }
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "e_remove OK". exact I. Qed.

End PhaseE.
End Walk.
End FXG.
