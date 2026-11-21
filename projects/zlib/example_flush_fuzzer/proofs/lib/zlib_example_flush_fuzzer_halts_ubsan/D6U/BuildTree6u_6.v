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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u TreesApi6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_3 BuildTree6u_4.
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



Definition FB6 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition stC6 : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x1ce34; 0x1cef8; 0x1cfb0; 0x1d23c]
      [AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 2 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EApp1 2 (EVar 38)) 2)) 2 2 1 (EApp1 2 (EVar 38))].

Definition VB6 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 16); (40%nat, 300); (41%nat, 600); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 63); (48%nat, 2 ^ 32); (49%nat, 3000);
   (50%nat, 2 ^ 63); (51%nat, 2 ^ 64)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC6 VB6 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).
Local Abbreviation NBC := (2 ^ 64 - 1 - (S + 2976)).

Lemma ml_range : 7 <= ML <= 15.
Proof. destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS; lia. Qed.
Lemma base_range : 0 <= BASE < 300 /\ BASE < E.
Proof. pose proof elems_range. destruct t; cbn in *; unfold LITERALS, L_CODES, LITERALS, LENGTH_CODES in *; lia. Qed.
Lemma EXP_span : 0x11ae0 <= EXP t /\ EXP t + 4 * (E - BASE) <= 0x12510 /\ EXP t mod 4 = 0.
Proof.
  destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; repeat split; try lia; reflexivity.
Qed.

Lemma extra_view_bound : forall x, 0 <= stF (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) (arr_make 1 0) 5%nat x < 16.
Proof.
  intros x. cbn [BuildTree6u_1.stF]. destruct t; cbn [sd_extra_bits].
  - pose proof (extra_lbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_dbits_bound x). rewrite Z.mod_small; lia.
  - pose proof (extra_blbits_bound x). rewrite Z.mod_small; lia.
Qed.
Lemma extra_view_bound' : forall FC DL HP DP BC x, 0 <= stF FC DL HP DP BC 5%nat x < 16.
Proof. intros. apply extra_view_bound. Qed.

Ltac side_closer ::=
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
            | intros; first [apply extra_view_bound' | nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia]] ].

Section PhaseF.
Variables (FC : arr) (DP : arr) (MC K : Z) (BC : arr) (OL SL : Z).
Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 2 <= K <= 571.

Local Abbreviation FREGS := (BuildTree6u_4.FREGS S sp t).
Local Abbreviation LOC2 := (BuildTree6u_4.LOC2 S sp t MC).
Local Abbreviation LOC2_keep := (BuildTree6u_4.LOC2_keep F mem0 mem S p PBL ds ra sp t HH MC).

Definition F2REGS (R : bvmap 5 word) : Prop :=
  getr R 10 = zw T /\ getr R 11 = zw MC /\ getr R 12 = zw ML /\ getr R 13 = zw (STP t) /\ getr R 14 = zw (EXP t)
  /\ getr R 15 = zw BASE /\ getr R 26 = zw (S + 5912)
  /\ getr R 19 = zw (S + 3008) /\ getr R 22 = zw T /\ getr R 24 = zw (S + 2976) /\ getr R 25 = zw (S + 5300)
  /\ getr R 27 = zw NDP /\ getr R 2 = zw SP.
Definition F2P : list (Z * expr) :=
  [(10, EVar 33); (11, EVar 37); (12, EVar 39); (13, EVar 48); (14, EVar 50); (15, EVar 40); (26, EAdd (EVar 32) (ELit 5912));
   (19, EAdd (EVar 32) (ELit 3008)); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976)); (25, EAdd (EVar 32) (ELit 5300));
   (27, EVar 45); (2, EVar 34)].
Definition F3REGS (R : bvmap 5 word) : Prop := F2REGS R /\ getr R 16 = zw (K - 1).
Definition GS (R : bvmap 5 word) (h ovf : Z) : Prop :=
  getr R 10 = zw T /\ getr R 11 = zw MC /\ getr R 12 = zw ML /\ getr R 13 = zw (STP t) /\ getr R 14 = zw (EXP t)
  /\ getr R 15 = zw BASE /\ getr R 26 = zw (S + 5912)
  /\ getr R 19 = zw (S + 3008) /\ getr R 22 = zw T /\ getr R 24 = zw (S + 2976)
  /\ getr R 27 = zw NDP /\ getr R 2 = zw SP
  /\ getr R 16 = zw NBC /\ getr R 17 = zw ovf /\ getr R 5 = zw 573 /\ getr R 6 = zw 573 /\ getr R 7 = zw NT
  /\ getr R 28 = zw (573 - h) /\ getr R 29 = zw (h * 4) /\ getr R 30 = zw 16.

Local Ltac fregs HR Hfr := unfold F2REGS, F3REGS, GS; repeat split; reg1 HR Hfr.


Lemma f1_blk : forall regs m1 m DL HP0,
  CI m1 m (U FC DL HP0 1 K DP BC OL SL MC) -> LOC2 m1 -> 0 <= arr_get HP0 1 < 573 -> arr_len HP0 = 573 ->
  FREGS regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1cdcc : word) m s6u_rom) (mkst R (0x1ce34 : word) m' s6u_rom)
    /\ CI m1 m' (U FC DL (arr_set HP0 (K - 1) (arr_get HP0 1)) 1 (K - 1) DP BC OL SL MC)
    /\ F2REGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP0 HC HLOC R1 LHP HF.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ci HC. destruct HF as (P9 & P18 & P19 & P22 & P24 & P25 & P27 & P2).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  assert (V1 : hv HP0 1 = arr_get HP0 1) by (apply hv_get; lia).
  assert (C4' : cell s6u_segs m (S + 5304) 4 (K - 1 + 1)) by (replace (K - 1 + 1) with K by lia; exact Chm).
  run 40%nat [false; false; false; false; false]
      [RVal (EAdd (EVar 38) (ELit 1)); RVal (EApp1 2 (ELit 1)); RVal (EVar 44); RVal (EAdd (EVar 32) (EVar 49)); RVal (EVar 47);
       RVal (EAdd (EVar 32) (ELit 5912)); RVal (EVar 33); RVal (EVar 37); RVal (EVar 48); RVal (EVar 50); RVal (EVar 40); RVal (EVar 39)]
      [(9, ELit 572); (18, EAdd (EVar 32) (ELit 5308)); (19, EAdd (EVar 32) (ELit 3008)); (22, EVar 33);
       (24, EVar 51); (25, EAdd (EVar 32) (ELit 5300)); (27, EVar 45); (2, EVar 34)]
      [S; T; SP; E; 0; MC; K - 1; ML; BASE; 0; 0; 0; NHP; NDP; NT; SDA t; STP t; dsc_off t; EXP t; S + 2976] FC DL HP0 DP BC.
  all: dbg_left.
  nf_in Hms. rewrite !V1 in Hms.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHm; KHeap (K - 1)] ltac:(split; [fregs HR Hfr | fr_weak Hfr]).
Qed.

Goal True. idtac "f1_blk OK". exact I. Qed.


Lemma f2_fill : forall regs m1 m DL HP,
  CI m1 m (U FC DL HP 1 (K - 1) DP BC OL SL MC) -> arr_len BC = 16 ->
  F2REGS regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1ce34 : word) m s6u_rom) (mkst R (0x1cef8 : word) m' s6u_rom)
    /\ CI m1 m' (U FC DL HP 1 (K - 1) DP (arr_fill BC 0 16 0) OL SL MC)
    /\ F3REGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP HC LBC HF.
  open_ciT HC. destruct HF as (P10 & P11 & P12 & P13 & P14 & P15 & P26 & P19 & P22 & P24 & P25 & P27 & P2).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp.
  assert (C4' : cell s6u_segs m (S + 5304) 4 (K - 1)) by exact Chm.
  run 60%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]
      [RVal (EVar 38)] F2P
      [S; T; SP; E; 0; MC; K - 1; ML; BASE; 0; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; EXP t; 0] FC DL HP DP BC.
  all: dbg_left.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M0 _) =>
      exists R, M0; split; [exact Hms|]; clear Hms; set (M := M0) in *
  end.
  assert (HF : Forall (cst_ok (S + 2976) (S + 3008))
            [(S + 3006, 2%nat); (S + 3004, 2%nat); (S + 3002, 2%nat); (S + 3000, 2%nat); (S + 2998, 2%nat); (S + 2996, 2%nat);
             (S + 2994, 2%nat); (S + 2992, 2%nat); (S + 2990, 2%nat); (S + 2988, 2%nat); (S + 2986, 2%nat); (S + 2984, 2%nat);
             (S + 2982, 2%nat); (S + 2980, 2%nat); (S + 2978, 2%nat); (S + 2976, 2%nat)]).
  { repeat constructor; cbn [fst snd]; lia. }
  assert (EM : M = ctower m (ms_bb 0)
            [(S + 3006, 2%nat); (S + 3004, 2%nat); (S + 3002, 2%nat); (S + 3000, 2%nat); (S + 2998, 2%nat); (S + 2996, 2%nat);
             (S + 2994, 2%nat); (S + 2992, 2%nat); (S + 2990, 2%nat); (S + 2988, 2%nat); (S + 2986, 2%nat); (S + 2984, 2%nat);
             (S + 2982, 2%nat); (S + 2980, 2%nat); (S + 2978, 2%nat); (S + 2976, 2%nat)]) by (subst M; reflexivity).
  assert (F0 : filled M (S + 2976) (S + 2976 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F1 : filled M (S + 2978) (S + 2978 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F2 : filled M (S + 2980) (S + 2980 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F3 : filled M (S + 2982) (S + 2982 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F4 : filled M (S + 2984) (S + 2984 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F5 : filled M (S + 2986) (S + 2986 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F6 : filled M (S + 2988) (S + 2988 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F7 : filled M (S + 2990) (S + 2990 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F8 : filled M (S + 2992) (S + 2992 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F9 : filled M (S + 2994) (S + 2994 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F10 : filled M (S + 2996) (S + 2996 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F11 : filled M (S + 2998) (S + 2998 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F12 : filled M (S + 3000) (S + 3000 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F13 : filled M (S + 3002) (S + 3002 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F14 : filled M (S + 3004) (S + 3004 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  assert (F15 : filled M (S + 3006) (S + 3006 + Z.of_nat 2) (ms_bb 0)) by (rewrite EM; eapply (ctower_filled m (ms_bb 0) (S + 2976) (S + 3008)); [exact HF | cbn; tauto]).
  pose proof F0 as J0.
  pose proof (filled_join _ _ _ _ _ _ J0 F1 ltac:(cbn; lia)) as J1.
  pose proof (filled_join _ _ _ _ _ _ J1 F2 ltac:(cbn; lia)) as J2.
  pose proof (filled_join _ _ _ _ _ _ J2 F3 ltac:(cbn; lia)) as J3.
  pose proof (filled_join _ _ _ _ _ _ J3 F4 ltac:(cbn; lia)) as J4.
  pose proof (filled_join _ _ _ _ _ _ J4 F5 ltac:(cbn; lia)) as J5.
  pose proof (filled_join _ _ _ _ _ _ J5 F6 ltac:(cbn; lia)) as J6.
  pose proof (filled_join _ _ _ _ _ _ J6 F7 ltac:(cbn; lia)) as J7.
  pose proof (filled_join _ _ _ _ _ _ J7 F8 ltac:(cbn; lia)) as J8.
  pose proof (filled_join _ _ _ _ _ _ J8 F9 ltac:(cbn; lia)) as J9.
  pose proof (filled_join _ _ _ _ _ _ J9 F10 ltac:(cbn; lia)) as J10.
  pose proof (filled_join _ _ _ _ _ _ J10 F11 ltac:(cbn; lia)) as J11.
  pose proof (filled_join _ _ _ _ _ _ J11 F12 ltac:(cbn; lia)) as J12.
  pose proof (filled_join _ _ _ _ _ _ J12 F13 ltac:(cbn; lia)) as J13.
  pose proof (filled_join _ _ _ _ _ _ J13 F14 ltac:(cbn; lia)) as J14.
  pose proof (filled_join _ _ _ _ _ _ J14 F15 ltac:(cbn; lia)) as J15.
  pose proof (ctower_same m (ms_bb 0) (S + 2976) (S + 3008) _ HF) as Hsame. rewrite <- EM in Hsame.
  assert (Hfill : filled M (S + 2976) (S + 2976 + 32) (ms_bb 0)) by (eapply filled_sub; [exact J15 | lia | cbn; lia]).
  replace (S + 3008) with (S + 2976 + 32) in Hsame by lia.
  split.
  { split; [| split; [ subst M; rod_tower HRC MS MP MF | split; [ subst M; ag_tower HAG | intros x Hx; subst M; repeat (apply wbytes_grows); apply MF; exact Hx ] ] ].
    apply (BRT_blc_fill _ _ _ _ F mem0 S p PBL HLb HFS ds t m M FC DL HP 1 (K - 1) DP BC OL SL MC HB LBC Hfill Hsame).
    intros x Hx. subst M. repeat (apply wbytes_grows). exact Hx. }
  split; [fregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "f2_fill OK". exact I. Qed.


Lemma shl32_shr30 : forall x, 0 <= x -> x * 2 ^ 32 / 2 ^ 30 = x * 4.
Proof. intros x Hx. replace (x * 2 ^ 32) with (x * 4 * 2 ^ 30) by lia. apply Z.div_mul. lia. Qed.

Lemma f3_blk : forall regs m1 m DL HP BC',
  CI m1 m (U FC DL HP 1 (K - 1) DP BC' OL SL MC) -> LOC2 m1 -> arr_len HP = 573 ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536) -> arr_len DL = tsize t ->
  F3REGS regs ->
  let h1 := arr_get HP (K - 1) in
  0 <= h1 < tsize t ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1cef8 : word) m s6u_rom) (mkst R (0x1cfb0 : word) m' s6u_rom)
    /\ CI m1 m' (U FC (arr_set DL h1 (wrap16 0)) HP 1 (K - 1) DP BC' OL SL MC)
    /\ GS R K 0
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP BC' HC HLOC LHP RDL LDL HF h1 Rh1.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC2_keep m1 m HAG0 HLOC) as ((C16 & C56 & C40 & C32 & C24 & C48) & C64 & C8). clear HAG0.
  open_ciT HC. destruct HF as ((P10 & P11 & P12 & P13 & P14 & P15 & P26 & P19 & P22 & P24 & P25 & P27 & P2) & P16).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as Hexp. pose proof STP_range as Hstp'.
  assert (Vh1 : hv HP (K - 1) = h1) by (subst h1; apply hv_get; lia).
  assert (Vl : pb DL h1 = arr_get DL h1) by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; lia]).
  run 40%nat [false; false; false; false; false; false; false; false]
      [RVal (EVar 44); RVal (EVar 38)] (F2P ++ [(16, EVar 38)])
      [S; T; SP; E; 0; MC; K - 1; ML; BASE; 0; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; EXP t; 0] FC DL HP DP BC'.
  all: dbg_left.
  nf_in Hms. rewrite !Vh1 in Hms.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KDl h1] ltac:(split; [fregs HR Hfr | fr_weak Hfr]).
  all: f_equal; replace ((K - 1) * 2 ^ 32 + 4294967296) with (K * 2 ^ 32) by lia; rewrite shl32_shr30 by lia; lia.
Qed.

Goal True. idtac "f3_blk OK". exact I. Qed.

End PhaseF.
End Walk.
End FXG.
