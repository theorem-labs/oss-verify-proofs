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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2.
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
Local Abbreviation DREGS := (BuildTree6_2.DREGS S sp t).
Local Abbreviation L2 := (BuildTree6_2.L2 t).
Local Abbreviation slen := (BuildTree6_2.slen t).

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


Definition pqF3 (FC HP DP : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb FC x | 1%nat => hv HP x | _ => wb DP x end.

Definition stC3 : cfg :=
  CFG [(0%nat, 65536); (1%nat, 573); (2%nat, 256)] [] [EVar 1%nat] [0x1ba70; 0x1bac4; 0x1bb30; 0x1bb68]
      [AV (EAdd (EVar 32) (EShl (EVar 34) 2)) 3008 4 1 (EVar 34);
       AV (EAdd (EVar 32) (EShl (EOr (EVar 34) (ELit 1)) 2)) 3008 4 1 (EOr (EVar 34) (ELit 1));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 34)) 2)) 0 2 0 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EOr (EVar 34) (ELit 1))) 2)) 0 2 0 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EApp1 1 (EVar 34))) 5308 1 2 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 32) (EApp1 1 (EOr (EVar 34) (ELit 1)))) 5308 1 2 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EVar 35)) 5308 1 2 (EVar 35);
       AV (EAdd (EVar 32) (EApp1 1 (EVar 38))) 5308 1 2 (EApp1 1 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EVar 35) 2)) 0 2 0 (EVar 35);
       AV (EAdd (EVar 32) (EShl (EVar 39) 2)) 3008 4 1 (EVar 39);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 1 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 38)) 2)) 0 2 0 (EApp1 1 (EVar 38))].

Definition VB3 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600);
   (39%nat, 600); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 3000); (43%nat, 300)].

Definition OP : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
   (10, EVar 43); (11, EAdd (EVar 32) (EVar 42)); (8, EAdd (EVar 32) (ELit 2976)); (22, EAdd (EVar 32) (ELit 3008));
   (12, EAdd (EVar 32) (ELit 5308)); (13, ELit 1); (19, EVar 41); (2, EVar 40)].
Definition HB3 : list (Z * expr) :=
  OP ++ [(14, EVar 39); (15, EVar 35); (16, EAdd (EAdd (EVar 32) (EVar 35)) (ELit 5308)); (17, EAdd (EVar 33) (EShl (EVar 35) 2))].
Definition HP3 : list (Z * expr) :=
  HB3 ++ [(5, EVar 36); (7, EVar 36); (6, EVar 34); (28, EVar 37)].
Definition MP3 : list (Z * expr) :=
  HB3 ++ [(5, EVar 36); (6, EVar 38); (7, EVar 38)].

Lemma lor1_even : forall k, 0 <= k -> Z.lor (k * 2) 1 = k * 2 + 1.
Proof.
  intros k Hk.
  assert (L : Z.land (k * 2) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    rewrite Z.mul_comm, Z.mul_mod by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Section PhaseD.
Variables (FC DL : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Abbreviation W h := (U FC DL h HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis RDP : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.
Hypothesis Hhl : 2 <= HL <= 572.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LDP : arr_len DP = 573.
Hypothesis Hmc : 0 <= MC < 600.

Definition smal (n m : Z) : bool :=
  (arr_get FC n <? arr_get FC m) || ((arr_get FC n =? arr_get FC m) && (arr_get DP n <=? arr_get DP m)).

Lemma smaller_W : forall h n m, smaller (W h) t n m = smal n m.
Proof. intros. unfold smaller, smal. autorewrite with btupd. reflexivity. Qed.

Definition sel3 (h : arr) (j : Z) : Z :=
  if (j <? HL) && smal (arr_get h (j + 1)) (arr_get h j) then j + 1 else j.

Lemma sel3_range : forall h j, 1 <= j <= HL -> j <= sel3 h j <= HL /\ sel3 h j <= j + 1.
Proof.
  intros h j Hj. unfold sel3. destruct (Z.ltb_spec j HL); cbn [andb]; [destruct (smal _ _)|]; lia.
Qed.

Definition PQ (h : arr) : Prop := forall i, 1 <= i <= HL -> 0 <= arr_get h i < tsize t.

Definition DI (m1 m : word -> option byte) (h : arr) : Prop :=
  CI m1 m (W h) /\ PQ h /\ arr_len h = 573.

Definition OREGS (R : bvmap 5 word) (nn : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 21 = zw (S + 2047)
  /\ getr R 10 = zw E /\ getr R 11 = zw (S + dsc_off t) /\ getr R 8 = zw (S + 2976) /\ getr R 22 = zw (S + 3008)
  /\ getr R 12 = zw (S + 5308) /\ getr R 13 = zw 1 /\ getr R 19 = zw MC /\ getr R 2 = zw SP
  /\ getr R 15 = zw nn.

Definition BREGS3 (R : bvmap 5 word) (v n : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 21 = zw (S + 2047)
  /\ getr R 10 = zw E /\ getr R 11 = zw (S + dsc_off t) /\ getr R 8 = zw (S + 2976) /\ getr R 22 = zw (S + 3008)
  /\ getr R 12 = zw (S + 5308) /\ getr R 13 = zw 1 /\ getr R 19 = zw MC /\ getr R 2 = zw SP
  /\ getr R 14 = zw n /\ getr R 15 = zw v /\ getr R 16 = zw (S + 5308 + v) /\ getr R 17 = zw (T + v * 4).

Definition HREGS3 (R : bvmap 5 word) (v j k n : Z) : Prop :=
  BREGS3 R v n /\ getr R 5 = zw k /\ getr R 7 = zw k /\ getr R 6 = zw j /\ getr R 28 = zw HL.

Definition MREGS3 (R : bvmap 5 word) (v j k j' n : Z) : Prop :=
  BREGS3 R v n /\ getr R 5 = zw k /\ getr R 6 = zw j' /\ getr R 7 = zw j'.


Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : PQ h |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb FC (arr_get h i) = arr_get FC (arr_get h i)) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]);
  assert (PD : wb DP (arr_get h i) = arr_get DP (arr_get h i)) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).

Local Ltac nflor :=
  cbn [pqF3];
  repeat match goal with H : Z.lor ?a 1 = _ |- context [Z.lor ?a 1] => rewrite !H end.
Local Ltac nf3 :=
  nflor;
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac side_closer3 :=
  try solve [ assumption
            | nf3; first [ assumption | lia | rewrite ?Z.mod_small by lia; lia
                         | repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; nf3; lia end
            | nflor; symex_read_auto
            | nf3; symex_store_auto
            | intros; cbn [pqF3]; first [apply pb_range | apply hv_range | apply wb_range] ].

Local Ltac run3 fuel dirs rds pins pv h :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB3 in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs stC3 fuel dirs rds pinsv vbv NoRegions pv NoVals (pqF3 FC h DP) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer3
  end.

Local Ltac hregs3 HR :=
  let A := fresh "A" in
  unfold MREGS3, HREGS3, BREGS3, OREGS;
  repeat match goal with
  | |- _ /\ _ => split
  | |- getr ?R ?r = _ =>
      symex_reg HR r as A; rewrite A; cbn [pqF3]; first [reflexivity | assumption | f_equal; nf3; lia | nf3; assumption]
  end.

Local Ltac open_di HD :=
  let HC := fresh "HC" in let HPQ := fresh "HPQ" in let HLh := fresh "HLh" in
  destruct HD as (HC & HPQ & HLh); open_ciT HC.

Local Ltac open_b3 H :=
  let H' := fresh "BR'" in pose proof H as H';
  destruct H' as (P9 & P18 & P20 & P21 & P10 & P11 & P8 & P22 & P12 & P13 & P19 & P2 & P14 & P15 & P16 & P17).
Local Ltac open_h3 H :=
  let H' := fresh "HR'" in pose proof H as H';
  destruct H' as (HB' & P5 & P7 & P6 & P28); open_b3 HB'.
Local Ltac open_m3 H :=
  let H' := fresh "MR'" in pose proof H as H';
  destruct H' as (HB' & P5 & P6 & P7); open_b3 HB'.


Lemma d_start : forall regs m1 m h n,
  DI m1 m h -> OREGS regs n -> 1 <= n -> n * 2 <= HL ->
  exists R, msteps s6_segs (mkst regs (0x1ba70 : word) m s6_rom) (mkst R (0x1bac4 : word) m s6_rom)
    /\ HREGS3 R (arr_get h n) (n * 2) n n
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h n HD HO Hn1 Hn2. open_di HD.
  destruct HO as (P9 & P18 & P20 & P21 & P10 & P11 & P8 & P22 & P12 & P13 & P19 & P2 & P15).
  node h n Vn Rn PFn PDn.
  run3 30%nat [false] [RVal (EVar 37)] (OP ++ [(15, EVar 39)]) [S; T; 0; 0; 0; HL; 0; n; SP; MC; dsc_off t; E] h.
  exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
Qed.

Goal True. idtac "d_start OK". exact I. Qed.


Lemma h3_step : forall regs m1 m h v j k n,
  DI m1 m h -> HREGS3 regs v j k n -> 1 <= k -> j = k * 2 -> j <= HL -> 0 <= v < tsize t -> 1 <= n < 300 ->
  exists R, msteps s6_segs (mkst regs (0x1bac4 : word) m s6_rom) (mkst R (0x1bb30 : word) m s6_rom)
    /\ MREGS3 R v j k (sel3 h j) n
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h v j k n HD HRg Hk Hjk Hj Hv Hn. open_di HD. open_h3 HRg.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  assert (PFv : pb FC v = arr_get FC v) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
  pose proof (lor1_even k ltac:(lia)) as Hj1. rewrite <- Hjk in Hj1.
  node h j Vj Rj PFj PDj.
  unfold sel3.
  destruct (Z.ltb_spec j HL) as [Cj|Cj]; cbn [andb].
  - node h (j + 1) Vj1 Rj1 PFj1 PDj1.
    assert (Vj1' : hv h (Z.lor j 1) = arr_get h (j + 1)) by (rewrite Hj1; exact Vj1).
    unfold smal.
    destruct (Z.ltb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C1|C1]; cbn [orb].
    + run3 40%nat [false; false] NoReads HP3 [S; T; j; v; k; HL; 0; n; SP; MC; dsc_off t; E] h.
      exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
    + destruct (Z.eqb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C2|C2]; cbn [andb].
      * destruct (Z.leb_spec (arr_get DP (arr_get h (j + 1))) (arr_get DP (arr_get h j))) as [C3|C3].
        -- run3 40%nat [false; true; false; true] NoReads HP3 [S; T; j; v; k; HL; 0; n; SP; MC; dsc_off t; E] h.
           exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
        -- run3 40%nat [false; true; false; false] NoReads HP3 [S; T; j; v; k; HL; 0; n; SP; MC; dsc_off t; E] h.
           exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
      * run3 40%nat [false; true; true] NoReads HP3 [S; T; j; v; k; HL; 0; n; SP; MC; dsc_off t; E] h.
        exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
  - run3 40%nat [true] NoReads HP3 [S; T; j; v; k; HL; 0; n; SP; MC; dsc_off t; E] h.
    exists R. split; [exact Hms|]. split; [hregs3 HR | fr_weak Hfr].
Qed.


Definition endpc (n : Z) : word := if n =? 1 then (0x1bb68 : word) else (0x1ba70 : word).

Lemma DI_write : forall m1 m h i x x' a,
  DI m1 m h -> trees_rod_clear6 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  agree_out GB m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  1 <= i <= HL -> 0 <= x < tsize t -> a = S + 3008 + 4 * i -> x' = x ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) (arr_set h i x).
Proof.
  intros m1 m h i x x' a (HC & HPQ & HLh) HRC' HAG' Hi Hx Ha ->. destruct HC as (HB & HRC & HAG & MF).
  pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'. pose proof HLb as (HS' & _). unfold dsl_SIZE in HS'.
  split; [|split].
  - split; [| split; [exact HRC' | split; [exact HAG' | apply mapped_wbytes; exact MF]]].
    apply (BRT_heap _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | exact Ha | lia].
  - intros q Hq. rewrite arr_get_set. unfold arr_inb. rewrite HLh.
    destruct (i =? q), (0 <=? i), (i <? 573); cbn [andb]; try lia; apply HPQ; lia.
  - rewrite arr_len_set. exact HLh.
Qed.

Local Ltac oregs_fin HR Hfr :=
  unfold OREGS; repeat split;
  (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; cbn [pqF3];
     first [reflexivity | assumption | f_equal; nf3; repeat (rewrite (szwrap_small 32) by lia); lia] end).

Local Ltac exit_fin Hms HR Hfr writes :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ writes
             | split; [oregs_fin HR Hfr | fr_weak Hfr] ]
  end.

Local Ltac rod1 HRC MS := apply (trees_rod_clear_wbytes R6 _ _ _ HRC); [intros x Hx; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia].
Local Ltac ag1 HAG := apply agree_out_wbytes; [exact HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia].

Local Ltac write1 m1 m h k x HD0 HRC MS HAG :=
  apply (DI_write m1 m h k x); [exact HD0 | rod1 HRC MS | ag1 HAG | lia | lia | lia | nf3; first [reflexivity | lia]].
Local Ltac write2 m1 m h k j' v HD0 HRC MS HAG :=
  apply (DI_write m1 _ (arr_set h k (arr_get h j')) j' v);
    [ write1 m1 m h k (arr_get h j') HD0 HRC MS HAG
    | apply (trees_rod_clear_wbytes R6); [rod1 HRC MS | intros x Hx; apply wbytes_grows; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia]
    | apply agree_out_wbytes; [ag1 HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia]
    | lia | lia | lia | nf3; first [reflexivity | lia] ].

Lemma m3_step : forall regs m1 m h v j k j' n,
  DI m1 m h -> MREGS3 regs v j k j' n -> 1 <= k < j -> j <= j' <= HL -> j' <= j + 1 -> 0 <= v < tsize t -> 1 <= n < 300 ->
  if smal v (arr_get h j') then
    exists R m', msteps s6_segs (mkst regs (0x1bb30 : word) m s6_rom) (mkst R (endpc n) m' s6_rom)
      /\ DI m1 m' (arr_set h k v)
      /\ OREGS R (n - 1)
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else if j' * 2 <=? HL then
    exists R m', msteps s6_segs (mkst regs (0x1bb30 : word) m s6_rom) (mkst R (0x1bac4 : word) m' s6_rom)
      /\ DI m1 m' (arr_set h k (arr_get h j'))
      /\ HREGS3 R v (j' * 2) j' n
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else
    exists R m', msteps s6_segs (mkst regs (0x1bb30 : word) m s6_rom) (mkst R (endpc n) m' s6_rom)
      /\ DI m1 m' (arr_set (arr_set h k (arr_get h j')) j' v)
      /\ OREGS R (n - 1)
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h v j k j' n HD HMR Hkj Hj Hj1 Hv Hn. pose proof HD as HD0. open_di HD. open_m3 HMR.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  assert (PFv : pb FC v = arr_get FC v) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
  assert (PDv : wb DP v = arr_get DP v) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).
  node h j' Vj' Rj' PFj' PDj'.
  unfold smal, endpc.
  destruct (Z.ltb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C1|C1]; cbn [orb].
  -
    destruct (Z.eqb_spec n 1) as [Cn|Cn].
    + run3 40%nat [true; true] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
      exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
    + run3 40%nat [true; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
      exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
  - destruct (Z.eqb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C2|C2]; cbn [andb].
    + destruct (Z.leb_spec (arr_get DP v) (arr_get DP (arr_get h j'))) as [C3|C3].
      *
        destruct (Z.eqb_spec n 1) as [Cn|Cn].
        -- run3 40%nat [false; false; false; true] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
           exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
        -- run3 40%nat [false; false; false; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
           exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
      * destruct (Z.leb_spec (j' * 2) HL) as [C4|C4].
        --
           run3 40%nat [false; false; true; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [hregs3 HR | fr_weak Hfr]
           end.
        --
           destruct (Z.eqb_spec n 1) as [Cn|Cn].
           ++ run3 40%nat [false; false; true; true; true] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
              exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
           ++ run3 40%nat [false; false; true; true; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
              exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
    + destruct (Z.leb_spec (j' * 2) HL) as [C4|C4].
      *
        run3 40%nat [false; true; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [hregs3 HR | fr_weak Hfr]
        end.
      * destruct (Z.eqb_spec n 1) as [Cn|Cn].
        -- run3 40%nat [false; true; true; true] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
           exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
        -- run3 40%nat [false; true; true; false] [RVal (EVar 37)] MP3 [S; T; j; v; k; HL; j'; n; SP; MC; dsc_off t; E] h.
           exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
Qed.

Goal True. idtac "m3_step OK". exact I. Qed.


Lemma loop3_S_sel : forall f h v k j, j <= HL ->
  pqdownheap_loop (Datatypes.S f) (W h) t v k j =
    if smal v (arr_get h (sel3 h j)) then (W h, k)
    else pqdownheap_loop f (W (arr_set h k (arr_get h (sel3 h j)))) t v (sel3 h j) (sel3 h j * 2).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. autorewrite with btupd.
  replace (j <=? HL) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  autorewrite with btupd. rewrite !smaller_W. unfold sel3.
  destruct ((j <? HL) && smal (arr_get h (j + 1)) (arr_get h j)).
  - destruct (smal v (arr_get h (j + 1))); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
  - destruct (smal v (arr_get h j)); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
Qed.

Lemma inner3 : forall fuel regs m1 m h v j k n,
  DI m1 m h -> HREGS3 regs v j k n -> 1 <= k -> j = k * 2 -> j <= HL -> 0 <= v < tsize t -> 1 <= n < 300 ->
  HL < j * 2 ^ Z.of_nat fuel ->
  let '(s', k') := pqdownheap_loop fuel (W h) t v k j in
  exists R m', msteps s6_segs (mkst regs (0x1bac4 : word) m s6_rom) (mkst R (endpc n) m' s6_rom)
    /\ DI m1 m' (arr_set (ds_heap s') k' v)
    /\ OREGS R (n - 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction fuel as [|f IH]; intros regs m1 m h v j k n HD HRg Hk Hjk Hj Hv Hn Hfuel.
  - exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
    rewrite loop3_S_sel by lia.
    pose proof (sel3_range h j ltac:(lia)) as Hsel.
    destruct (h3_step regs m1 m h v j k n HD HRg Hk Hjk Hj Hv Hn) as (R1 & Hms1 & HM1 & Hfr1).
    pose proof (m3_step R1 m1 m h v j k (sel3 h j) n HD HM1 ltac:(lia) ltac:(lia) ltac:(lia) Hv Hn) as HB.
    destruct (smal v (arr_get h (sel3 h j))).
    + destruct HB as (R2 & m2 & Hms2 & HD2 & HO2 & Hfr2). autorewrite with btupd.
      exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HD2|]. split; [exact HO2|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (Z.leb_spec (sel3 h j * 2) HL) as [C4|C4].
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HR2 & Hfr2).
        specialize (IH R2 m1 m2 (arr_set h k (arr_get h (sel3 h j))) v (sel3 h j * 2) (sel3 h j) n
                       HD2 HR2 ltac:(lia) ltac:(lia) C4 Hv Hn ltac:(nia)).
        destruct (pqdownheap_loop f _ t v (sel3 h j) (sel3 h j * 2)) as [s' k'].
        destruct IH as (R3 & m3 & Hms3 & HD3 & HO3 & Hfr3).
        exists R3, m3. split.
        { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
        split; [exact HD3|]. split; [exact HO3|].
        intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HO2 & Hfr2).
        rewrite pqdownheap_loop_out by (autorewrite with btupd; lia). autorewrite with btupd.
        exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HD2|]. split; [exact HO2|].
        intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma pq_n : forall regs m1 m h n,
  DI m1 m h -> OREGS regs n -> 1 <= n -> n * 2 <= HL ->
  exists R m', msteps s6_segs (mkst regs (0x1ba70 : word) m s6_rom) (mkst R (endpc n) m' s6_rom)
    /\ DI m1 m' (ds_heap (pqdownheap (W h) t n))
    /\ OREGS R (n - 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h n HD HO Hn1 Hn2.
  pose proof HD as (_ & HPQ & HLh).
  assert (Rv : 0 <= arr_get h n < tsize t) by (apply HPQ; lia).
  destruct (d_start regs m1 m h n HD HO Hn1 Hn2) as (R1 & Hms1 & HR1 & Hfr1).
  pose proof (inner3 32 R1 m1 m h (arr_get h n) (n * 2) n n HD HR1 ltac:(lia) ltac:(lia) Hn2 Rv ltac:(lia)
                ltac:(change (2 ^ Z.of_nat 32) with 4294967296; lia)) as HI.
  unfold pqdownheap. autorewrite with btupd. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (pqdownheap_loop 32 (W h) t (arr_get h n) n (n * 2)) as [s' k'].
  destruct HI as (R2 & m2 & Hms2 & HD2 & HO2 & Hfr2).
  rewrite heap_set_shape, ds_heap_set_heap.
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  split; [exact HD2|]. split; [exact HO2|].
  intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Definition L3 (h : arr) (n : Z) : deflate_state := build_tree_loop3 (Z.to_nat n) (W h) t n.

Lemma outer3 : forall k n regs m1 m h,
  n <= Z.of_nat k -> DI m1 m h -> OREGS regs n -> 1 <= n -> n * 2 <= HL ->
  exists R m' h', L3 h n = W h'
    /\ msteps s6_segs (mkst regs (0x1ba70 : word) m s6_rom) (mkst R (0x1bb68 : word) m' s6_rom)
    /\ DI m1 m' h'
    /\ OREGS R 0
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros n regs m1 m h Hk HD HO Hn1 Hn2; [lia|].
  unfold L3. replace (Z.to_nat n) with (Datatypes.S (Z.to_nat (n - 1))) by lia.
  cbn [build_tree_loop3]. replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (pqdownheap_shape (W h) t n). autorewrite with btupd.
  destruct (pq_n regs m1 m h n HD HO Hn1 Hn2) as (R1 & m2 & Hms1 & HD1 & HO1 & Hfr1).
  unfold endpc in Hms1. destruct (Z.eqb_spec n 1) as [Cn|Cn].
  - rewrite Cn in *. replace (Z.to_nat (1 - 1)) with 0%nat by lia. cbn [build_tree_loop3].
    eexists R1, m2, _. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HD1|]. split; [exact HO1 | exact Hfr1].
  - destruct (IH (n - 1) R1 m1 m2 _ ltac:(lia) HD1 HO1 ltac:(lia) ltac:(lia)) as (R2 & m3 & h' & E2 & Hms2 & HD2 & HO2 & Hfr2).
    unfold L3 in E2. exists R2, m3, h'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HD2|]. split; [exact HO2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma d_pro : forall regs m1 m h MC0,
  CI m1 m (U FC DL h HL HM DP BC OL SL MC0) -> PQ h -> arr_len h = 573 ->
  DREGS regs HL MC ->
  exists R m', msteps s6_segs (mkst regs (0x1ba30 : word) m s6_rom) (mkst R (0x1ba70 : word) m' s6_rom)
    /\ DI m1 m' h
    /\ OREGS R (HL / 2)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h MC0 HC HPQ HLh HDR.
  open_ci HC. destruct HDR as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P19 & P14).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run3 30%nat NoDirs NoReads
      [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
       (10, EVar 43); (11, EAdd (EVar 32) (EVar 42)); (2, EVar 40); (19, EVar 41); (14, EVar 37)]
      [S; T; 0; 0; 0; HL; 0; 0; SP; MC; dsc_off t; E] h.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M [KMc] ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ split; [ exact HB2 | split; [ rod_tower HRC MS MP MF | split; [ ag_tower HAG
                   | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                 | split; [exact HPQ | exact HLh] ] |]
      end
  end.
  split; [| fr_weak Hfr].
  unfold OREGS; repeat split;
    (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; cbn [pqF3];
       change (2 ^ 1) with 2; first [reflexivity | assumption | f_equal; lia] end).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Goal True. idtac "d_pro OK". exact I. Qed.


End PhaseD.
End Walk.
End FXG.
