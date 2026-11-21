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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2 BuildTree6_3.
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


Definition stC4 : cfg :=
  CFG [(0%nat, 65536); (1%nat, 573); (2%nat, 256)] [] [EVar 1%nat] [0x1bba8; 0x1bc00; 0x1bc6c; 0x1bcb0; 0x1be14]
      [AV (EAdd (EVar 32) (EShl (EVar 34) 2)) 3008 4 1 (EVar 34);
       AV (EAdd (EVar 32) (EShl (EOr (EVar 34) (ELit 1)) 2)) 3008 4 1 (EOr (EVar 34) (ELit 1));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 34)) 2)) 0 2 0 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EOr (EVar 34) (ELit 1))) 2)) 0 2 0 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EApp1 1 (EVar 34))) 5308 1 2 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 32) (EApp1 1 (EOr (EVar 34) (ELit 1)))) 5308 1 2 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EVar 35)) 5308 1 2 (EVar 35);
       AV (EAdd (EVar 32) (EApp1 1 (EVar 38))) 5308 1 2 (EApp1 1 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EVar 35) 2)) 0 2 0 (EVar 35);
       AV (EAdd (EVar 32) (EShl (EVar 44) 2)) 3008 4 1 (EVar 44);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 1 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 38)) 2)) 0 2 0 (EApp1 1 (EVar 38))].

Definition VB4 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600);
   (39%nat, 573); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 3000); (43%nat, 600); (44%nat, 600)].

Definition EP0 : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (8, EAdd (EVar 32) (ELit 2976));
   (22, EAdd (EVar 32) (ELit 3008)); (13, EAdd (EVar 32) (ELit 5308)); (12, ELit 3); (14, ELit 2); (15, ELit 1);
   (11, EAdd (EVar 32) (EVar 42)); (19, EVar 41); (2, EVar 40); (10, EVar 43)].
Definition HB4 : list (Z * expr) :=
  EP0 ++ [(16, EVar 39); (17, EVar 35); (5, EAdd (EAdd (EVar 32) (EVar 35)) (ELit 5308)); (6, EAdd (EVar 33) (EShl (EVar 35) 2))].
Definition HP4 : list (Z * expr) := HB4 ++ [(28, EVar 34); (7, EVar 36); (30, EVar 37)].
Definition MP4 : list (Z * expr) := HB4 ++ [(7, EVar 36); (28, EVar 38); (29, EVar 38)].

Section PhaseE.
Variables (BC : arr) (OL SL MC : Z).
Local Abbreviation W6 FC DL HP HL HM DP := (U FC DL HP HL HM DP BC OL SL MC).
Hypothesis Hmc : 0 <= MC < 600.

Definition BASE4 (R : bvmap 5 word) (node : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 8 = zw (S + 2976)
  /\ getr R 22 = zw (S + 3008) /\ getr R 13 = zw (S + 5308) /\ getr R 12 = zw 3 /\ getr R 14 = zw 2 /\ getr R 15 = zw 1
  /\ getr R 11 = zw (S + dsc_off t) /\ getr R 19 = zw MC /\ getr R 2 = zw SP /\ getr R 10 = zw node.

Definition EREGS (R : bvmap 5 word) (hl node : Z) : Prop := BASE4 R node /\ getr R 5 = zw hl.

Definition H2B (R : bvmap 5 word) (node n v : Z) : Prop :=
  BASE4 R node /\ getr R 16 = zw n /\ getr R 17 = zw v /\ getr R 5 = zw (S + 5308 + v) /\ getr R 6 = zw (T + v * 4).
Definition H2REGS (R : bvmap 5 word) (node n v hl j k : Z) : Prop :=
  H2B R node n v /\ getr R 28 = zw j /\ getr R 7 = zw k /\ getr R 30 = zw hl.
Definition M2REGS (R : bvmap 5 word) (node n v hl j k j' : Z) : Prop :=
  H2B R node n v /\ getr R 7 = zw k /\ getr R 28 = zw j' /\ getr R 29 = zw j'.
Definition X2REGS (R : bvmap 5 word) (node n : Z) : Prop := BASE4 R node /\ getr R 16 = zw n.

Definition RNG (FC DP : arr) : Prop :=
  (forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256)
  /\ arr_len FC = tsize t /\ arr_len DP = 573.

Definition PQ4 (HP : arr) (HL : Z) : Prop := (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < tsize t) /\ arr_len HP = 573.

Definition EI (m1 m : word -> option byte) (FC DL HP : arr) (HL HM : Z) (DP : arr) : Prop :=
  CI m1 m (W6 FC DL HP HL HM DP) /\ PQ4 HP HL /\ RNG FC DP /\ arr_len DL = tsize t
  /\ cell s6_segs m SP 8 (S + 2047).

Local Ltac nflor :=
  cbn [BuildTree6_3.pqF3];
  repeat match goal with H : Z.lor ?a 1 = _ |- context [Z.lor ?a 1] => rewrite !H end.
Local Ltac nf3 :=
  nflor;
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac side_closer4 :=
  try solve [ assumption
            | nf3; first [ assumption | lia | rewrite ?Z.mod_small by lia; lia
                         | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; nf3; lia end
            | nflor; symex_read_auto
            | nf3; symex_store_auto
            | intros; cbn [BuildTree6_3.pqF3]; first [apply pb_range | apply hv_range | apply wb_range] ].

Local Ltac run4 fuel dirs rds pins pv FC HP DP :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB4 in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs stC4 fuel dirs rdv pinsv vbv NoRegions pv NoVals (pqF3 FC HP DP) F0' (mkst regs pc m s6_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer4
  end.

Local Ltac regs4 HR Hfr :=
  unfold EREGS, H2REGS, M2REGS, X2REGS, H2B, BASE4;
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


Lemma e0_blk : forall regs m1 m FC DL HP HL HM DP,
  CI m1 m (W6 FC DL HP HL HM DP) -> PQ4 HP HL -> RNG FC DP -> arr_len DL = tsize t -> 2 <= HL <= 572 ->
  BuildTree6_3.OREGS S sp t MC regs 0 ->
  exists R m',
    msteps s6_segs (mkst regs (0x1bb68 : word) m s6_rom) (mkst R (0x1bba8 : word) m' s6_rom)
    /\ EI m1 m' FC DL HP HL HM DP
    /\ EREGS R HL E
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP HC HPQ HRN LDL Hhl HO.
  open_ci HC. destruct HO as (P9 & P18 & P20 & P21 & P10 & P11 & P8 & P22 & P12 & P13 & P19 & P2 & P15).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run4 30%nat NoDirs [RVal (EVar 37)]
      [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
       (10, EVar 43); (11, EAdd (EVar 32) (EVar 42)); (8, EAdd (EVar 32) (ELit 2976)); (22, EAdd (EVar 32) (ELit 3008));
       (19, EVar 41); (2, EVar 40)]
      [S; T; 0; 0; 0; HL; 0; 0; SP; MC; dsc_off t; E; 0] FC HP DP.
  blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf [KOther]
    ltac:(split; [regs4 HR Hfr | fr_weak Hfr]).
  split; [exact HPQ|]. split; [exact HRN|]. split; [exact LDL|]. frame_cells.
Qed.

Goal True. idtac "e0 OK". exact I. Qed.


Definition stC4a : cfg := CFG [(0%nat, 65536); (1%nat, 573); (2%nat, 256)] [] [EVar 1%nat] [0x1bbb4] [].

Definition E1X (R : bvmap 5 word) (hl node : Z) : Prop :=
  BASE4 R node /\ getr R 30 = zw (hl - 1) /\ getr R 16 = zw (hl * 4) /\ getr R 5 = zw hl.

Lemma e1a_blk : forall regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> 2 <= HL <= 572 -> 0 <= node < 600 ->
  EREGS regs HL node ->
  exists R m',
    msteps s6_segs (mkst regs (0x1bba8 : word) m s6_rom) (mkst R (0x1bbb4 : word) m' s6_rom)
    /\ EI m1 m' FC DL HP (HL - 1) HM DP
    /\ E1X R HL node
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP node (HC & HPQ & HRN & LDL & C0) Hhl Hnode HE.
  open_ci HC. destruct HE as ((P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10) & P5).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HPQ as [HPQ1 LHP].
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in (EP0 ++ [(5, EVar 44)]) in
  let vbv := eval vm_compute in VB4 in
  symex s6_segs stC4a 10%nat NoDirs NoReads pinsv vbv NoRegions [S; T; 0; 0; 0; 0; 0; 0; SP; MC; dsc_off t; node; HL] NoVals
        (pqF3 FC HP DP) F0' (mkst regs (0x1bba8 : word) m s6_rom) R HR Hfr Hms;
  [side_closer4 ..|].
  blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl]
    ltac:(split; [unfold E1X, BASE4; regs4 HR Hfr | fr_weak Hfr]).
  all: try (nf3; first [reflexivity | f_equal; lia | repeat (rewrite (szwrap_small 32) by lia); lia]).
  split; [|split; [exact HRN | split; [exact LDL | frame_cells]]].
  split; [| exact LHP]. intros i Hi. apply HPQ1. lia.
Qed.

Goal True. idtac "e1a OK". exact I. Qed.

Lemma e1b_blk : forall regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP (HL - 1) HM DP -> 2 <= HL <= 572 -> 0 <= node < 600 -> 0 <= arr_get HP HL < tsize t ->
  E1X regs HL node ->
  let v := arr_get HP HL in
  exists R m',
    msteps s6_segs (mkst regs (0x1bbb4 : word) m s6_rom)
           (mkst R (if HL <? 3 then (0x1bcb0 : word) else (0x1bc00 : word)) m' s6_rom)
    /\ EI m1 m' FC DL (if HL <? 3 then arr_set (arr_set HP 1 v) 1 v else arr_set HP 1 v) (HL - 1) HM DP
    /\ (if HL <? 3 then X2REGS R node (arr_get HP 1) else H2REGS R node (arr_get HP 1) v (HL - 1) 2 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP node (HC & HPQ & HRN & LDL & C0) Hhl Hnode Rh HE.
  open_ci HC. destruct HE as ((P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10) & P30 & P16 & P5).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HPQ as [HPQ1 LHP].
  assert (R1 : 0 <= arr_get HP 1 < tsize t) by (apply HPQ1; lia).
  assert (V1 : hv HP 1 = arr_get HP 1) by (apply hv_get; lia).
  assert (Vh : hv HP HL = arr_get HP HL) by (apply hv_get; lia).
  nodef FC DP (arr_get HP HL) PFh PDh.
  cbv zeta.
  destruct (Z.ltb_spec HL 3) as [C3|C3].
  - run4 40%nat [true] [RVal (EApp1 1 (ELit 1))]
        (EP0 ++ [(5, EVar 44); (30, EAdd (EVar 44) (ELit (-1))); (16, EShl (EVar 44) 2)])
        [S; T; 0; 0; 0; 0; 0; 0; SP; MC; dsc_off t; node; HL] FC HP DP.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf [KHeap 1; KHeap 1]
      ltac:(split; [regs4 HR Hfr | fr_weak Hfr]).
    all: try (nf3; first [reflexivity | f_equal; lia]).
    split; [|split; [exact HRN | split; [exact LDL | nf3; frame_cells]]].
    split; [| rewrite ?arr_len_set; exact LHP].
    intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite ?arr_len_set, LHP.
    destruct (1 =? i), (0 <=? 1), (1 <? 573); cbn [andb]; try lia; apply HPQ1; lia.
  - run4 40%nat [false] [RVal (EApp1 1 (ELit 1))]
        (EP0 ++ [(5, EVar 44); (30, EAdd (EVar 44) (ELit (-1))); (16, EShl (EVar 44) 2)])
        [S; T; 0; 0; 0; 0; 0; 0; SP; MC; dsc_off t; node; HL] FC HP DP.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf [KHeap 1]
      ltac:(split; [regs4 HR Hfr | fr_weak Hfr]).
    all: try (nf3; first [reflexivity | f_equal; lia]).
    split; [|split; [exact HRN | split; [exact LDL | nf3; frame_cells]]].
    split; [| rewrite ?arr_len_set; exact LHP].
    intros i Hi. rewrite !arr_get_set. unfold arr_inb. rewrite ?arr_len_set, LHP.
    destruct (1 =? i), (0 <=? 1), (1 <? 573); cbn [andb]; try lia; apply HPQ1; lia.
Qed.

Goal True. idtac "e1 OK". exact I. Qed.


Section Pq2.
Variables (FC DL : arr) (HLc HM : Z) (DP : arr) (node n : Z).
Local Abbreviation W h := (W6 FC DL h HLc HM DP).
Hypothesis Hhl : 1 <= HLc <= 571.
Hypothesis Hnode : 0 <= node < 600.
Hypothesis Hn : 0 <= n < 573.

Local Abbreviation smal := (BuildTree6_3.smal FC DP).
Local Abbreviation sel := (BuildTree6_3.sel3 FC HLc DP).

Definition DI2 (m1 m : word -> option byte) (h : arr) : Prop := EI m1 m FC DL h HLc HM DP.

Local Ltac open_di HD :=
  let HC := fresh "HC" in let HPQ := fresh "HPQ" in let HRN := fresh "HRN" in let LDL := fresh "LDL" in let C0 := fresh "C0" in
  let HPQ1 := fresh "HPQ1" in let LHP := fresh "LHP" in
  let RFC := fresh "RFC" in let RDP := fresh "RDP" in let LFC := fresh "LFC" in let LDP := fresh "LDP" in
  destruct HD as (HC & HPQ & HRN & LDL & C0); pose proof HPQ as [HPQ1 LHP]; pose proof HRN as (RFC & RDP & LFC & LDP); open_ciT HC.

Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : forall q, 1 <= q <= HLc -> 0 <= arr_get h q < tsize t |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  nodef FC DP (arr_get h i) PF PD.

Local Ltac open_b4 H :=
  let H' := fresh "BR'" in pose proof H as H';
  destruct H' as ((P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10) & P16 & P17 & P5 & P6).

Lemma h2_step : forall regs m1 m h v j k,
  DI2 m1 m h -> H2REGS regs node n v HLc j k -> 1 <= k -> j = k * 2 -> j <= HLc -> 0 <= v < tsize t ->
  exists R, msteps s6_segs (mkst regs (0x1bc00 : word) m s6_rom) (mkst R (0x1bc6c : word) m s6_rom)
    /\ M2REGS R node n v HLc j k (sel h j)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h v j k HD HRg Hk Hjk Hj Hv. open_di HD. destruct HRg as (HBx & P28 & P7 & P30). open_b4 HBx.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  nodef FC DP v PFv PDv.
  pose proof (lor1_even k ltac:(lia)) as Hj1. rewrite <- Hjk in Hj1.
  node h j Vj Rj PFj PDj.
  unfold BuildTree6_3.sel3.
  destruct (Z.ltb_spec j HLc) as [Cj|Cj]; cbn [andb].
  - node h (j + 1) Vj1 Rj1 PFj1 PDj1.
    assert (Vj1' : hv h (Z.lor j 1) = arr_get h (j + 1)) by (rewrite Hj1; exact Vj1).
    unfold BuildTree6_3.smal.
    destruct (Z.ltb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C1|C1]; cbn [orb].
    + run4 40%nat [false; false] NoReads HP4 [S; T; j; v; k; HLc; 0; n; SP; MC; dsc_off t; node; 0] FC h DP.
      exists R. split; [exact Hms|]. split; [regs4 HR Hfr | fr_weak Hfr].
    + destruct (Z.eqb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C2|C2]; cbn [andb].
      * destruct (Z.leb_spec (arr_get DP (arr_get h (j + 1))) (arr_get DP (arr_get h j))) as [C3|C3].
        -- run4 40%nat [false; true; false; true] NoReads HP4 [S; T; j; v; k; HLc; 0; n; SP; MC; dsc_off t; node; 0] FC h DP.
           exists R. split; [exact Hms|]. split; [regs4 HR Hfr | fr_weak Hfr].
        -- run4 40%nat [false; true; false; false] NoReads HP4 [S; T; j; v; k; HLc; 0; n; SP; MC; dsc_off t; node; 0] FC h DP.
           exists R. split; [exact Hms|]. split; [regs4 HR Hfr | fr_weak Hfr].
      * run4 40%nat [false; true; true] NoReads HP4 [S; T; j; v; k; HLc; 0; n; SP; MC; dsc_off t; node; 0] FC h DP.
        exists R. split; [exact Hms|]. split; [regs4 HR Hfr | fr_weak Hfr].
  - run4 40%nat [true] NoReads HP4 [S; T; j; v; k; HLc; 0; n; SP; MC; dsc_off t; node; 0] FC h DP.
    exists R. split; [exact Hms|]. split; [regs4 HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h2_step OK". exact I. Qed.

Lemma DI2_write : forall m1 m h i x x' a,
  DI2 m1 m h -> trees_rod_clear6 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  agree_out GB m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
  1 <= i <= HLc -> 0 <= x < tsize t -> a = S + 3008 + 4 * i -> x' = x ->
  DI2 m1 (wbytes m (zw a) (Z_to_le_bytes 4 x')) (arr_set h i x).
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
  apply (DI2_write m1 m h k x); [exact HD0 | rod1 HRC MS | ag1 HAG | lia | lia | lia | nf3; first [reflexivity | lia]].
Local Ltac write2 m1 m h k j' v HD0 HRC MS HAG :=
  apply (DI2_write m1 _ (arr_set h k (arr_get h j')) j' v);
    [ write1 m1 m h k (arr_get h j') HD0 HRC MS HAG
    | apply (trees_rod_clear_wbytes R6); [rod1 HRC MS | intros x Hx; apply wbytes_grows; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia]
    | apply agree_out_wbytes; [ag1 HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia]
    | lia | lia | lia | nf3; first [reflexivity | lia] ].

Local Ltac exit_fin Hms HR Hfr writes :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ writes | split; [regs4 HR Hfr | fr_weak Hfr] ]
  end.

Lemma m2_step : forall regs m1 m h v j k j',
  DI2 m1 m h -> M2REGS regs node n v HLc j k j' -> 1 <= k < j -> j <= j' <= HLc -> j' <= j + 1 -> 0 <= v < tsize t ->
  if smal v (arr_get h j') then
    exists R m', msteps s6_segs (mkst regs (0x1bc6c : word) m s6_rom) (mkst R (0x1bcb0 : word) m' s6_rom)
      /\ DI2 m1 m' (arr_set h k v)
      /\ X2REGS R node n
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else if j' * 2 <=? HLc then
    exists R m', msteps s6_segs (mkst regs (0x1bc6c : word) m s6_rom) (mkst R (0x1bc00 : word) m' s6_rom)
      /\ DI2 m1 m' (arr_set h k (arr_get h j'))
      /\ H2REGS R node n v HLc (j' * 2) j'
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r)
  else
    exists R m', msteps s6_segs (mkst regs (0x1bc6c : word) m s6_rom) (mkst R (0x1bcb0 : word) m' s6_rom)
      /\ DI2 m1 m' (arr_set (arr_set h k (arr_get h j')) j' v)
      /\ X2REGS R node n
      /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h v j k j' HD HMR Hkj Hj Hj1 Hv. pose proof HD as HD0. open_di HD.
  destruct HMR as (HBx & P7 & P28 & P29). open_b4 HBx.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  nodef FC DP v PFv PDv.
  node h j' Vj' Rj' PFj' PDj'.
  unfold BuildTree6_3.smal.
  destruct (Z.ltb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C1|C1]; cbn [orb].
  -
    run4 40%nat [true] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
    exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
  - destruct (Z.eqb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C2|C2]; cbn [andb].
    + destruct (Z.leb_spec (arr_get DP v) (arr_get DP (arr_get h j'))) as [C3|C3].
      *
        run4 40%nat [false; false; false] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
        exit_fin Hms HR Hfr ltac:(write1 m1 m h k v HD0 HRC MS HAG).
      * destruct (Z.leb_spec (j' * 2) HLc) as [C4|C4].
        --
           run4 40%nat [false; false; true; false] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [regs4 HR Hfr | fr_weak Hfr]
           end.
        --
           run4 40%nat [false; false; true; true] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
           exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
    + destruct (Z.leb_spec (j' * 2) HLc) as [C4|C4].
      *
        run4 40%nat [false; true; false] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [regs4 HR Hfr | fr_weak Hfr]
        end.
      * run4 40%nat [false; true; true] [RVal (EVar 37)] MP4 [S; T; j; v; k; HLc; j'; n; SP; MC; dsc_off t; node; 0] FC h DP.
        exit_fin Hms HR Hfr ltac:(write2 m1 m h k j' v HD0 HRC MS HAG).
Qed.

Goal True. idtac "m2_step OK". exact I. Qed.

Lemma smaller_W2 : forall h a b, smaller (W h) t a b = smal a b.
Proof. intros. unfold smaller, BuildTree6_3.smal. autorewrite with btupd. reflexivity. Qed.

Lemma loop2_S_sel : forall f h v k j, j <= HLc ->
  pqdownheap_loop (Datatypes.S f) (W h) t v k j =
    if smal v (arr_get h (sel h j)) then (W h, k)
    else pqdownheap_loop f (W (arr_set h k (arr_get h (sel h j)))) t v (sel h j) (sel h j * 2).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. autorewrite with btupd.
  replace (j <=? HLc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  autorewrite with btupd. rewrite !smaller_W2. unfold BuildTree6_3.sel3.
  destruct ((j <? HLc) && smal (arr_get h (j + 1)) (arr_get h j)).
  - destruct (smal v (arr_get h (j + 1))); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
  - destruct (smal v (arr_get h j)); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
Qed.

Lemma inner2 : forall fuel regs m1 m h v j k,
  DI2 m1 m h -> H2REGS regs node n v HLc j k -> 1 <= k -> j = k * 2 -> j <= HLc -> 0 <= v < tsize t ->
  HLc < j * 2 ^ Z.of_nat fuel ->
  let '(s', k') := pqdownheap_loop fuel (W h) t v k j in
  exists R m', msteps s6_segs (mkst regs (0x1bc00 : word) m s6_rom) (mkst R (0x1bcb0 : word) m' s6_rom)
    /\ DI2 m1 m' (arr_set (ds_heap s') k' v)
    /\ X2REGS R node n
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction fuel as [|f IH]; intros regs m1 m h v j k HD HRg Hk Hjk Hj Hv Hfuel.
  - exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
    rewrite loop2_S_sel by lia.
    pose proof (BuildTree6_3.sel3_range FC HLc DP h j ltac:(lia)) as Hsel.
    destruct (h2_step regs m1 m h v j k HD HRg Hk Hjk Hj Hv) as (R1 & Hms1 & HM1 & Hfr1).
    pose proof (m2_step R1 m1 m h v j k (sel h j) HD HM1 ltac:(lia) ltac:(lia) ltac:(lia) Hv) as HB.
    destruct (smal v (arr_get h (sel h j))).
    + destruct HB as (R2 & m2 & Hms2 & HD2 & HO2 & Hfr2). autorewrite with btupd.
      exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HD2|]. split; [exact HO2|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (Z.leb_spec (sel h j * 2) HLc) as [C4|C4].
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HR2 & Hfr2).
        specialize (IH R2 m1 m2 (arr_set h k (arr_get h (sel h j))) v (sel h j * 2) (sel h j)
                       HD2 HR2 ltac:(lia) ltac:(lia) C4 Hv ltac:(nia)).
        destruct (pqdownheap_loop f _ t v (sel h j) (sel h j * 2)) as [s' k'].
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

End Pq2.


Lemma e_remove : forall regs m1 m FC DL HP HL HM DP node,
  EI m1 m FC DL HP HL HM DP -> 2 <= HL <= 572 -> 0 <= node < 600 ->
  EREGS regs HL node ->
  let HP1 := arr_set HP 1 (arr_get HP HL) in
  exists R m',
    msteps s6_segs (mkst regs (0x1bba8 : word) m s6_rom) (mkst R (0x1bcb0 : word) m' s6_rom)
    /\ EI m1 m' FC DL (ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM DP) t 1)) (HL - 1) HM DP
    /\ X2REGS R node (arr_get HP 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HL HM DP node HE Hhl Hnode HRE.
  pose proof Htt as Htt'. pose proof elems_range as He. pose proof tsize_elems as Hte.
  pose proof HE as (_ & [HPQ1 LHP] & _).
  assert (Hh : 0 <= arr_get HP HL < tsize t) by (apply HPQ1; lia).
  assert (H1 : 0 <= arr_get HP 1 < tsize t) by (apply HPQ1; lia).
  destruct (e1a_blk regs m1 m FC DL HP HL HM DP node HE Hhl Hnode HRE) as (R1 & ma & Hms1 & HE1 & HR1 & Hfr1).
  destruct (e1b_blk R1 m1 ma FC DL HP HL HM DP node HE1 Hhl Hnode Hh HR1) as (R2 & mb & Hms2 & HE2 & HR2 & Hfr2).
  cbv zeta. unfold pqdownheap. autorewrite with btupd. rewrite Z.shiftl_mul_pow2 by lia. change (1 * 2 ^ 1) with 2.
  destruct (Z.ltb_spec HL 3) as [C3|C3].
  -
    rewrite pqdownheap_loop_out by (autorewrite with btupd; lia).
    rewrite heap_set_shape, ds_heap_set_heap. autorewrite with btupd.
    rewrite (arr_get_set HP 1 1 (arr_get HP HL)). unfold arr_inb. rewrite LHP. replace ((1 =? 1) && ((0 <=? 1) && (1 <? 573))) with true by reflexivity. cbn [andb].
    replace (HL <? 3) with true in * by (symmetry; apply Z.ltb_lt; lia).
    exists R2, mb. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HE2|]. split; [exact HR2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - pose proof (inner2 FC DL (HL - 1) HM DP node (arr_get HP 1) ltac:(lia) Hnode ltac:(lia)
                  32 R2 m1 mb (arr_set HP 1 (arr_get HP HL)) (arr_get HP HL) 2 1
                  HE2 HR2 ltac:(lia) ltac:(lia) ltac:(lia) Hh ltac:(change (2 ^ Z.of_nat 32) with 4294967296; lia)) as HI.
    rewrite (arr_get_set HP 1 1 (arr_get HP HL)). unfold arr_inb. rewrite LHP. replace ((1 =? 1) && ((0 <=? 1) && (1 <? 573))) with true by reflexivity. cbn [andb].
    destruct (pqdownheap_loop 32 _ t (arr_get HP HL) 1 2) as [s' k'].
    destruct HI as (R3 & m3 & Hms3 & HD3 & HO3 & Hfr3).
    rewrite heap_set_shape, ds_heap_set_heap.
    exists R3, m3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
    split; [exact HD3|]. split; [exact HO3|].
    intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

End PhaseE.
End Walk.
End FXG.
