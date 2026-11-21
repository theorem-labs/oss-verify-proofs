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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import BuildTree6_1 BuildTree6_2 BuildTree6_3 BuildTree6_4.
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


Definition stC5 : cfg :=
  CFG [(0%nat, 65536); (1%nat, 573); (2%nat, 256)] [] [EVar 1%nat] [0x1bba8; 0x1bd6c; 0x1bdd8; 0x1bb90; 0x1be14]
      [AV (EAdd (EVar 32) (EShl (EVar 34) 2)) 3008 4 1 (EVar 34);
       AV (EAdd (EVar 32) (EShl (EOr (EVar 34) (ELit 1)) 2)) 3008 4 1 (EOr (EVar 34) (ELit 1));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 34)) 2)) 0 2 0 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EOr (EVar 34) (ELit 1))) 2)) 0 2 0 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EApp1 1 (EVar 34))) 5308 1 2 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 32) (EApp1 1 (EOr (EVar 34) (ELit 1)))) 5308 1 2 (EApp1 1 (EOr (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EVar 43)) 5308 1 2 (EVar 43);
       AV (EAdd (EVar 32) (EApp1 1 (EVar 38))) 5308 1 2 (EApp1 1 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EVar 43) 2)) 0 2 0 (EVar 43);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 1 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 38)) 2)) 0 2 0 (EApp1 1 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EVar 39) 2)) 0 2 0 (EVar 39);
       AV (EAdd (EVar 33) (EShl (EVar 46) 2)) 0 2 0 (EVar 46);
       AV (EAdd (EVar 32) (EVar 39)) 5308 1 2 (EVar 39);
       AV (EAdd (EVar 32) (EVar 46)) 5308 1 2 (EVar 46);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (ELit 1)) 2)) 0 2 0 (EApp1 1 (ELit 1));
       AV (EAdd (EVar 32) (EApp1 1 (ELit 1))) 5308 1 2 (EApp1 1 (ELit 1))].

Definition VB5 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600);
   (39%nat, 573); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 3000); (43%nat, 573); (44%nat, 600); (45%nat, 2 ^ 63); (46%nat, 573)].

Definition EP5 : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (8, EVar 45);
   (22, EAdd (EVar 32) (ELit 3008)); (13, EAdd (EVar 32) (ELit 5308)); (12, ELit 3); (14, ELit 2); (15, ELit 1);
   (11, EAdd (EVar 32) (EVar 42)); (19, EVar 41); (2, EVar 40); (10, EVar 43)].
Definition HB5 : list (Z * expr) :=
  EP5 ++ [(16, EAdd (EVar 33) (EShl (EVar 43) 2)); (17, EAdd (EAdd (EVar 32) (EVar 43)) (ELit 5308))].
Definition HP5 : list (Z * expr) := HB5 ++ [(6, EVar 34); (5, EVar 36); (28, EVar 37)].
Definition MP5 : list (Z * expr) := HB5 ++ [(5, EVar 36); (6, EVar 38); (7, EVar 38)].

Lemma szwrap_eqm : forall k a, 0 < k -> (szwrap k a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros k a Hk. unfold szwrap.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (a + 2 ^ (k - 1) - 2 ^ (k - 1)) with a by lia. reflexivity.
Qed.
Lemma wrap16_sx_add : forall a b, wrap16 (szwrap 16 a + szwrap 16 b) = wrap16 (a + b).
Proof.
  intros a b. rewrite !wrap16_mod.
  rewrite Z.add_mod, !szwrap_eqm, <- Z.add_mod by lia. reflexivity.
Qed.

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

Definition H3B (R : bvmap 5 word) (node : Z) : Prop :=
  BASE4 R node /\ getr R 16 = zw (T + node * 4) /\ getr R 17 = zw (S + 5308 + node).
Definition H3REGS (R : bvmap 5 word) (node hl j k : Z) : Prop :=
  H3B R node /\ getr R 6 = zw j /\ getr R 5 = zw k /\ getr R 28 = zw hl.
Definition M3REGS (R : bvmap 5 word) (node j k j' : Z) : Prop :=
  H3B R node /\ getr R 5 = zw k /\ getr R 6 = zw j' /\ getr R 7 = zw j'.
Definition X3REGS (R : bvmap 5 word) (node k : Z) : Prop := BASE4 R node /\ getr R 7 = zw k.
Definition FREGS (R : bvmap 5 word) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 8 = zw (S + 2976)
  /\ getr R 22 = zw (S + 3008) /\ getr R 11 = zw (S + dsc_off t) /\ getr R 19 = zw MC /\ getr R 2 = zw SP.

Definition dmax (DP : arr) (n m : Z) : Z := if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m.


Local Ltac e2_fin :=
  first
    [ nf3; rewrite wrap16_sx_add; f_equal; f_equal; lia
    | nf3; f_equal; f_equal;
      repeat match goal with |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b) end; lia
    |
      lazymatch goal with
      | |- BuildTree6_4.PQ4 _ _ _ /\ _ =>
          split; [|split; [|split; [rewrite !arr_len_set; assumption | nf3; frame_cells]]];
          [ split; [|rewrite !arr_len_set; assumption];
            intros i Hi; rewrite !arr_get_set; unfold arr_inb; rewrite !arr_len_set;
            match goal with L : arr_len ?h = 573 |- context [arr_len ?h] => rewrite L end;
            repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
            rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff, ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.ltb_lt in *;
            try lia;
            match goal with Hp : forall q, 1 <= q <= _ -> 0 <= arr_get ?h q < tsize t |- 0 <= arr_get ?h _ < _ => apply Hp; lia end
          | match goal with Hr : BuildTree6_4.RNG _ ?FC ?DP |- _ =>
              destruct Hr as (RFC' & RDP' & LFC' & LDP');
              split; [|split; [|split; [rewrite arr_len_set; exact LFC' | rewrite arr_len_set; exact LDP']]];
              [ intros i Hi; rewrite arr_get_set; destruct (_ =? i); destruct (arr_inb FC _); cbn [andb];
                [apply wrap16_range' | apply RFC'; exact Hi..]
              | intros i Hi; rewrite arr_get_set; destruct (_ =? i); destruct (arr_inb DP _); cbn [andb];
                [rewrite wrap8_mod'; apply Z.mod_pos_bound; lia | apply RDP'; exact Hi..] ] end ]
      end ].

Lemma e2_blk : forall regs m1 m FC DL HP HLc HM DP node n,
  EI m1 m FC DL HP HLc HM DP -> 1 <= HLc <= 571 -> 0 <= node < tsize t -> 3 <= HM <= 573 ->
  0 <= n < tsize t ->
  X2REGS regs node n ->
  let m_ := arr_get HP 1 in
  exists R m',
    msteps s6_segs (mkst regs (0x1bcb0 : word) m s6_rom)
           (mkst R (if HLc <? 2 then (0x1bb90 : word) else (0x1bd6c : word)) m' s6_rom)
    /\ EI m1 m' (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
                (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node))
                (arr_set (arr_set (arr_set HP (HM - 1) n) (HM - 2) m_) 1 node) HLc (HM - 2)
                (arr_set DP node (wrap8 (dmax DP n m_ + 1)))
    /\ (if HLc <? 2 then X3REGS R node 1 else H3REGS R node HLc 2 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC DL HP HLc HM DP node n (HC & HPQ & HRN & LDL & C0) Hhl Hnode Hhm Hn HE.
  open_ciT HC. destruct HE as ((P9 & P18 & P20 & P8 & P22 & P13 & P12 & P14 & P15 & P11 & P19 & P2 & P10) & P16).
  assert (P8' : getr regs 8 = zw (S + 2976)) by exact P8.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HPQ as [HPQ1 LHP]. pose proof HRN as (RFC & RDP & LFC & LDP).
  assert (R1 : 0 <= arr_get HP 1 < tsize t) by (apply HPQ1; lia).
  assert (V1 : hv HP 1 = arr_get HP 1) by (apply hv_get; lia).
  nodef FC DP n PFn PDn. nodef FC DP (arr_get HP 1) PFm PDm.
  assert (C4' : cell s6_segs m (S + 5304) 4 (HM - 2 + 2)) by (replace (HM - 2 + 2) with HM by lia; exact Chm).
  cbv zeta. unfold dmax.
  destruct (Z.ltb_spec (arr_get DP (arr_get HP 1)) (arr_get DP n)) as [Cd|Cd];
    destruct (Z.ltb_spec HLc 2) as [C2|C2].
  - run5 60%nat [true; true] [RVal (EAdd (EVar 44) (ELit 2)); RVal (EApp1 1 (ELit 1)); RVal (EVar 37)]
        (EP5 ++ [(16, EVar 39)]) [S; T; 0; 0; 0; HLc; 0; n; SP; MC; dsc_off t; node; HM - 2; S + 2976; 0] FC HP DP.
    nf_in Hms. rewrite !V1 in Hms.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf
      [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1]
      ltac:(split; [unfold X3REGS; regs5 HR Hfr | fr_weak Hfr]).
    all: e2_fin.
  - run5 60%nat [true; false] [RVal (EAdd (EVar 44) (ELit 2)); RVal (EApp1 1 (ELit 1)); RVal (EVar 37)]
        (EP5 ++ [(16, EVar 39)]) [S; T; 0; 0; 0; HLc; 0; n; SP; MC; dsc_off t; node; HM - 2; S + 2976; 0] FC HP DP.
    nf_in Hms. rewrite !V1 in Hms.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf
      [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1]
      ltac:(split; [unfold H3REGS, H3B; regs5 HR Hfr | fr_weak Hfr]).
    all: e2_fin.
  - run5 60%nat [false; true] [RVal (EAdd (EVar 44) (ELit 2)); RVal (EApp1 1 (ELit 1)); RVal (EVar 37)]
        (EP5 ++ [(16, EVar 39)]) [S; T; 0; 0; 0; HLc; 0; n; SP; MC; dsc_off t; node; HM - 2; S + 2976; 0] FC HP DP.
    nf_in Hms. rewrite !V1 in Hms.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf
      [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1]
      ltac:(split; [unfold X3REGS; regs5 HR Hfr | fr_weak Hfr]).
    all: e2_fin.
  - run5 60%nat [false; false] [RVal (EAdd (EVar 44) (ELit 2)); RVal (EApp1 1 (ELit 1)); RVal (EVar 37)]
        (EP5 ++ [(16, EVar 39)]) [S; T; 0; 0; 0; HLc; 0; n; SP; MC; dsc_off t; node; HM - 2; S + 2976; 0] FC HP DP.
    nf_in Hms. rewrite !V1 in Hms.
    blk_finE Hms HR Hfr HB HRC HAG MS MP MF HFf
      [KHm; KHeap (HM - 1); KHm; KHeap (HM - 2); KFc node; KDepth node; KDl (arr_get HP 1); KDl n; KHeap 1]
      ltac:(split; [unfold H3REGS, H3B; regs5 HR Hfr | fr_weak Hfr]).
    all: e2_fin.
Qed.

Goal True. idtac "e2 OK". exact I. Qed.

End PhaseE.
End Walk.
End FXG.
