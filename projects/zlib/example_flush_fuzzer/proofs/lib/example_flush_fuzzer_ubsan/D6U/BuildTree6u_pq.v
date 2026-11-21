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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1.
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



Definition pqF (FC HP DP : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb FC x | 1%nat => hv HP x | _ => wb DP x end.

Definition stCq : cfg :=
  CFG [(0%nat, 65536); (1%nat, 573); (2%nat, 256)] [] [EVar 1%nat] [0x1ded0; 0x1df9c; 0x1e044]
      [AV (EAdd (EVar 32) (EShl (EVar 34) 2)) 3008 4 1 (EVar 34);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 34)) 2)) 0 2 0 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EAdd (EVar 34) (ELit 1))) 2)) 0 2 0 (EApp1 1 (EAdd (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EApp1 1 (EVar 34))) 5308 1 2 (EApp1 1 (EVar 34));
       AV (EAdd (EVar 32) (EApp1 1 (EAdd (EVar 34) (ELit 1)))) 5308 1 2 (EApp1 1 (EAdd (EVar 34) (ELit 1)));
       AV (EAdd (EVar 32) (EVar 35)) 5308 1 2 (EVar 35);
       AV (EAdd (EVar 32) (EApp1 1 (EVar 38))) 5308 1 2 (EApp1 1 (EVar 38));
       AV (EAdd (EVar 33) (EShl (EVar 35) 2)) 0 2 0 (EVar 35);
       AV (EAdd (EVar 32) (EShl (EVar 36) 2)) 3008 4 1 (EVar 36);
       AV (EAdd (EVar 32) (EShl (EVar 38) 2)) 3008 4 1 (EVar 38);
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EVar 38)) 2)) 0 2 0 (EApp1 1 (EVar 38))].

Definition VBq : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600);
   (39%nat, 600); (40%nat, 2 ^ 63); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64);
   (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64); (50%nat, 2 ^ 64); (51%nat, 2 ^ 64)].

Definition PQ_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Section Pq.
Variables (FC DL : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Abbreviation W h := (U FC DL h HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis RDP : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.
Hypothesis Hhl : 1 <= HL <= 572.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LDP : arr_len DP = 573.

Definition smal (n m : Z) : bool :=
  (arr_get FC n <? arr_get FC m) || ((arr_get FC n =? arr_get FC m) && (arr_get DP n <=? arr_get DP m)).

Lemma smaller_W : forall h n m, smaller (W h) t n m = smal n m.
Proof. intros. unfold smaller, smal. autorewrite with btupd. reflexivity. Qed.

Definition sel (h : arr) (j : Z) : Z :=
  if (j <? HL) && smal (arr_get h (j + 1)) (arr_get h j) then j + 1 else j.

Lemma sel_range : forall h j, 1 <= j <= HL -> j <= sel h j <= HL /\ sel h j <= j + 1.
Proof.
  intros h j Hj. unfold sel. destruct (Z.ltb_spec j HL); cbn [andb]; [destruct (smal _ _)|]; lia.
Qed.

Definition PQ (h : arr) : Prop := forall i, 1 <= i <= HL -> 0 <= arr_get h i < tsize t.

Definition PQF (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6u_segs m (SP + -8) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6u_segs m (SP + -16) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6u_segs m (SP + -24) 8 (bv_unsigned (getr regs0 18))
  /\ cell s6u_segs m (SP + -32) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6u_segs m (SP + -40) 8 (bv_unsigned (getr regs0 20))
  /\ cell s6u_segs m (SP + -48) 8 (bv_unsigned (getr regs0 21))
  /\ cell s6u_segs m (SP + -56) 8 (bv_unsigned (getr regs0 22)).

Definition DI (m1 m : word -> option byte) (h : arr) : Prop :=
  CI m1 m (W h) /\ PQ h /\ arr_len h = 573.

Definition QB (R : bvmap 5 word) (v : Z) : Prop :=
  getr R 10 = zw (S + 5308) /\ getr R 11 = zw T /\ getr R 12 = zw (S + 3008) /\ getr R 13 = zw NHP
  /\ getr R 14 = zw v /\ getr R 16 = zw (S + 5300) /\ getr R 17 = zw 1 /\ getr R 5 = zw (T + v * 4)
  /\ getr R 6 = zw NDP /\ getr R 7 = zw (S + v + 5308) /\ getr R 28 = zw 1 /\ getr R 29 = zw 1
  /\ getr R 30 = zw 572 /\ getr R 2 = zw (SP - 64).
Definition QBP : list (Z * expr) :=
  [(10, EAdd (EVar 32) (ELit 5308)); (11, EVar 33); (12, EAdd (EVar 32) (ELit 3008)); (13, EVar 44);
   (14, EVar 35); (16, EAdd (EVar 32) (ELit 5300)); (17, ELit 1); (5, EAdd (EVar 33) (EShl (EVar 35) 2));
   (6, EVar 45); (7, EAdd (EAdd (EVar 32) (EVar 35)) (ELit 5308)); (28, ELit 1); (29, ELit 1); (30, ELit 572);
   (2, EAdd (EVar 40) (ELit (-64)))].
Definition QH (R : bvmap 5 word) (v j k hl : Z) : Prop := QB R v /\ getr R 15 = zw k /\ getr R 31 = zw j /\ getr R 9 = zw hl.
Definition QHP : list (Z * expr) := QBP ++ [(15, EVar 36); (31, EVar 34); (9, EVar 37)].
Definition QM (R : bvmap 5 word) (v j k j' : Z) : Prop := QB R v /\ getr R 15 = zw k /\ getr R 31 = zw j /\ getr R 8 = zw j'.
Definition QMP : list (Z * expr) := QBP ++ [(15, EVar 36); (31, EVar 34); (8, EVar 38)].
Definition QX (R : bvmap 5 word) (v k' : Z) : Prop :=
  getr R 12 = zw (S + 3008) /\ getr R 14 = zw v /\ getr R 8 = zw (k' * 4) /\ getr R 2 = zw (SP - 64).
Definition QXP : list (Z * expr) := [(12, EAdd (EVar 32) (ELit 3008)); (14, EVar 35); (8, EShl (EVar 36) 2); (2, EAdd (EVar 40) (ELit (-64)))].


Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : PQ h |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb FC (arr_get h i) = arr_get FC (arr_get h i)) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]);
  assert (PD : wb DP (arr_get h i) = arr_get DP (arr_get h i)) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).

Local Ltac nf3 :=
  cbn [pqF];
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac zc3 :=
  change (2 ^ 3) with 8 in *;
  first [ lazymatch goal with
          | |- _ mod _ = 0 => keep_mod_facts; Z.to_euclidean_division_equations; lia
          end
        | zcond_close ].

Local Ltac side_closer3 :=
  try solve [ assumption
            | nf3; first [ assumption | lia | rewrite ?Z.mod_small by lia; lia
                         | repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; nf3; lia end
            | cbn [pqF]; symex_read_auto
            | nf3; symex_read_auto
            | nf3; symex_store_auto
            | nf3; symex_sok_auto
            | nf3; zc3
            | intros; cbn [pqF]; first [apply pb_range | apply hv_range | apply wb_range] ].

Local Ltac run3 fuel dirs rds pins pv h :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBq in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs stCq fuel dirs rdv pinsv vbv NoRegions pv NoVals (pqF FC h DP) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer3
  end.

Local Ltac qregs HR Hfr :=
  let A := fresh "A" in
  unfold QH, QM, QX, QB;
  repeat match goal with
  | |- _ /\ _ => split
  | |- getr ?R ?r = _ =>
      first [ rewrite (Hfr r eq_refl); assumption
            | symex_reg HR r as A; rewrite A; cbn [pqF];
              first [ reflexivity | assumption | f_equal; nf3; lia | nf3; assumption
                    | rewrite zw_not by lia; f_equal; lia
                    | idtac ] ]
  end.

Local Ltac open_di HD :=
  let HC := fresh "HC" in let HPQ := fresh "HPQ" in let HLh := fresh "HLh" in
  destruct HD as (HC & HPQ & HLh); open_ciT HC.

Definition CLOBQ : list reg := [2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%bv.

Lemma tree_even : forall x, 0 <= x -> (S + toff t + x * 2 ^ 2) mod 2 ^ 1 = 0.
Proof.
  intros x Hx. pose proof HS8 as HS8'. pose proof toff_mod4 as Htm.
  keep_mod_facts. Z.to_euclidean_division_equations. lia.
Qed.


Lemma q_pro : forall regs m1 m h k,
  DI m1 m h -> 1 <= k <= HL ->
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw k -> getr regs 2 = zw SP ->
  let v := arr_get h k in
  exists R m',
    msteps s6u_segs (mkst regs (0x1de0c : word) m s6u_rom)
           (mkst R (if HL <? k * 2 then (0x1e044 : word) else (0x1ded0 : word)) m' s6u_rom)
    /\ DI m1 m' h /\ PQF m' regs
    /\ (if HL <? k * 2 then QX R v k else QH R v (k * 2) k HL)
    /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h k HD Hk P10 P11 P12 P2. cbv zeta. pose proof HD as (_ & HPQ0 & HLh0). open_di HD.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  node h k Vk Rk PFk PDk. pose proof (tree_even (arr_get h k) ltac:(lia)) as Hal.
  destruct (Z.ltb_spec HL (k * 2)) as [Ck|Ck].
  - run3 60%nat [false; false; false; false; true] [RVal (EVar 37)]
        [(10, EVar 32); (11, EVar 33); (12, EVar 36); (2, EVar 40)]
        [S; T; 0; arr_get h k; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [split; [ci_tower HB HRC HAG MS MP MF HFf M [KOther; KOther; KOther; KOther; KOther; KOther; KOther]
                      | split; [exact HPQ0 | exact HLh0]] |];
        split; [unfold PQF; repeat split; frame_cells|];
        split; [qregs HR Hfr | fr_weak Hfr]
    end.
  - run3 60%nat [false; false; false; true] [RVal (EVar 37)]
        [(10, EVar 32); (11, EVar 33); (12, EVar 36); (2, EVar 40)]
        [S; T; 0; arr_get h k; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
    lazymatch type of Hms with
    | msteps _ _ (mkst ?R _ ?M _) =>
        exists R, M; split; [exact Hms|]; clear Hms;
        split; [split; [ci_tower HB HRC HAG MS MP MF HFf M [KOther; KOther; KOther; KOther; KOther; KOther; KOther]
                      | split; [exact HPQ0 | exact HLh0]] |];
        split; [unfold PQF; repeat split; frame_cells|];
        split; [qregs HR Hfr; f_equal; nf3; rewrite ?Hal; ltb_tf; zlit_logic; lia | fr_weak Hfr]
    end.
Qed.

Goal True. idtac "q_pro OK". exact I. Qed.

Local Ltac open_qb H :=
  let H' := fresh "QB'" in pose proof H as H';
  destruct H' as (P10 & P11 & P12 & P13 & P14 & P16 & P17 & P5 & P6 & P7 & P28 & P29 & P30 & P2).
Local Ltac open_qh H :=
  let H' := fresh "QH'" in pose proof H as H';
  destruct H' as (HB' & P15 & P31 & P9); open_qb HB'.
Local Ltac open_qm H :=
  let H' := fresh "QM'" in pose proof H as H';
  destruct H' as (HB' & P15 & P31 & P8); open_qb HB'.


Lemma q_h : forall regs m h v j k m1,
  DI m1 m h -> QH regs v j k HL -> 1 <= k -> j = k * 2 -> j <= HL -> 0 <= v < tsize t ->
  exists R, msteps s6u_segs (mkst regs (0x1ded0 : word) m s6u_rom) (mkst R (0x1df9c : word) m s6u_rom)
    /\ QM R v j k (sel h j)
    /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r).
Proof.
  intros regs m h v j k m1 HD HRg Hk Hjk Hj Hv. open_di HD. open_qh HRg.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  node h j Vj Rj PFj PDj.
  unfold sel.
  destruct (Z.ltb_spec j HL) as [Cj|Cj]; cbn [andb].
  - node h (j + 1) Vj1 Rj1 PFj1 PDj1.
    unfold smal.
    destruct (Z.ltb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C1|C1]; cbn [orb].
    + run3 60%nat [false; false; false; false; false; false; false; false; false; false; false] NoReads QHP
          [S; T; j; v; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
      exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
    + destruct (Z.eqb_spec (arr_get FC (arr_get h (j + 1))) (arr_get FC (arr_get h j))) as [C2|C2]; cbn [andb].
      * destruct (Z.leb_spec (arr_get DP (arr_get h (j + 1))) (arr_get DP (arr_get h j))) as [C3|C3].
        -- run3 60%nat [false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; true] NoReads QHP
              [S; T; j; v; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
           exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
        -- run3 60%nat [false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false] NoReads QHP
              [S; T; j; v; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
           exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
      * run3 60%nat [false; false; false; false; false; false; false; false; false; false; true; true] NoReads QHP
            [S; T; j; v; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
        exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
  - run3 60%nat [true] NoReads QHP [S; T; j; v; k; HL; 0; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
    exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "q_h OK". exact I. Qed.


Lemma DI_write : forall m1 m h i x x' a,
  DI m1 m h -> trees_rod_clear6u (wbytes m (zw a) (Z_to_le_bytes 4 x')) ->
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

Lemma PQF_write : forall m regs0 (a : Z) bs,
  PQF m regs0 -> S <= a -> a + Z.of_nat (length bs) <= S + 5968 ->
  PQF (wbytes m (zw a) bs) regs0.
Proof.
  intros m regs0 a bs HF Ha Hb.
  pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'. pose proof HLb as (HS' & _). unfold dsl_SIZE in HS'.
  unfold PQF in *.
  repeat match goal with |- _ /\ _ => split end;
    (apply cell_write_other; [ | lia | cbn; lia | lia | lia | cbn; lia ]);
    repeat match type of HF with _ /\ _ => let X := fresh in destruct HF as [X HF]; try exact X end; try exact HF.
Qed.

Local Ltac rod1 HRC MS := apply (trees_rod_clear_wbytes R6u _ _ _ HRC); [intros x Hx; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia].
Local Ltac ag1 HAG := apply agree_out_wbytes; [exact HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6u_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia].
Local Ltac write1 m1 m h k x HD0 HRC MS HAG :=
  apply (DI_write m1 m h k x); [exact HD0 | rod1 HRC MS | ag1 HAG | lia | lia | lia | nf3; first [reflexivity | lia]].

Lemma q_m : forall regs m h v j k j' m1 regs0,
  DI m1 m h -> PQF m regs0 -> QM regs v j k j' -> 1 <= k < j -> j <= j' <= HL -> j' <= j + 1 -> 0 <= v < tsize t ->
  if smal v (arr_get h j') then
    exists R, msteps s6u_segs (mkst regs (0x1df9c : word) m s6u_rom) (mkst R (0x1e044 : word) m s6u_rom)
      /\ QX R v k
      /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r)
  else if j' * 2 <=? HL then
    exists R m', msteps s6u_segs (mkst regs (0x1df9c : word) m s6u_rom) (mkst R (0x1ded0 : word) m' s6u_rom)
      /\ DI m1 m' (arr_set h k (arr_get h j')) /\ PQF m' regs0
      /\ QH R v (j' * 2) j' HL
      /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r)
  else
    exists R m', msteps s6u_segs (mkst regs (0x1df9c : word) m s6u_rom) (mkst R (0x1e044 : word) m' s6u_rom)
      /\ DI m1 m' (arr_set h k (arr_get h j')) /\ PQF m' regs0
      /\ QX R v j'
      /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r).
Proof.
  intros regs m h v j k j' m1 regs0 HD HF HMR Hkj Hj Hj1 Hv. pose proof HD as HD0. open_di HD. open_qm HMR.
  assert (Rv : 0 <= v < tsize t) by exact Hv.
  assert (PFv : pb FC v = arr_get FC v) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
  assert (PDv : wb DP v = arr_get DP v) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).
  node h j' Vj' Rj' PFj' PDj'.
  unfold smal.
  destruct (Z.ltb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C1|C1]; cbn [orb].
  -
    run3 60%nat [false; false; false; false; false; false; false; true; false] NoReads QMP
        [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
    exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
  - destruct (Z.eqb_spec (arr_get FC v) (arr_get FC (arr_get h j'))) as [C2|C2]; cbn [andb].
    + destruct (Z.leb_spec (arr_get DP v) (arr_get DP (arr_get h j'))) as [C3|C3].
      *
        run3 60%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; true; true] NoReads QMP
            [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
        exists R. split; [exact Hms|]. split; [qregs HR Hfr | fr_weak Hfr].
      * destruct (Z.leb_spec (j' * 2) HL) as [C4|C4].
        --
           run3 60%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]
               [RVal (EVar 37)] QMP [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [apply PQF_write; [exact HF | lia | rewrite length_Z_to_le_bytes; cbn; lia] |];
               split; [qregs HR Hfr | fr_weak Hfr]
           end.
        --
           run3 60%nat [false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]
               [RVal (EVar 37)] QMP [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
           lazymatch type of Hms with
           | msteps _ _ (mkst ?R _ ?M _) =>
               exists R, M; split; [exact Hms|]; clear Hms;
               split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
               split; [apply PQF_write; [exact HF | lia | rewrite length_Z_to_le_bytes; cbn; lia] |];
               split; [qregs HR Hfr | fr_weak Hfr]
           end.
    + destruct (Z.leb_spec (j' * 2) HL) as [C4|C4].
      *
        run3 60%nat [false; false; false; false; false; false; false; false; true; false; true]
            [RVal (EVar 37)] QMP [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [apply PQF_write; [exact HF | lia | rewrite length_Z_to_le_bytes; cbn; lia] |];
            split; [qregs HR Hfr | fr_weak Hfr]
        end.
      * run3 60%nat [false; false; false; false; false; false; false; false; true; false; false; false]
            [RVal (EVar 37)] QMP [S; T; j; v; k; HL; j'; 0; SP; 0; 0; 0; NHP; NDP; 0; 0; 0; 0; 0; 0] h.
        lazymatch type of Hms with
        | msteps _ _ (mkst ?R _ ?M _) =>
            exists R, M; split; [exact Hms|]; clear Hms;
            split; [write1 m1 m h k (arr_get h j') HD0 HRC MS HAG |];
            split; [apply PQF_write; [exact HF | lia | rewrite length_Z_to_le_bytes; cbn; lia] |];
            split; [qregs HR Hfr | fr_weak Hfr]
        end.
Qed.

Goal True. idtac "q_m OK". exact I. Qed.

End Pq.
End Walk.
End FXG.
