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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import BuildTree6u_1.
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


Definition VB2 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300);
   (36%nat, 600); (37%nat, 600); (38%nat, 600); (39%nat, 2 ^ 63); (40%nat, 600); (41%nat, 600);
   (42%nat, 65536); (43%nat, 65536); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64);
   (47%nat, 2 ^ 64); (48%nat, 2 ^ 32); (49%nat, 3000); (50%nat, 2 ^ 64); (51%nat, 2 ^ 64)].

Definition stC2 : cfg := CFG FB [] [EVar 1%nat] [0x1cbd0; 0x1d444; 0x1d478] [].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC2 VB2 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation NSTP := (2 ^ 64 - 1 - STP t).

Lemma node_lt2 : forall mc, mc < 2 -> Z.land (0 - (if mc <? 2 then 1 else 0)) (mc + 1) = mc + 1.
Proof. intros mc H. rewrite (proj2 (Z.ltb_lt mc 2) H). change (0 - 1) with (-1). apply Z.land_m1_l. Qed.
Lemma node_ge2 : forall mc, 2 <= mc -> Z.land (0 - (if mc <? 2 then 1 else 0)) (mc + 1) = 0.
Proof. intros mc H. rewrite (proj2 (Z.ltb_ge mc 2) H). apply Z.land_0_l. Qed.

Lemma wrap64_mod_add : forall x k, wrap64 (x mod 2 ^ 64 + k) = wrap64 (x + k).
Proof. intros. rewrite !wrap64_mod. rewrite Z.add_mod_idemp_l by lia. reflexivity. Qed.
Lemma wrap64_mod_sub : forall x k, wrap64 (x mod 2 ^ 64 - k) = wrap64 (x - k).
Proof. intros x k. replace (x mod 2 ^ 64 - k) with (x mod 2 ^ 64 + (- k)) by lia. rewrite wrap64_mod_add. f_equal. Qed.


Lemma stree_has_STP : stree_has t = true <-> STP t <> 0.
Proof. destruct t; cbn; split; intros; try congruence; lia. Qed.

Definition slen : Z := match t with TL => 288 | TD => 30 | TB => 1 end.

Lemma stree_Len_dl : forall n, stree_Len t n = arr_get stree_dl n.
Proof. intros n. unfold BuildTree6u_1.stree_dl. destruct t; cbn [stree_Len]; rewrite ?arr_get_make; reflexivity. Qed.

Lemma stree_dl_bound : forall n, 0 <= n < slen -> 0 <= arr_get stree_dl n < 16.
Proof.
  intros n _. unfold BuildTree6u_1.stree_dl. destruct t.
  - pose proof (static_ltree_dl_bound n). lia.
  - pose proof (static_dtree_dl_bound n). lia.
  - rewrite arr_get_make. lia.
Qed.

Lemma slen_ge : STP t <> 0 -> 3 <= slen.
Proof. unfold slen. destruct t; cbn; intros; lia. Qed.

Lemma stree_cells : forall m, trees_rod_clear6u m -> STP t <> 0 ->
  cells s6u_segs m (STP t + 2) 4 2 slen (arr_get stree_dl).
Proof.
  intros m HRC Hst. unfold BuildTree6u_1.stree_dl, slen. destruct t; cbn [TreesRod.STP].
  - exact (proj2 (static_ltree_cells R6u _ m trod_ok6u HRC)).
  - exact (proj2 (static_dtree_cells R6u _ m trod_ok6u HRC)).
  - exfalso. apply Hst. reflexivity.
Qed.

Lemma stree_pb : forall n, 0 <= n < slen -> pb stree_dl n = arr_get stree_dl n.
Proof. intros n Hn. unfold pb. apply Z.mod_small. pose proof (stree_dl_bound n Hn). lia. Qed.

Lemma STP_rod : STP t <> 0 -> 0x11ae0 <= STP t /\ STP t + 2 + 4 * slen <= 0x12510 /\ STP t mod 4 = 0.
Proof. unfold slen. destruct t; cbn; intros; repeat split; try lia; reflexivity. Qed.


Definition DREGS (R : bvmap 5 word) (hl mc : Z) : Prop :=
  getr R 22 = zw T /\ getr R 25 = zw (S + 5300) /\ getr R 26 = zw (S + 2047) /\ getr R 2 = zw SP
  /\ getr R 29 = zw mc /\ getr R 6 = zw hl.

Definition CB (R : bvmap 5 word) : Prop :=
  getr R 22 = zw T /\ getr R 25 = zw (S + 5300) /\ getr R 26 = zw (S + 2047) /\ getr R 10 = zw (STP t) /\ getr R 2 = zw SP
  /\ getr R 11 = zw (S + 3008) /\ getr R 12 = zw NHP /\ getr R 13 = zw NSTP /\ getr R 14 = zw 2 /\ getr R 15 = zw 572
  /\ getr R 16 = zw (S + 5308) /\ getr R 17 = zw NDP /\ getr R 5 = zw 1.
Definition CBP : list (Z * expr) :=
  [(22, EVar 33); (25, EAdd (EVar 32) (ELit 5300)); (26, EAdd (EVar 32) (ELit 2047)); (10, EVar 48); (2, EVar 34);
   (11, EAdd (EVar 32) (ELit 3008)); (12, EVar 44); (13, EVar 47); (14, ELit 2); (15, ELit 572);
   (16, EAdd (EVar 32) (ELit 5308)); (17, EVar 45); (5, ELit 1)].
Definition CREGS (R : bvmap 5 word) (hl mc : Z) : Prop :=
  CB R /\ getr R 7 = zw mc /\ getr R 29 = zw mc /\ getr R 6 = zw hl.
Definition MREGS (R : bvmap 5 word) (hl mc' node : Z) : Prop :=
  CB R /\ getr R 6 = zw (4 * hl + 4) /\ getr R 29 = zw mc' /\ getr R 31 = zw mc' /\ getr R 7 = zw node.
Definition MP : list (Z * expr) :=
  CBP ++ [(6, EAdd (EShl (EVar 37) 2) (ELit 4)); (29, EVar 38); (31, EVar 38); (7, EVar 36)].

Section PhaseC.
Variables (DL : arr) (HM : Z) (BC : arr) (MC : Z).
Local Abbreviation W FC HP HL DP OL SL := (U FC DL HP HL HM DP BC OL SL MC).

Definition l2node (mc : Z) : Z * Z := if mc <? 2 then (mc + 1, mc + 1) else (0, mc).

Definition L2 (X : deflate_state) (mc : Z) : deflate_state * Z := build_tree_loop2 2 X t mc.

Lemma L2_out : forall f FC HP HL DP OL SL mc, 2 <= HL ->
  build_tree_loop2 f (W FC HP HL DP OL SL) t mc = (W FC HP HL DP OL SL, mc).
Proof.
  intros [|f] FC HP HL DP OL SL mc Hhl; [reflexivity|]. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma L2_step : forall f FC HP HL DP OL SL mc, HL < 2 ->
  build_tree_loop2 (Datatypes.S f) (W FC HP HL DP OL SL) t mc =
    (let '(node, mc') := l2node mc in
     build_tree_loop2 f
       (W (arr_set FC node (wrap16 1)) (arr_set HP (HL + 1) node) (HL + 1) (arr_set DP node (wrap8 0)) (wrap64 (OL - 1))
          (if stree_has t then wrap64 (SL - stree_Len t node) else SL)) t mc').
Proof.
  intros f FC HP HL DP OL SL mc Hhl. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with true by (symmetry; apply Z.ltb_lt; lia). unfold l2node.
  destruct (mc <? 2); autorewrite with btupd; destruct (stree_has t); autorewrite with btupd; reflexivity.
Qed.

Lemma L2_ge2 : forall FC HP HL DP OL SL mc, 2 <= HL -> L2 (W FC HP HL DP OL SL) mc = (W FC HP HL DP OL SL, mc).
Proof. intros. unfold L2. apply L2_out. assumption. Qed.

Local Ltac dregs HR Hfr := unfold DREGS; repeat split; reg1 HR Hfr.
Local Ltac cregs HR Hfr := unfold CREGS, MREGS, CB; repeat split; reg1 HR Hfr.

Lemma c_disp : forall regs m1 m FC HP HL DP OL SL mc,
  CI m1 m (W FC HP HL DP OL SL) -> LOC m1 -> 0 <= HL < 600 ->
  L1REGS regs E mc ->
  exists R,
    msteps s6u_segs (mkst regs (0x1cbc4 : word) m s6u_rom)
           (mkst R (if HL <? 2 then (0x1d444 : word) else (0x1cbd0 : word)) m s6u_rom)
    /\ (if HL <? 2 then CREGS R HL mc else DREGS R HL mc)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP HL DP OL SL mc HC HLOC Hhl HR0.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC_keep m1 m HAG0 HLOC) as (C16 & C56 & C40 & C32 & C24 & C48). clear HAG0.
  open_ciT HC.
  destruct HR0 as (P22 & P26 & P25 & P10 & P11 & P12 & P13 & P14 & P15 & P29 & P16 & P17 & P5 & P6 & P7 & P28 & P2).
  destruct (Z.ltb_spec HL 2) as [Ch|Ch].
  - run 30%nat [true; false] [RVal (EVar 37); RVal (EVar 32)]
        [(22, EVar 33); (26, EAdd (EVar 32) (ELit 2047)); (25, EAdd (EVar 32) (ELit 5300)); (10, EVar 48); (2, EVar 34)]
        [S; T; SP; E; 0; HL; 0; 0; 0; 0; 0; 0; NHP; NDP; NT; NSTP; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    exists R. split; [exact Hms|]. split; [cregs HR Hfr | fr_weak Hfr].
  - run 30%nat [false] [RVal (EVar 37)]
        [(22, EVar 33); (26, EAdd (EVar 32) (ELit 2047)); (25, EAdd (EVar 32) (ELit 5300)); (10, EVar 48); (2, EVar 34)]
        [S; T; SP; E; 0; HL; 0; 0; 0; 0; 0; 0; NHP; NDP; NT; NSTP; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    exists R. split; [exact Hms|]. split; [dregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "c_disp OK". exact I. Qed.

Lemma c_h1 : forall regs m1 m FC HP HL DP OL SL mc,
  CI m1 m (W FC HP HL DP OL SL) -> 0 <= HL < 2 -> 0 <= mc < E ->
  CREGS regs HL mc ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d444 : word) m s6u_rom) (mkst R (0x1d478 : word) m' s6u_rom)
    /\ CI m1 m' (W FC HP (HL + 1) DP OL SL)
    /\ MREGS R HL (if mc <? 2 then mc + 1 else mc) (if mc <? 2 then mc + 1 else 0)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP HL DP OL SL mc HC Hhl Hmc HR0. open_ciT HC.
  destruct HR0 as ((P22 & P25 & P26 & P10 & P2 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P5) & P7 & P29 & P6).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  destruct (Z.ltb_spec mc 2) as [Cm|Cm].
  - pose proof (node_lt2 mc ltac:(lia)) as Hnode.
    run 40%nat [true; false; false] NoReads (CBP ++ [(7, EVar 38); (29, EVar 38); (6, EVar 37)])
        [S; T; SP; E; 0; HL; mc; 0; 0; 0; 0; 0; NHP; NDP; NT; NSTP; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl] ltac:(split; [cregs HR Hfr; rewrite ?Hnode; f_equal; lia | fr_weak Hfr]).
  - pose proof (node_ge2 mc ltac:(lia)) as Hnode.
    run 40%nat [false; false; false] NoReads (CBP ++ [(7, EVar 38); (29, EVar 38); (6, EVar 37)])
        [S; T; SP; E; 0; HL; mc; 0; 0; 0; 0; 0; NHP; NDP; NT; NSTP; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
    blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl] ltac:(split; [cregs HR Hfr; rewrite ?Hnode; f_equal; lia | fr_weak Hfr]).
Qed.

Goal True. idtac "c_h1 OK". exact I. Qed.

Lemma c_h1n : forall regs m1 m FC HP DP OL SL,
  CI m1 m (W FC HP 0 DP OL SL) ->
  CREGS regs 0 (-1) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d444 : word) m s6u_rom) (mkst R (0x1d478 : word) m' s6u_rom)
    /\ CI m1 m' (W FC HP 1 DP OL SL)
    /\ MREGS R 0 0 0
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL HC HR0. open_ciT HC.
  destruct HR0 as ((P22 & P25 & P26 & P10 & P2 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P5) & P7 & P29 & P6).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run 40%nat [true; false; false] NoReads (CBP ++ [(7, ELit 18446744073709551615); (29, ELit 18446744073709551615); (6, ELit 0)])
      [S; T; SP; E; 0; 0; 0; 0; 0; 0; 0; 0; NHP; NDP; NT; NSTP; STP t; dsc_off t; 0; 0] FC DL HP DP BC.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl] ltac:(split; [cregs HR Hfr | fr_weak Hfr]).
Qed.

Goal True. idtac "c_h1n OK". exact I. Qed.



Lemma L2_hl1 : forall FC HP DP OL SL mc,
  L2 (W FC HP 1 DP OL SL) mc =
    (let '(node, mc') := l2node mc in
     (W (arr_set FC node (wrap16 1)) (arr_set HP 2 node) 2 (arr_set DP node (wrap8 0)) (wrap64 (OL - 1))
        (if stree_has t then wrap64 (SL - stree_Len t node) else SL), mc')).
Proof.
  intros. unfold L2. rewrite L2_step by lia. unfold l2node.
  destruct (mc <? 2); (rewrite L2_out by lia); reflexivity.
Qed.

Lemma L2_hl0 : forall FC HP DP OL SL,
  L2 (W FC HP 0 DP OL SL) (-1) =
    (W (arr_set (arr_set FC 0 (wrap16 1)) 1 (wrap16 1)) (arr_set (arr_set HP 1 0) 2 1) 2
        (arr_set (arr_set DP 0 (wrap8 0)) 1 (wrap8 0)) (wrap64 (wrap64 (OL - 1) - 1))
        (if stree_has t then wrap64 ((if stree_has t then wrap64 (SL - stree_Len t 0) else SL) - stree_Len t 1)
         else (if stree_has t then wrap64 (SL - stree_Len t 0) else SL)), 1).
Proof.
  intros. unfold L2. rewrite L2_step by lia. unfold l2node. cbn [Z.ltb Z.compare Pos.compare].
  replace (-1 + 1) with 0 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  rewrite L2_step by lia. unfold l2node. cbn [Z.ltb Z.compare Pos.compare].
  replace (1 + 1) with 2 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  rewrite L2_out by lia. reflexivity.
Qed.

End PhaseC.

End Walk.
End FXG.
