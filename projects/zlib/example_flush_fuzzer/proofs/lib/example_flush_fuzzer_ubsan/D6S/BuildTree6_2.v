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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import BuildTree6_1.
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

Local Ltac open_ci HC :=
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
  cbn [tr_lo tr_hi tr_sdesc R6] in RODS, RODF.

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

Definition stC2 : cfg := CFG FB [] [EVar 1%nat] [0x1ba30] [].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC2 VB fuel dirs rds pins pv FC DL HP DP BC.

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
Proof. intros n. unfold BuildTree6_1.stree_dl. destruct t; cbn [stree_Len]; rewrite ?arr_get_make; reflexivity. Qed.

Lemma stree_dl_bound : forall n, 0 <= n < slen -> 0 <= arr_get stree_dl n < 16.
Proof.
  intros n _. unfold BuildTree6_1.stree_dl. destruct t.
  - pose proof (static_ltree_dl_bound n). lia.
  - pose proof (static_dtree_dl_bound n). lia.
  - rewrite arr_get_make. lia.
Qed.

Lemma slen_ge : STP t <> 0 -> 3 <= slen.
Proof. unfold slen. destruct t; cbn; intros; lia. Qed.

Lemma stree_cells : forall m, trees_rod_clear6 m -> STP t <> 0 ->
  cells s6_segs m (STP t + 2) 4 2 slen (arr_get stree_dl).
Proof.
  intros m HRC Hst. unfold BuildTree6_1.stree_dl, slen. destruct t; cbn [TreesRod.STP].
  - exact (proj2 (static_ltree_cells R6 _ m trod_ok6 HRC)).
  - exact (proj2 (static_dtree_cells R6 _ m trod_ok6 HRC)).
  - exfalso. apply Hst. reflexivity.
Qed.

Lemma stree_pb : forall n, 0 <= n < slen -> pb stree_dl n = arr_get stree_dl n.
Proof. intros n Hn. unfold pb. apply Z.mod_small. pose proof (stree_dl_bound n Hn). lia. Qed.

Lemma STP_rod : STP t <> 0 -> 0x11ae0 <= STP t /\ STP t + 2 + 4 * slen <= 0x12510.
Proof. unfold slen. destruct t; cbn; intros; lia. Qed.


Definition DREGS (R : bvmap 5 word) (hl mc : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 21 = zw (S + 2047)
  /\ getr R 10 = zw E /\ getr R 11 = zw (S + dsc_off t) /\ getr R 12 = zw (STP t)
  /\ getr R 2 = zw SP /\ getr R 19 = zw mc /\ getr R 14 = zw hl.

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

Local Ltac dregs HR Hfr := unfold DREGS; repeat split; reg1 HR Hfr.

Lemma c0_blk : forall regs m1 m FC HP HL DP OL SL mc,
  CI m1 m (W FC HP HL DP OL SL) -> 2 <= HL < 600 -> (mc = -1 \/ 0 <= mc < E) ->
  L1REGS regs E mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (W FC HP HL DP OL SL)
    /\ DREGS R HL mc
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP HL DP OL SL mc HC Hhl Hmc HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run 30%nat [false] [RVal (EVar 37)]
      [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
       (10, EVar 35); (2, EVar 34); (12, EVar 49)]
      [S; T; SP; E; 0; HL; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; STP t; 0; dsc_off t] FC DL HP DP BC.
  exists R, m. split; [exact Hms|]. split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]]|].
  split; [dregs HR Hfr | fr_weak Hfr].
Qed.

Definition CP (mce : expr) : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
   (10, EVar 35); (2, EVar 34); (12, EVar 49); (19, mce); (13, ELit 4096)].

Definition stC2m : cfg := CFG FB [] [EVar 1%nat] [0x1ba30; 0x1c280] [].
Local Ltac runm fuel dirs rds pins pv FC DL HP DP BC := run_with stC2m VB fuel dirs rds pins pv FC DL HP DP BC.

Definition MREGS2 (R : bvmap 5 word) (node mc : Z) : Prop :=
  getr R 9 = zw S /\ getr R 18 = zw T /\ getr R 20 = zw (S + 5300) /\ getr R 21 = zw (S + 2047)
  /\ getr R 10 = zw E /\ getr R 11 = zw (S + dsc_off t) /\ getr R 12 = zw (STP t)
  /\ getr R 2 = zw SP /\ getr R 19 = zw mc /\ getr R 14 = zw (node * 4) /\ getr R 13 = zw 2.

Local Ltac mregs HR Hfr := unfold MREGS2; repeat split; reg1 HR Hfr.

Lemma c1a_blk : forall regs m1 m FC HP DP OL SL mc,
  CI m1 m (W FC HP 1 DP OL SL) -> 0 <= mc < 2 ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  L1REGS regs E mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1c280 : word) m' s6_rom)
    /\ CI m1 m' (W (arr_set FC (mc + 1) (wrap16 1)) (arr_set HP 2 (mc + 1)) 2 (arr_set DP (mc + 1) (wrap8 0)) OL SL)
    /\ MREGS2 R (mc + 1) (mc + 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL mc HC Hmc LFC LHP LDP HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof (node_lt2 mc ltac:(lia)) as Hnode.
  runm 80%nat [true; true] [RVal (ELit 1)] (CP (EVar 38))
      [S; T; SP; E; 0; 1; mc; 0; 0; 0; 0; 0; 0; 0; 0; 0; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
  all: rewrite ?Hnode. all: side_closer.
  rewrite ?Hnode in Hms.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl; KHeap 2; KFc (mc + 1); KDepth (mc + 1)]
    ltac:(split; [mregs HR Hfr; rewrite ?Hnode; f_equal; lia | fr_weak Hfr]).
Qed.

Lemma c2a_blk : forall regs m1 m FC HP DP OL SL mc,
  CI m1 m (W FC HP 1 DP OL SL) -> 2 <= mc < E ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  L1REGS regs E mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1c280 : word) m' s6_rom)
    /\ CI m1 m' (W (arr_set FC 0 (wrap16 1)) (arr_set HP 2 0) 2 (arr_set DP 0 (wrap8 0)) OL SL)
    /\ MREGS2 R 0 mc
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL mc HC Hmc LFC LHP LDP HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof (node_ge2 mc ltac:(lia)) as Hnode.
  runm 80%nat [true; false] [RVal (ELit 1)] (CP (EVar 38))
      [S; T; SP; E; 0; 1; mc; 0; 0; 0; 0; 0; 0; 0; 0; 0; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
  all: rewrite ?Hnode. all: side_closer.
  rewrite ?Hnode in Hms.
  blk_fin Hms HR Hfr HB HRC HAG MS MP MF HFf [KHl; KHeap 2; KFc 0; KDepth 0]
    ltac:(split; [mregs HR Hfr; rewrite ?Hnode; f_equal; lia | fr_weak Hfr]).
Qed.

Local Ltac ceq :=
  first [ reflexivity
        | rewrite ?arr_set_set_same; reflexivity
        | nf; rewrite ?stree_pb by lia; rewrite ?wrap64_mod_add, ?wrap64_mod_sub, ?wrap64_sub_l; first [reflexivity | f_equal; lia] ].

Local Ltac blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf ks :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwdT HB M ks ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [ split; [ eapply BR_eqst; [exact HB2|]; clear HB2; st_eqT; ceq
                          | split; [ rod_tower HRC MS MP MF
                                   | split; [ ag_tower HAG
                                            | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                                              repeat (apply wbytes_grows); apply MF; exact Hx ] ] ]
                 | split; [dregs HR Hfr | fr_weak Hfr] ]
      end
  end.

Definition MP2 : list (Z * expr) :=
  [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
   (10, EVar 35); (2, EVar 34); (12, EVar 49); (19, EVar 38); (14, EShl (EVar 36) 2); (13, ELit 2)].

Lemma cms_blk : forall regs m1 m FC HP DP OL SL node mc,
  CI m1 m (W FC HP 2 DP OL SL) -> 0 <= node <= 2 -> (mc = -1 \/ 0 <= mc < E) -> STP t <> 0 ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  MREGS2 regs node mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c280 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (W FC HP 2 DP (wrap64 (OL - 1)) (wrap64 (SL - arr_get stree_dl node)))
    /\ DREGS R 2 mc
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL node mc HC Hnode Hmc Hst ROL RSL HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P19 & P14 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof (stree_cells m HRC Hst) as Cstl. pose proof stree_dl_bound as Rstl.
  pose proof (slen_ge Hst) as Hsl. pose proof (STP_rod Hst) as Hstr.
  destruct Hmc as [Hmc|Hmc].
  - subst mc.
    run 40%nat [false; true] [RVal (EVar 46); RVal (EApp1 6 (EVar 36)); RVal (EVar 47); RVal (ELit 2)]
        [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
         (10, EVar 35); (2, EVar 34); (12, EVar 49); (19, ELit 18446744073709551615); (14, EShl (EVar 36) 2); (13, ELit 2)]
        [S; T; SP; E; node; 2; 0; 0; 0; 0; 0; 0; 0; 0; OL; SL; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW; KStatW].
  - run 40%nat [false; true] [RVal (EVar 46); RVal (EApp1 6 (EVar 36)); RVal (EVar 47); RVal (ELit 2)] MP2
        [S; T; SP; E; node; 2; mc; 0; 0; 0; 0; 0; 0; 0; OL; SL; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW; KStatW].
Qed.

Lemma cmn_blk : forall regs m1 m FC HP DP OL SL node mc,
  CI m1 m (W FC HP 2 DP OL SL) -> 0 <= node <= 2 -> (mc = -1 \/ 0 <= mc < E) -> STP t = 0 ->
  0 <= OL < 2 ^ 64 ->
  MREGS2 regs node mc ->
  exists R m',
    msteps s6_segs (mkst regs (0x1c280 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (W FC HP 2 DP (wrap64 (OL - 1)) SL)
    /\ DREGS R 2 mc
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL node mc HC Hnode Hmc Hst ROL HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P19 & P14 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS. rewrite Hst in P12.
  destruct Hmc as [Hmc|Hmc].
  - subst mc.
    run 40%nat [true; true] [RVal (EVar 46); RVal (ELit 2)]
        [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
         (10, EVar 35); (2, EVar 34); (12, ELit 0); (19, ELit 18446744073709551615); (14, EShl (EVar 36) 2); (13, ELit 2)]
        [S; T; SP; E; node; 2; 0; 0; 0; 0; 0; 0; 0; 0; OL; 0; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW].
    all: rewrite Hst; reg1 HR Hfr.
  - run 40%nat [true; true] [RVal (EVar 46); RVal (ELit 2)]
        [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
         (10, EVar 35); (2, EVar 34); (12, ELit 0); (19, EVar 38); (14, EShl (EVar 36) 2); (13, ELit 2)]
        [S; T; SP; E; node; 2; mc; 0; 0; 0; 0; 0; 0; 0; OL; 0; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
    blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW].
    all: rewrite Hst; reg1 HR Hfr.
Qed.

Lemma c3_blk : forall regs m1 m FC HP DP OL SL,
  CI m1 m (W FC HP 0 DP OL SL) -> STP t <> 0 ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  L1REGS regs E (-1) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (W (arr_set (arr_set FC 0 (wrap16 1)) 1 (wrap16 1)) (arr_set (arr_set HP 1 0) 2 1) 2
                  (arr_set (arr_set DP 0 (wrap8 0)) 1 (wrap8 0))
                  (wrap64 (OL - 1 - 1)) (wrap64 (SL - arr_get stree_dl 0 - arr_get stree_dl 1)))
    /\ DREGS R 2 1
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL HC Hst ROL RSL LFC LHP LDP HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof (stree_cells m HRC Hst) as Cstl. pose proof stree_dl_bound as Rstl.
  pose proof (slen_ge Hst) as Hsl. pose proof (STP_rod Hst) as Hstr.
  run 120%nat [true; true; false; false; true; false; true]
      [RVal (ELit 0); RVal (EVar 46); RVal (EApp1 6 (ELit 0)); RVal (EVar 47); RVal (EApp1 6 (ELit 1))]
      (CP (ELit 18446744073709551615))
      [S; T; SP; E; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; OL; SL; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
  blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf
    [KHl; KHeap 1; KFc 0; KDepth 0; KOptW; KStatW; KHl; KHeap 2; KFc 1; KDepth 1; KOptW; KStatW].
Qed.

Lemma n3_blk : forall regs m1 m FC HP DP OL SL,
  CI m1 m (W FC HP 0 DP OL SL) -> STP t = 0 ->
  0 <= OL < 2 ^ 64 ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  L1REGS regs E (-1) ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (W (arr_set (arr_set FC 0 (wrap16 1)) 1 (wrap16 1)) (arr_set (arr_set HP 1 0) 2 1) 2
                  (arr_set (arr_set DP 0 (wrap8 0)) 1 (wrap8 0)) (wrap64 (OL - 1 - 1)) SL)
    /\ DREGS R 2 1
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m FC HP DP OL SL HC Hst ROL LFC LHP LDP HR0.
  open_ci HC. destruct HR0 as (P9 & P18 & P20 & P21 & P10 & P11 & P12 & P2 & P14 & P15 & P16 & P17 & P5 & P19 & P13).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS. rewrite Hst in P12.
  run 120%nat [true; true; true; false; true; true; true]
      [RVal (ELit 0); RVal (EVar 46)]
      [(9, EVar 32); (18, EVar 33); (20, EAdd (EVar 32) (ELit 5300)); (21, EAdd (EVar 32) (ELit 2047));
       (10, EVar 35); (2, EVar 34); (12, ELit 0); (19, ELit 18446744073709551615); (13, ELit 4096)]
      [S; T; SP; E; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; OL; 0; SDA t; STP t; 0; dsc_off t] FC DL HP DP BC.
  blk_finC Hms HR Hfr HB HRC HAG MS MP MF HFf
    [KHl; KHeap 1; KFc 0; KDepth 0; KOptW; KHl; KHeap 2; KFc 1; KDepth 1; KOptW].
  all: rewrite Hst; reg1 HR Hfr.
Qed.

End PhaseC.


Lemma c_phase : forall regs m1 m DL HP HL DP mc,
  let FC := tree_fc ds t in let BC := ds_bl_count ds in let OL := ds_opt_len ds in let SL := ds_static_len ds in
  let MC0 := max_code ds t in
  CI m1 m (U FC DL HP HL 573 DP BC OL SL MC0) ->
  0 <= HL <= E -> (mc = -1 /\ HL = 0 \/ 0 <= mc < E /\ 1 <= HL) ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536) ->
  arr_len FC = tsize t -> arr_len HP = 573 -> arr_len DP = 573 ->
  0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  L1REGS regs E mc ->
  exists R m' FC2 HP2 HL2 DP2 OL2 SL2 mc2,
    L2 (U FC DL HP HL 573 DP BC OL SL MC0) mc = (U FC2 DL HP2 HL2 573 DP2 BC OL2 SL2 MC0, mc2)
    /\ msteps s6_segs (mkst regs (0x1ba24 : word) m s6_rom) (mkst R (0x1ba30 : word) m' s6_rom)
    /\ CI m1 m' (U FC2 DL HP2 HL2 573 DP2 BC OL2 SL2 MC0)
    /\ DREGS R HL2 mc2
    /\ 2 <= HL2 <= E /\ 0 <= mc2 < E
    /\ arr_len FC2 = tsize t /\ arr_len HP2 = 573 /\ arr_len DP2 = 573
    /\ 0 <= OL2 < 2 ^ 64 /\ 0 <= SL2 < 2 ^ 64
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL HP HL DP mc FC BC OL SL MC0 HC Hhl Hinv RFC LFC LHP LDP ROL RSL HR0.
  pose proof elems_range as He. pose proof tsize_elems as Hte.
  assert (W64 : forall z, 0 <= wrap64 z < 2 ^ 64) by (intros z; apply wrap64_range).
  assert (FRT : forall (R1 R2 : bvmap 5 word) rs,
            (forall r : reg, reg_in r CLOBI = false -> getr R1 r = getr rs r) ->
            (forall r : reg, reg_in r CLOBI = false -> getr R2 r = getr R1 r) ->
            forall r : reg, reg_in r CLOBI = false -> getr R2 r = getr rs r).
  { intros R1 R2 rs H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). }
  destruct (Z_le_gt_dec 2 HL) as [Chl|Chl].
  -
    destruct (c0_blk DL 573 BC MC0 regs m1 m FC HP HL DP OL SL mc HC ltac:(lia) ltac:(lia) HR0)
      as (R1 & m2 & Hms1 & HC1 & HD1 & Hfr1).
    exists R1, m2, FC, HP, HL, DP, OL, SL, mc. split; [apply L2_ge2; lia|].
    split; [exact Hms1|]. split; [exact HC1|]. split; [exact HD1|].
    split; [lia|]. split; [lia|]. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [exact ROL|]. split; [exact RSL|]. exact Hfr1.
  - destruct (Z.eq_dec HL 1) as [Chl1|Chl1].
    +
      subst HL. assert (Hmc : 0 <= mc < E) by lia.
      rewrite (L2_hl1 DL 573 BC MC0 FC HP DP OL SL mc). unfold l2node.
      destruct (Z.ltb_spec mc 2) as [Cm|Cm]; cbv beta iota zeta.
      * destruct (c1a_blk DL 573 BC MC0 regs m1 m FC HP DP OL SL mc HC ltac:(lia) LFC LHP LDP HR0)
          as (R1 & m2 & Hms1 & HC1 & HM1 & Hfr1).
        destruct (Z.eqb_spec (STP t) 0) as [Cs|Cs].
        -- replace (stree_has t) with false
             by (symmetry; destruct (stree_has t) eqn:Es; [exfalso; exact (proj1 stree_has_STP Es Cs) | reflexivity]).
           destruct (cmn_blk DL 573 BC MC0 R1 m1 m2 _ _ _ OL SL (mc + 1) (mc + 1) HC1 ltac:(lia) ltac:(lia) Cs ROL HM1)
             as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
           eexists R2, m3, _, _, 2, _, _, SL, (mc + 1). split; [reflexivity|].
           split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HD2|].
           split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
           split; [apply W64|]. split; [exact RSL|]. exact (FRT _ _ _ Hfr1 Hfr2).
        -- replace (stree_has t) with true by (symmetry; apply (proj2 stree_has_STP); exact Cs).
           rewrite !stree_Len_dl.
           destruct (cms_blk DL 573 BC MC0 R1 m1 m2 _ _ _ OL SL (mc + 1) (mc + 1) HC1 ltac:(lia) ltac:(lia) Cs ROL RSL HM1)
             as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
           eexists R2, m3, _, _, 2, _, _, _, (mc + 1). split; [reflexivity|].
           split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HD2|].
           split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
           split; [apply W64|]. split; [apply W64|]. exact (FRT _ _ _ Hfr1 Hfr2).
      * destruct (c2a_blk DL 573 BC MC0 regs m1 m FC HP DP OL SL mc HC ltac:(lia) LFC LHP LDP HR0)
          as (R1 & m2 & Hms1 & HC1 & HM1 & Hfr1).
        destruct (Z.eqb_spec (STP t) 0) as [Cs|Cs].
        -- replace (stree_has t) with false
             by (symmetry; destruct (stree_has t) eqn:Es; [exfalso; exact (proj1 stree_has_STP Es Cs) | reflexivity]).
           destruct (cmn_blk DL 573 BC MC0 R1 m1 m2 _ _ _ OL SL 0 mc HC1 ltac:(lia) ltac:(lia) Cs ROL HM1)
             as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
           eexists R2, m3, _, _, 2, _, _, SL, mc. split; [reflexivity|].
           split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HD2|].
           split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
           split; [apply W64|]. split; [exact RSL|]. exact (FRT _ _ _ Hfr1 Hfr2).
        -- replace (stree_has t) with true by (symmetry; apply (proj2 stree_has_STP); exact Cs).
           rewrite !stree_Len_dl.
           destruct (cms_blk DL 573 BC MC0 R1 m1 m2 _ _ _ OL SL 0 mc HC1 ltac:(lia) ltac:(lia) Cs ROL RSL HM1)
             as (R2 & m3 & Hms2 & HC2 & HD2 & Hfr2).
           eexists R2, m3, _, _, 2, _, _, _, mc. split; [reflexivity|].
           split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HC2|]. split; [exact HD2|].
           split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
           split; [apply W64|]. split; [apply W64|]. exact (FRT _ _ _ Hfr1 Hfr2).
    +
      assert (HL = 0) by lia. subst HL. assert (mc = -1) by lia. subst mc.
      rewrite (L2_hl0 DL 573 BC MC0 FC HP DP OL SL).
      destruct (Z.eqb_spec (STP t) 0) as [Cs|Cs].
      * replace (stree_has t) with false
          by (symmetry; destruct (stree_has t) eqn:Es; [exfalso; exact (proj1 stree_has_STP Es Cs) | reflexivity]).
        destruct (n3_blk DL 573 BC MC0 regs m1 m FC HP DP OL SL HC Cs ROL LFC LHP LDP HR0)
          as (R1 & m2 & Hms1 & HC1 & HD1 & Hfr1).
        eexists R1, m2, _, _, 2, _, _, SL, 1. split; [rewrite wrap64_sub_l; reflexivity|].
        split; [exact Hms1|]. split; [exact HC1|]. split; [exact HD1|].
        split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
        split; [apply W64|]. split; [exact RSL|]. exact Hfr1.
      * replace (stree_has t) with true by (symmetry; apply (proj2 stree_has_STP); exact Cs).
        rewrite !stree_Len_dl.
        destruct (c3_blk DL 573 BC MC0 regs m1 m FC HP DP OL SL HC Cs ROL RSL LFC LHP LDP HR0)
          as (R1 & m2 & Hms1 & HC1 & HD1 & Hfr1).
        eexists R1, m2, _, _, 2, _, _, _, 1. split; [rewrite !wrap64_sub_l; reflexivity|].
        split; [exact Hms1|]. split; [exact HC1|]. split; [exact HD1|].
        split; [lia|]. split; [lia|]. rewrite !arr_len_set. split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|].
        split; [apply W64|]. split; [apply W64|]. exact Hfr1.
Qed.

End Walk.
End FXG.
