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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_pq.
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


Section Pq.
Variables (FC DL : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Abbreviation W h := (U FC DL h HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis RDP : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.
Hypothesis Hhl : 1 <= HL <= 572.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LDP : arr_len DP = 573.

Local Abbreviation pqF := BuildTree6u_pq.pqF.
Local Abbreviation smal := (BuildTree6u_pq.smal FC DP).
Local Abbreviation sel := (BuildTree6u_pq.sel FC HL DP).
Local Abbreviation PQ := (BuildTree6u_pq.PQ t HL).
Local Abbreviation PQF := (BuildTree6u_pq.PQF sp).
Local Abbreviation DI := (BuildTree6u_pq.DI F mem0 S p PBL ds sp t FC DL HL HM DP BC OL SL MC).
Local Abbreviation QB := (BuildTree6u_pq.QB S sp t).
Local Abbreviation QH := (BuildTree6u_pq.QH S sp t).
Local Abbreviation QM := (BuildTree6u_pq.QM S sp t).
Local Abbreviation QX := (BuildTree6u_pq.QX S sp).
Local Abbreviation CLOBQ := BuildTree6u_pq.CLOBQ.
Local Abbreviation sel_range := (BuildTree6u_pq.sel_range S FC HL DP).
Local Abbreviation smaller_W := (BuildTree6u_pq.smaller_W ds t FC DL HL HM DP BC OL SL MC).
Local Abbreviation DI_write := (BuildTree6u_pq.DI_write F mem0 mem S p PBL ds ra sp t HH FC DL HL HM DP BC OL SL MC Hhl).
Local Abbreviation PQF_write := (BuildTree6u_pq.PQF_write F mem0 mem S p PBL ds ra sp HH).
Local Abbreviation q_pro := (BuildTree6u_pq.q_pro F mem0 mem S p PBL ds ra sp t HH FC DL HL HM DP BC OL SL MC RFC RDP Hhl LFC LDP).
Local Abbreviation q_h := (BuildTree6u_pq.q_h F mem0 mem S p PBL ds ra sp t HH FC DL HL HM DP BC OL SL MC RFC RDP Hhl LFC LDP).
Local Abbreviation q_m := (BuildTree6u_pq.q_m F mem0 mem S p PBL ds ra sp t HH FC DL HL HM DP BC OL SL MC RFC RDP Hhl LFC LDP).

Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : PQ h |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb FC (arr_get h i) = arr_get FC (arr_get h i)) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]);
  assert (PD : wb DP (arr_get h i) = arr_get DP (arr_get h i)) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).

Local Ltac nf3 :=
  cbn [BuildTree6u_pq.pqF];
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
            | cbn [BuildTree6u_pq.pqF]; symex_read_auto
            | nf3; symex_read_auto
            | nf3; symex_store_auto
            | nf3; symex_sok_auto
            | nf3; zc3
            | intros; cbn [BuildTree6u_pq.pqF]; first [apply pb_range | apply hv_range | apply wb_range] ].

Local Ltac run3 fuel dirs rds pins pv h :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VBq in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs stCq fuel dirs rdv pinsv vbv NoRegions pv NoVals (BuildTree6u_pq.pqF FC h DP) F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer3
  end.

Local Ltac open_di HD :=
  let HC := fresh "HC" in let HPQ := fresh "HPQ" in let HLh := fresh "HLh" in
  destruct HD as (HC & HPQ & HLh); open_ciT HC.

Local Ltac rod1 HRC MS := apply (trees_rod_clear_wbytes R6u _ _ _ HRC); [intros x Hx; apply MS; rewrite ?length_Z_to_le_bytes in Hx; cbn in Hx; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia].
Local Ltac ag1 HAG := apply agree_out_wbytes; [exact HAG | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; unfold BuildTree6u_1.GB; apply sub_franges_here; unfold dsl_SIZE; cbn; lia].
Local Ltac write1 m1 m h k x HD0 HRC MS HAG :=
  apply (DI_write m1 m h k x); [exact HD0 | rod1 HRC MS | ag1 HAG | lia | lia | lia | nf3; first [reflexivity | lia]].

Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz He. apply ret_ok_even. rewrite u_zw_small by exact Hz. exact He. Qed.

Lemma q_x : forall regs m h v k' m1 regs0 (raq : word),
  DI m1 m h -> PQF m regs0 -> QX regs v k' -> 1 <= k' <= HL -> 0 <= v < tsize t ->
  getr regs 1 = raq -> ret_ok raq ->
  exists R m', msteps s6u_segs (mkst regs (0x1e044 : word) m s6u_rom) (mkst R raq m' s6u_rom)
    /\ DI m1 m' (arr_set h k' v)
    /\ getr R 2 = zw SP
    /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9 /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19
    /\ getr R 20 = getr regs0 20 /\ getr R 21 = getr regs0 21 /\ getr R 22 = getr regs0 22
    /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r).
Proof.
  intros regs m h v k' m1 regs0 raq HD HF HX Hk Hv P1 Hrq. pose proof HD as HD0. open_di HD.
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  destruct HX as (P12 & P14 & P8 & P2).
  destruct HF as (C8 & C9 & C18 & C19 & C20 & C21 & C22).
  pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof (u64_range (getr regs0 20)) as U20. pose proof (u64_range (getr regs0 21)) as U21.
  pose proof (u64_range (getr regs0 22)) as U22.
  run3 30%nat NoDirs
      [RVal (EVar 41); RVal (EVar 42); RVal (EVar 43); RVal (EVar 46); RVal (EVar 47); RVal (EVar 48); RVal (EVar 49)] QXP
      [S; T; 0; v; k'; HL; 0; 0; SP; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18); NHP; NDP;
       bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21); bv_unsigned (getr regs0 22); 0; 0] h.
  first [rewrite P1 in Hms | idtac].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [write1 m1 m h k' v HD0 HRC MS HAG |]
  end.
  repeat match goal with |- _ /\ _ => split end;
    try (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; cbn [pqF]; rewrite ?zw_u; first [reflexivity | f_equal; lia] end).
  fr_weak Hfr.
Qed.

Goal True. idtac "q_x OK". exact I. Qed.



Lemma loop_S_sel : forall f h v k j, j <= HL ->
  pqdownheap_loop (Datatypes.S f) (W h) t v k j =
    if smal v (arr_get h (sel h j)) then (W h, k)
    else pqdownheap_loop f (W (arr_set h k (arr_get h (sel h j)))) t v (sel h j) (sel h j * 2).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. autorewrite with btupd.
  replace (j <=? HL) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  autorewrite with btupd. rewrite !smaller_W. unfold BuildTree6u_pq.sel.
  destruct ((j <? HL) && smal (arr_get h (j + 1)) (arr_get h j)).
  - destruct (smal v (arr_get h (j + 1))); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
  - destruct (smal v (arr_get h j)); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
Qed.

Lemma q_inner : forall fuel regs m1 m h v j k regs0,
  DI m1 m h -> PQF m regs0 -> QH regs v j k HL -> 1 <= k -> j = k * 2 -> j <= HL -> 0 <= v < tsize t ->
  HL < j * 2 ^ Z.of_nat fuel ->
  let '(s', k') := pqdownheap_loop fuel (W h) t v k j in
  exists R m', msteps s6u_segs (mkst regs (0x1ded0 : word) m s6u_rom) (mkst R (0x1e044 : word) m' s6u_rom)
    /\ DI m1 m' (ds_heap s') /\ PQF m' regs0
    /\ QX R v k' /\ 1 <= k' <= HL
    /\ (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r).
Proof.
  induction fuel as [|f IH]; intros regs m1 m h v j k regs0 HD HF HRg Hk Hjk Hj Hv Hfuel.
  - exfalso. change (2 ^ Z.of_nat 0) with 1 in Hfuel. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
    rewrite loop_S_sel by lia.
    pose proof (sel_range h j ltac:(lia)) as Hsel.
    destruct (q_h regs m h v j k m1 HD HRg Hk Hjk Hj Hv) as (R1 & Hms1 & HM1 & Hfr1).
    pose proof (q_m R1 m h v j k (sel h j) m1 regs0 HD HF HM1 ltac:(lia) ltac:(lia) ltac:(lia) Hv) as HB.
    destruct (smal v (arr_get h (sel h j))).
    + destruct HB as (R2 & Hms2 & HX2 & Hfr2). autorewrite with btupd.
      exists R2, m. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HD|]. split; [exact HF|]. split; [exact HX2|]. split; [lia|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (Z.leb_spec (sel h j * 2) HL) as [C4|C4].
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HF2 & HR2 & Hfr2).
        specialize (IH R2 m1 m2 (arr_set h k (arr_get h (sel h j))) v (sel h j * 2) (sel h j) regs0
                       HD2 HF2 HR2 ltac:(lia) ltac:(lia) C4 Hv ltac:(nia)).
        destruct (pqdownheap_loop f _ t v (sel h j) (sel h j * 2)) as [s' k'].
        destruct IH as (R3 & m3 & Hms3 & HD3 & HF3 & HX3 & Hk3 & Hfr3).
        exists R3, m3. split.
        { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
        split; [exact HD3|]. split; [exact HF3|]. split; [exact HX3|]. split; [exact Hk3|].
        intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
      * destruct HB as (R2 & m2 & Hms2 & HD2 & HF2 & HX2 & Hfr2).
        rewrite pqdownheap_loop_out by (autorewrite with btupd; lia). autorewrite with btupd.
        exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HD2|]. split; [exact HF2|]. split; [exact HX2|]. split; [lia|].
        intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "q_inner OK". exact I. Qed.

Theorem pq_run : forall regs m1 m h k (raq : word),
  DI m1 m h -> 1 <= k <= HL ->
  getr regs 10 = zw S -> getr regs 11 = zw T -> getr regs 12 = zw k -> getr regs 2 = zw SP ->
  getr regs 1 = raq -> ret_ok raq ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1de0c : word) m s6u_rom) (mkst R raq m' s6u_rom)
    /\ DI m1 m' (ds_heap (pqdownheap (W h) t k))
    /\ getr R 2 = zw SP
    /\ (forall r : reg, reg_in r PQ_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h k raq HD Hk P10 P11 P12 P2 P1 Hrq.
  pose proof HD as (_ & HPQ & HLh).
  assert (Rv : 0 <= arr_get h k < tsize t) by (apply HPQ; lia).
  assert (FIN : forall R : bvmap 5 word,
            getr R 2 = zw SP ->
            getr R 8 = getr regs 8 -> getr R 9 = getr regs 9 -> getr R 18 = getr regs 18 -> getr R 19 = getr regs 19 ->
            getr R 20 = getr regs 20 -> getr R 21 = getr regs 21 -> getr R 22 = getr regs 22 ->
            (forall r : reg, reg_in r CLOBQ = false -> getr R r = getr regs r) ->
            forall r : reg, reg_in r PQ_CLOB = false -> getr R r = getr regs r).
  { intros R W2 W8 W9 W18 W19 W20 W21 W22 Hfr.
    apply (frame_fix R regs 2%bv); [rewrite W2, P2; reflexivity|].
    apply (frame_fix R regs 8%bv); [exact W8|]. apply (frame_fix R regs 9%bv); [exact W9|].
    apply (frame_fix R regs 18%bv); [exact W18|]. apply (frame_fix R regs 19%bv); [exact W19|].
    apply (frame_fix R regs 20%bv); [exact W20|]. apply (frame_fix R regs 21%bv); [exact W21|].
    apply (frame_fix R regs 22%bv); [exact W22|].
    intros r Hr. apply Hfr. eapply reg_in_sub; [| exact Hr]. reflexivity. }
  destruct (q_pro regs m1 m h k HD Hk P10 P11 P12 P2) as (R1 & m2 & Hms1 & HD1 & HF1 & HX1 & Hfr1).
  unfold pqdownheap. autorewrite with btupd. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (Z.ltb_spec HL (k * 2)) as [Ck|Ck].
  - rewrite pqdownheap_loop_out by (autorewrite with btupd; lia).
    rewrite heap_set_shape, ds_heap_set_heap. autorewrite with btupd.
    destruct (q_x R1 m2 h (arr_get h k) k m1 regs raq HD1 HF1 HX1 Hk Rv ltac:(rewrite (Hfr1 1%bv eq_refl); exact P1) Hrq)
      as (R2 & m3 & Hms2 & HD2 & W2 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & Hfr2).
    exists R2, m3. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HD2|]. split; [exact W2|].
    apply FIN; try assumption. intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - pose proof (q_inner 32 R1 m1 m2 h (arr_get h k) (k * 2) k regs HD1 HF1 HX1 ltac:(lia) eq_refl ltac:(lia) Rv
                  ltac:(change (2 ^ Z.of_nat 32) with 4294967296; lia)) as HI.
    destruct (pqdownheap_loop 32 (W h) t (arr_get h k) k (k * 2)) as [s' k'] eqn:EL.
    destruct HI as (R2 & m3 & Hms2 & HD2 & HF2 & HX2 & Hk2 & Hfr2).
    rewrite heap_set_shape, ds_heap_set_heap.
    destruct (q_x R2 m3 (ds_heap s') (arr_get h k) k' m1 regs raq HD2 HF2 HX2 Hk2 Rv
                ltac:(rewrite (Hfr2 1%bv eq_refl), (Hfr1 1%bv eq_refl); exact P1) Hrq)
      as (R3 & m4 & Hms3 & HD3 & W2 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & Hfr3).
    exists R3, m4. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
    split; [exact HD3|]. split; [exact W2|].
    apply FIN; try assumption. intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "pq_run OK". exact I. Qed.

End Pq.
End Walk.
End FXG.
