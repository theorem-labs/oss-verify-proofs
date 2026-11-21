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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_pq BuildTree6u_pq2.
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
Local Abbreviation DREGS := (BuildTree6u_2.DREGS S sp t).


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


Definition stC3 : cfg := CFG FB [] [EVar 1%nat] [0x1de0c; 0x1cc08] [].
Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC3 VB fuel dirs rds pins pv FC DL HP DP BC.

Section PhaseD.
Variables (FC DL : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z).
Local Abbreviation W h := (U FC DL h HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis RDP : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.
Hypothesis Hhl : 2 <= HL <= 572.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LDP : arr_len DP = 573.
Hypothesis Hmc : 0 <= MC < 600.
Let Hhl' : 1 <= HL <= 572 := conj (Z.le_trans 1 2 HL ltac:(lia) (proj1 Hhl)) (proj2 Hhl).

Local Abbreviation PQ := (BuildTree6u_pq.PQ t HL).
Local Abbreviation DI := (BuildTree6u_pq.DI F mem0 S p PBL ds sp t FC DL HL HM DP BC OL SL MC).
Local Abbreviation pq_run := (BuildTree6u_pq2.pq_run F mem0 mem S p PBL ds ra sp t HH FC DL HL HM DP BC OL SL MC RFC RDP Hhl' LFC LDP).

Definition OREGS (R : bvmap 5 word) (n : Z) : Prop :=
  getr R 10 = zw S /\ getr R 11 = zw T /\ getr R 12 = zw n /\ getr R 1 = zw 0x1cc00
  /\ getr R 8 = zw 1 /\ getr R 19 = zw n /\ getr R 20 = zw S /\ getr R 22 = zw T
  /\ getr R 24 = zw (S + 2976) /\ getr R 25 = zw (S + 5300) /\ getr R 26 = zw (S + 2047) /\ getr R 2 = zw SP.
Definition EREGS (R : bvmap 5 word) : Prop :=
  getr R 20 = zw S /\ getr R 22 = zw T /\ getr R 24 = zw (S + 2976) /\ getr R 25 = zw (S + 5300)
  /\ getr R 26 = zw (S + 2047) /\ getr R 2 = zw SP.

Local Ltac oregs HR Hfr := unfold OREGS, EREGS; repeat split; reg1 HR Hfr.


Lemma d_pro : forall regs m1 m h MC0 regs0,
  CI m1 m (U FC DL h HL HM DP BC OL SL MC0) -> LOC m1 -> FRM m1 regs0 -> PQ h -> arr_len h = 573 ->
  DREGS regs HL MC ->
  exists R m', msteps s6u_segs (mkst regs (0x1cbd0 : word) m s6u_rom) (mkst R (0x1de0c : word) m' s6u_rom)
    /\ DI m' m' h /\ LOC m' /\ FRM m' regs0 /\ cell s6u_segs m' (SP + 8) 8 MC
    /\ OREGS R (HL / 2)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h MC0 regs0 HC HLOC HFRM HPQ HLh HDR.
  pose proof HC as (_ & _ & HAG0 & _). pose proof (LOC_keep m1 m HAG0 HLOC) as HLOCm.
  pose proof HLOCm as (C16 & C56 & C40 & C32 & C24 & C48).
  assert (HFRMm : FRM m regs0).
  { pose proof Hcf as (_ & _ & _ & HfS & _). unfold dsl_SIZE in HfS. pose proof Hsp as Hsp'.
    unfold BuildTree6u_1.FRM in HFRM |- *.
    repeat match goal with |- _ /\ _ => split end;
      (eapply BuildTree6u_1.loc_cell; [exact HH | exact HAG0 | unfold dsl_SIZE; lia | lia |]);
      repeat match type of HFRM with _ /\ _ => let X := fresh in destruct HFRM as [X HFRM]; try exact X end; try exact HFRM. }
  clear HAG0.
  open_ci HC. destruct HDR as (P22 & P25 & P26 & P2 & P29 & P6).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  run 30%nat NoDirs [RVal (EAdd (EVar 32) (EVar 49)); RVal (EVar 32)]
      [(22, EVar 33); (25, EAdd (EVar 32) (ELit 5300)); (26, EAdd (EVar 32) (ELit 2047)); (2, EVar 34); (29, EVar 38); (6, EVar 37)]
      [S; T; SP; E; 0; HL; MC; 0; 0; 0; 0; 0; NHP; NDP; NT; 0; STP t; dsc_off t; 0; 0] FC DL h DP BC.
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      br_fwdT HB M [KOther; KMc] ltac:(oth HFf);
      lazymatch goal with
      | HB2 : BR _ _ _ _ _ _ _ _ _ M _ |- _ =>
          split; [ split; [ split; [exact HB2 | split; [rod_tower HRC MS MP MF | split; [apply agree_out_refl | intros x Hx; repeat (apply wbytes_grows); apply MF; exact Hx]]]
                          | split; [exact HPQ | exact HLh] ] |]
      end
  end.
  split.
  { unfold BuildTree6u_1.LOC in HLOCm |- *. repeat match goal with |- _ /\ _ => split end;
      (repeat (apply cell_write_other; [ | lia | cbn; lia | lia | cbn; lia | cbn; lia ]));
      repeat match type of HLOCm with _ /\ _ => let X := fresh in destruct HLOCm as [X HLOCm]; try exact X end; try exact HLOCm. }
  split.
  { unfold BuildTree6u_1.FRM in HFRMm |- *. repeat match goal with |- _ /\ _ => split end;
      (repeat (apply cell_write_other; [ | lia | cbn; lia | lia | cbn; lia | cbn; lia ]));
      repeat match type of HFRMm with _ /\ _ => let X := fresh in destruct HFRMm as [X HFRMm]; try exact X end; try exact HFRMm. }
  split; [frame_cells|].
  split; [| fr_weak Hfr].
  unfold OREGS; repeat split;
    (let A := fresh "A" in lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A; nf;
       change (2 ^ 1) with 2; first [reflexivity | assumption | f_equal; lia] end).
Qed.

Goal True. idtac "d_pro OK". exact I. Qed.


Definition LREGS (R : bvmap 5 word) (n : Z) : Prop :=
  getr R 1 = zw 0x1cc00 /\ getr R 8 = zw 1 /\ getr R 19 = zw n /\ getr R 20 = zw S /\ getr R 22 = zw T
  /\ getr R 24 = zw (S + 2976) /\ getr R 25 = zw (S + 5300) /\ getr R 26 = zw (S + 2047) /\ getr R 2 = zw SP.

Lemma d_latch : forall regs m n,
  LREGS regs n -> 1 <= n < 300 ->
  exists R, msteps s6u_segs (mkst regs (0x1cc00 : word) m s6u_rom)
                   (mkst R (if 1 <? n then (0x1de0c : word) else (0x1cc08 : word)) m s6u_rom)
    /\ (if 1 <? n then OREGS R (n - 1) else EREGS R)
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 19]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m n (P1 & P8 & P19 & P20 & P22 & P24 & P25 & P26 & P2) Hn.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof elems_range as He.
  destruct (Z.ltb_spec 1 n) as [Cn|Cn].
  - run 20%nat [true] NoReads
        [(8, ELit 1); (19, EVar 36); (20, EVar 32); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976));
         (25, EAdd (EVar 32) (ELit 5300)); (26, EAdd (EVar 32) (ELit 2047)); (2, EVar 34)]
        [S; T; SP; E; n; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC DL DL DP BC.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
  - run 20%nat [false] NoReads
        [(8, ELit 1); (19, EVar 36); (20, EVar 32); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976));
         (25, EAdd (EVar 32) (ELit 5300)); (26, EAdd (EVar 32) (ELit 2047)); (2, EVar 34)]
        [S; T; SP; E; n; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC DL DL DP BC.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "d_latch OK". exact I. Qed.

Lemma d_step : forall regs m1 m h n,
  DI m1 m h -> OREGS regs n -> 1 <= n -> n * 2 <= HL ->
  exists R m', msteps s6u_segs (mkst regs (0x1de0c : word) m s6u_rom)
                      (mkst R (if 1 <? n then (0x1de0c : word) else (0x1cc08 : word)) m' s6u_rom)
    /\ DI m1 m' (ds_heap (pqdownheap (W h) t n))
    /\ (if 1 <? n then OREGS R (n - 1) else EREGS R)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m h n HD HO Hn1 Hn2.
  destruct HO as (P10 & P11 & P12 & P1 & P8 & P19 & P20 & P22 & P24 & P25 & P26 & P2).
  assert (Hrq : ret_ok (zw 0x1cc00)) by (apply ret_ok_lit; [lia | reflexivity]).
  destruct (pq_run regs m1 m h n (zw 0x1cc00) HD ltac:(lia) P10 P11 P12 P2 P1 Hrq) as (R1 & m2 & Hms1 & HD1 & Q2 & Hfr1).
  symex_pc_lit_in Hms1.
  assert (HL1 : LREGS R1 n).
  { unfold LREGS. rewrite !Hfr1 by reflexivity. repeat split; assumption. }
  destruct (d_latch R1 m2 n HL1 ltac:(lia)) as (R2 & Hms2 & HX2 & Hfr2).
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HD1|]. split; [exact HX2|].
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [| exact Hr]. reflexivity.
Qed.

Goal True. idtac "d_step OK". exact I. Qed.


Definition L3 (h : arr) (n : Z) : deflate_state := build_tree_loop3 (Z.to_nat n) (W h) t n.

Lemma d_loop : forall k n regs m1 m h,
  n <= Z.of_nat k -> DI m1 m h -> OREGS regs n -> 1 <= n -> n * 2 <= HL ->
  exists R m' h', L3 h n = W h'
    /\ msteps s6u_segs (mkst regs (0x1de0c : word) m s6u_rom) (mkst R (0x1cc08 : word) m' s6u_rom)
    /\ DI m1 m' h'
    /\ EREGS R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction k as [|k IH]; intros n regs m1 m h Hk HD HO Hn1 Hn2; [lia|].
  unfold L3. replace (Z.to_nat n) with (Datatypes.S (Z.to_nat (n - 1))) by lia.
  cbn [build_tree_loop3]. replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (pqdownheap_shape (W h) t n). autorewrite with btupd.
  destruct (d_step regs m1 m h n HD HO Hn1 Hn2) as (R1 & m2 & Hms1 & HD1 & HO1 & Hfr1).
  destruct (Z.ltb_spec 1 n) as [Cn|Cn].
  - destruct (IH (n - 1) R1 m1 m2 _ ltac:(lia) HD1 HO1 ltac:(lia) ltac:(lia)) as (R2 & m3 & h' & E2 & Hms2 & HD2 & HO2 & Hfr2).
    unfold L3 in E2. exists R2, m3, h'. split; [exact E2|].
    split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HD2|]. split; [exact HO2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - replace (n - 1) with 0 by lia. replace (Z.to_nat 0) with 0%nat by lia. cbn [build_tree_loop3].
    eexists R1, m2, _. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HD1|]. split; [exact HO1 | exact Hfr1].
Qed.

Goal True. idtac "d_loop OK". exact I. Qed.

End PhaseD.
End Walk.
End FXG.
