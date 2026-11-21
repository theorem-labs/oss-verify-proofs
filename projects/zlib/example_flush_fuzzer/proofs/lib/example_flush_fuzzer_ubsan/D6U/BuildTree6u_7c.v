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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_4 BuildTree6u_6 BuildTree6u_7 BuildTree6u_7b.
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

Local Ltac ag_read :=
  lazymatch goal with
  | |- exists bs, rdn ?sg ?m (zw ?a) ?n = Some bs /\ bytes_le_to_Z bs = arr_get ?tt ?i =>
      match goal with
      | H : cells sg m ?P 4 2%nat ?len (arr_get tt) |- _ =>
          eapply (fc_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      | H : cells sg m ?P 4 4%nat ?len (arr_get tt) |- _ =>
          eapply (u32_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      | H : cells sg m ?P 2 2%nat ?len (arr_get tt) |- _ =>
          eapply (u16_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | change (2 ^ 1) with 2; lia | reflexivity]
      | H : cells sg m ?P 1 1%nat ?len (arr_get tt) |- _ =>
          eapply (bytes_read_at sg m P len (arr_get tt) i a _ H); [lia | arr_range_auto | lia | reflexivity]
      end
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
            | nf; vfix; first [symex_read_auto | ag_read]
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


Definition stC7c : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x1cfb0; 0x1d028; 0x1d0f8]
      [AV (EAdd (EVar 32) (EShl (EVar 36) 2)) 3008 4 2 (EVar 36);
       AV (EAdd (EVar 33) (EShl (EApp1 2 (EVar 36)) 2)) 2 2 1 (EApp1 2 (EVar 36));
       AV (EAdd (EVar 33) (EShl (EApp1 1 (EApp1 2 (EVar 36))) 2)) 2 2 1 (EApp1 1 (EApp1 2 (EVar 36)));
       AV (EAdd (EVar 33) (EShl (EVar 48) 2)) 0 2 0 (EVar 48);
       AV (EAdd (EVar 32) (EShl (EVar 49) 1)) 2976 2 4 (EVar 49)].

Definition VB7c : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 16); (40%nat, 300); (41%nat, 600); (42%nat, 2 ^ 64); (43%nat, 2 ^ 64);
   (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 600); (49%nat, 16);
   (50%nat, 2 ^ 63); (51%nat, 65536)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC7c VB7c fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).
Local Abbreviation NBC := (2 ^ 64 - 1 - (S + 2976)).
Local Abbreviation xbits := (GenBitlenModel.xbits t).
Local Abbreviation ml_range := (BuildTree6u_6.ml_range t).
Local Abbreviation base_range := (BuildTree6u_6.base_range S t).
Local Abbreviation EXP_span := (BuildTree6u_6.EXP_span t).

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
            | nf; vfix; first [symex_read_auto | ag_read]
            | nf; vfix; symex_store_auto
            | nf; vfix; symex_sok_auto
            | nf; vfix; zc
            | intros; first [apply (BuildTree6u_6.extra_view_bound' S t) | nf; first [apply pb_range | apply hv_range | apply wb_range | apply Z.mod_pos_bound; lia]] ].

Local Abbreviation extra_read := (BuildTree6u_7.extra_read S t).
Local Abbreviation xbits_range := (BuildTree6u_7.xbits_range S t).
Local Abbreviation slen_E := (BuildTree6u_7.slen_E S t).
Local Abbreviation stree_Len_dl := (BuildTree6u_2.stree_Len_dl t).

Section PhaseG.
Variables (FC HP : arr) (DP : arr) (MC K : Z).
Local Abbreviation W4 DL BC OL SL := (U FC DL HP 1 (K - 1) DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.
Hypothesis PQH : forall h, K <= h < 573 -> 0 <= arr_get HP h < tsize t.

Local Abbreviation GS := (BuildTree6u_6.GS S sp t MC).
Local Abbreviation GSA := (BuildTree6u_7.GSA S sp t MC).
Local Abbreviation GI := (BuildTree6u_7.GI F mem0 S p PBL ds sp t FC HP DP MC K).

Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL).

Local Ltac gregs HR Hfr := unfold BuildTree6u_7.GSA, BuildTree6u_6.GS; repeat split; reg1 HR Hfr.

Local Ltac blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf ks pure tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M ks | pure] | tregs ]
  end.

Local Ltac ceqG :=
  nf; vfix;
  repeat match goal with H : _ mod 2 ^ 32 = GenBitlenModel.xbits _ _ |- context [_ mod 2 ^ 32] => rewrite H end;
  repeat match goal with H : GenBitlenModel.xbits _ ?n = 0 |- context [GenBitlenModel.xbits _ ?n] => rewrite H end;
  rewrite <- ?stree_Len_dl; rewrite ?wrap16_sx_addk;
  first [ reflexivity | f_equal; lia | f_equal; ring ].

Local Abbreviation GI_auxB := (BuildTree6u_7b.GI_auxB S).

Lemma gB_s : forall regs m1 m DL BC OL SL h ovf n bits,
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf < 600 -> n = arr_get HP h -> n <= MC -> 1 <= bits <= ML ->
  STP t <> 0 -> GSA regs h ovf n bits ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d028 : word) m s6u_rom)
           (mkst R (if h =? 572 then (0x1d0f8 : word) else (0x1cfb0 : word)) m' s6u_rom)
    /\ GI m1 m' DL (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
          (wrap64 (OL + arr_get FC n * (bits + xbits n)))
          (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits n)) else SL)
    /\ GS R (h + 1) ovf
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL h ovf n bits HG Hh Hovf Hn Hle Hbits Cs HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ci HC.
  destruct HR0 as ((P10 & P11 & P12 & P13 & P14 & P15 & P26 & P19 & P22 & P24 & P27 & P2 & P16 & P17 & P5 & P6 & P7 & P28 & P29 & P30) & P20 & P9 & P31 & P18 & P8).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml. pose proof base_range as Hbase. pose proof EXP_span as (Hexp1 & Hexp2 & Hexp4).
  pose proof (PQH h ltac:(lia)) as Rn. rewrite <- Hn in Rn.
  assert (Vf : pb FC n = arr_get FC n) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
  assert (Vb : pb BC bits = arr_get BC bits) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RFC n ltac:(lia)) as Rf. pose proof (RBC bits ltac:(lia)) as Rb.
  pose proof (xbits_range n) as Rx.
  assert (RODS' : S + 5968 <= 0x11ae0 \/ 0x12510 <= S) by (destruct RODS as [RS _]; lia).
  clear HD Cdyn Csd Cst Cex Cbase Celems Cml RODS RODF HPB' Hsda Hsda8.
  pose proof (GI_auxB BC bits (arr_get BC bits + 1) RBC LBC) as (A3 & A4).
  replace (stree_has t) with true by (symmetry; apply (proj2 (BuildTree6u_2.stree_has_STP t)); exact Cs).
  pose proof (BuildTree6u_2.stree_cells t m HRC Cs) as Cstl. pose proof (BuildTree6u_2.stree_dl_bound S t) as Rstl.
  pose proof (BuildTree6u_2.slen_ge S t Cs) as Hsl. pose proof (BuildTree6u_2.STP_rod S t Cs) as (Hstr1 & Hstr2 & Hstr4). pose proof (slen_E Cs) as HsE.
  assert (Vs : pb stree_dl n = arr_get stree_dl n) by (apply (BuildTree6u_2.stree_pb S t); lia).
  destruct (Z.leb_spec BASE n) as [Cx|Cx].
  + assert (Vx : arr_get (sd_extra_bits t) (n - BASE) mod 2 ^ 32 = xbits n)
      by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_le _ _) Cx); apply Z.mod_small; unfold GenBitlenModel.xbits in Rx; rewrite (proj2 (Z.leb_le _ _) Cx) in Rx; lia).
    destruct (Z.eqb_spec h 572) as [Ce|Ce].
    * run 60%nat [false; false; true; false; false; false; false; false; false; false; false; false; false; true; true]
          [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42); RVal (EApp1 6 (EVar 48)); RVal (EVar 43)] GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; NDP; STP t; NT; NBC; n; bits; EXP t; 0] FC DL HP DP BC.
      all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
      all: dbg_left.
      nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
        ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [exact A3|]; split; [exact A4|]; split; [apply wrap64_range | apply wrap64_range])
        ltac:(split; [gregs HR Hfr | fr_weak Hfr]).
      all: try ceqG.
    * run 60%nat [false; false; true; false; false; false; false; false; false; false; false; false; false; true; false]
          [RVal (EApp1 5 (ESub (EVar 48) (EVar 40))); RVal (EVar 42); RVal (EApp1 6 (EVar 48)); RVal (EVar 43)] GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; NDP; STP t; NT; NBC; n; bits; EXP t; 0] FC DL HP DP BC.
      all: try (nf; rewrite ?(szwrap_small 32) by lia; eapply extra_read; [exact HRC | lia | lia]).
      all: dbg_left.
      nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
        ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [exact A3|]; split; [exact A4|]; split; [apply wrap64_range | apply wrap64_range])
        ltac:(split; [gregs HR Hfr | fr_weak Hfr]).
      all: try ceqG.
  + assert (Vx : xbits n = 0) by (unfold GenBitlenModel.xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity).
    destruct (Z.eqb_spec h 572) as [Ce|Ce].
    * run 60%nat [false; false; false; false; false; false; false; false; true; true]
          [RVal (EVar 42); RVal (EApp1 6 (EVar 48)); RVal (EVar 43)] GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; NDP; STP t; NT; NBC; n; bits; EXP t; 0] FC DL HP DP BC.
      all: dbg_left.
      nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
        ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [exact A3|]; split; [exact A4|]; split; [apply wrap64_range | apply wrap64_range])
        ltac:(split; [gregs HR Hfr | fr_weak Hfr]).
      all: try ceqG.
    * run 60%nat [false; false; false; false; false; false; false; false; true; false]
          [RVal (EVar 42); RVal (EApp1 6 (EVar 48)); RVal (EVar 43)] GSAP
          [S; T; SP; E; h; MC; K - 1; ML; BASE; ovf; OL; SL; NDP; STP t; NT; NBC; n; bits; EXP t; 0] FC DL HP DP BC.
      all: dbg_left.
      nf_in Hms. rewrite ?Vb, ?Vf, ?Vs in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc bits; KOptW; KStatW]
        ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [exact A3|]; split; [exact A4|]; split; [apply wrap64_range | apply wrap64_range])
        ltac:(split; [gregs HR Hfr | fr_weak Hfr]).
      all: try ceqG.
Qed.

Goal True. idtac "gB_s OK". exact I. Qed.

Lemma gB_blk : forall regs m1 m DL BC OL SL h ovf n bits,
  GI m1 m DL BC OL SL -> K <= h <= 572 -> 0 <= ovf < 600 -> n = arr_get HP h -> n <= MC -> 1 <= bits <= ML ->
  GSA regs h ovf n bits ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d028 : word) m s6u_rom)
           (mkst R (if h =? 572 then (0x1d0f8 : word) else (0x1cfb0 : word)) m' s6u_rom)
    /\ GI m1 m' DL (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
          (wrap64 (OL + arr_get FC n * (bits + xbits n)))
          (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits n)) else SL)
    /\ GS R (h + 1) ovf
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL h ovf n bits HG Hh Hovf Hn Hle Hbits HR0.
  destruct (Z.eqb_spec (STP t) 0) as [Cs|Cs].
  - exact (BuildTree6u_7b.gB_n _ _ _ _ _ _ _ _ _ _ HH FC HP DP MC K RFC LFC Hmc HK PQH regs m1 m DL BC OL SL h ovf n bits HG Hh Hovf Hn Hle Hbits Cs HR0).
  - exact (gB_s regs m1 m DL BC OL SL h ovf n bits HG Hh Hovf Hn Hle Hbits Cs HR0).
Qed.

Goal True. idtac "gB_blk OK". exact I. Qed.

End PhaseG.
End Walk.
End FXG.
