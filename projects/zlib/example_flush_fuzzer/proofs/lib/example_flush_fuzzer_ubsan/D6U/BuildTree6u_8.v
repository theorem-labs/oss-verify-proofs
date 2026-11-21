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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_4 BuildTree6u_6 BuildTree6u_7.
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


Definition stC8 : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x1d12c; 0x1d130; 0x1d158; 0x1d17c; 0x1d198; 0x1d23c]
      [AV (EAdd (EVar 32) (EShl (EVar 36) 1)) 2976 2 4 (EVar 36);
       AV (EAdd (EVar 32) (EShl (EVar 39) 1)) 2976 2 4 (EVar 39)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC8 VB7 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
Local Abbreviation BASE := (sd_extra_base t).
Local Abbreviation NBC := (2 ^ 64 - 1 - (S + 2976)).
Local Abbreviation ml_range := (BuildTree6u_6.ml_range t).

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

Local Abbreviation wrap16_sx_addk := BuildTree6u_7.wrap16_sx_addk.

Section PhaseH.
Variables (FC HP : arr) (DP : arr) (MC K : Z).
Local Abbreviation W4 DL BC OL SL := (U FC DL HP 1 (K - 1) DP BC OL SL MC).

Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.

Local Abbreviation GS := (BuildTree6u_6.GS S sp t MC).
Local Abbreviation GI := (BuildTree6u_7.GI F mem0 S p PBL ds sp t FC HP DP MC K).

Definition H1C (R : bvmap 5 word) : Prop :=
  getr R 10 = zw T /\ getr R 11 = zw MC /\ getr R 12 = zw ML /\ getr R 19 = zw (S + 3008)
  /\ getr R 24 = zw (S + 2976) /\ getr R 26 = zw (S + 5912) /\ getr R 2 = zw SP
  /\ getr R 16 = zw NBC /\ getr R 13 = zw ML /\ getr R 14 = zw (S + 2976 + ML * 2) /\ getr R 15 = zw 16
  /\ getr R 22 = zw T.
Definition H1CP : list (Z * expr) :=
  [(10, EVar 33); (11, EVar 37); (12, EVar 39); (19, EAdd (EVar 32) (ELit 3008)); (24, EAdd (EVar 32) (ELit 2976));
   (26, EAdd (EVar 32) (ELit 5912)); (2, EVar 34); (16, EVar 47); (13, EVar 39);
   (14, EAdd (EAdd (EVar 32) (EShl (EVar 39) 1)) (ELit 2976)); (15, ELit 16); (22, EVar 33)].
Definition H1O (R : bvmap 5 word) (ovf : Z) : Prop := H1C R /\ getr R 17 = zw ovf.
Definition H1OP : list (Z * expr) := H1CP ++ [(17, EVar 41)].
Definition H1S (R : bvmap 5 word) (ovf b : Z) : Prop := H1C R /\ getr R 17 = zw ovf /\ getr R 5 = zw (b + 1).
Definition H1SP : list (Z * expr) := H1CP ++ [(17, EVar 41); (5, EAdd (EVar 36) (ELit 1))].
Definition H1F (R : bvmap 5 word) (ovf r v : Z) : Prop :=
  H1C R /\ getr R 17 = zw ovf /\ getr R 5 = zw (r + 1) /\ getr R 6 = zw r /\ getr R 7 = zw (S + r * 2 + 2976) /\ getr R 28 = zw v.
Definition H1FP : list (Z * expr) :=
  H1CP ++ [(17, EVar 41); (5, EAdd (EVar 36) (ELit 1)); (6, EVar 36); (7, EAdd (EAdd (EVar 32) (EShl (EVar 36) 1)) (ELit 2976)); (28, EApp1 4 (EVar 36))].
Definition GCR (R : bvmap 5 word) : Prop := getr R 24 = zw (S + 2976) /\ getr R 22 = zw T /\ getr R 2 = zw SP.

Local Ltac hregs HR Hfr := unfold H1O, H1S, H1F, H1C, GCR; repeat split; reg1 HR Hfr.

Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL).

Local Ltac blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf ks pure tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M ks | pure] | tregs ]
  end.

Lemma blc_set_range : forall BC i w,
  (forall q, 0 <= q < 16 -> 0 <= arr_get BC q < 65536) ->
  forall q, 0 <= q < 16 -> 0 <= arr_get (arr_set BC i (wrap16 w)) q < 65536.
Proof.
  intros BC i w RBC q Hq. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range w); lia | apply RBC; exact Hq].
Qed.


Lemma h1_setup : forall regs m1 m DL BC OL SL ovf,
  GI m1 m DL BC OL SL -> 0 <= ovf < 600 ->
  GS regs 573 ovf ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d0f8 : word) m s6u_rom)
           (mkst R (if ovf =? 0 then (0x1d23c : word) else (0x1d12c : word)) m s6u_rom)
    /\ (if ovf =? 0 then GCR R else H1O R ovf)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL ovf HG Hovf HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as (P10 & P11 & P12 & P13 & P14 & P15 & P26 & P19 & P22 & P24 & P27 & P2 & P16 & P17 & P5 & P6 & P7 & P28 & P29 & P30).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml.
  destruct (Z.eqb_spec ovf 0) as [Co|Co].
  - subst ovf.
    run 20%nat [true] NoReads
        [(10, EVar 33); (11, EVar 37); (12, EVar 39); (19, EAdd (EVar 32) (ELit 3008)); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976));
         (26, EAdd (EVar 32) (ELit 5912)); (2, EVar 34); (16, EVar 47); (17, ELit 0)]
        [S; T; SP; E; 0; MC; K - 1; ML; 0; 0; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [hregs HR Hfr | fr_weak Hfr].
  - run 30%nat [false; false; false; false; false] NoReads
        [(10, EVar 33); (11, EVar 37); (12, EVar 39); (19, EAdd (EVar 32) (ELit 3008)); (22, EVar 33); (24, EAdd (EVar 32) (ELit 2976));
         (26, EAdd (EVar 32) (ELit 5912)); (2, EVar 34); (16, EVar 47); (17, EVar 41)]
        [S; T; SP; E; 0; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [hregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h1_setup OK". exact I. Qed.

Lemma h1_head : forall regs m ovf,
  H1O regs ovf -> 0 < ovf < 600 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d12c : word) m s6u_rom) (mkst R (0x1d130 : word) m s6u_rom)
    /\ H1S R ovf (ML - 1)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m ovf ((P10 & P11 & P12 & P19 & P24 & P26 & P2 & P16 & P13 & P14 & P15 & P22) & P17) Hovf.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof ml_range as Hml. pose proof elems_range as He.
  run 10%nat NoDirs NoReads H1OP
      [S; T; SP; E; 0; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC FC HP DP FC.
  all: dbg_left.
  exists R. split; [exact Hms|]. split; [hregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h1_head OK". exact I. Qed.


Lemma h1_scan_step : forall regs m1 m DL BC OL SL ovf b,
  GI m1 m DL BC OL SL -> 0 <= b <= ML - 1 -> 0 <= ovf < 600 ->
  (arr_get BC b = 0 -> 1 <= b) ->
  H1S regs ovf b ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d130 : word) m s6u_rom)
           (mkst R (if arr_get BC b =? 0 then (0x1d130 : word) else (0x1d158 : word)) m s6u_rom)
    /\ (if arr_get BC b =? 0 then H1S R ovf (b - 1) else H1F R ovf b (arr_get BC b))
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL ovf b HG Hb Hovf Hb1 HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as ((P10 & P11 & P12 & P19 & P24 & P26 & P2 & P16 & P13 & P14 & P15 & P22) & P17 & P5).
  pose proof ml_range as Hml.
  assert (Vb : pb BC b = arr_get BC b) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RBC b ltac:(lia)) as Rb.
  destruct (Z.eqb_spec (arr_get BC b) 0) as [Cz|Cz].
  - specialize (Hb1 Cz).
    run 20%nat [false; false; true] NoReads H1SP
        [S; T; SP; E; b; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [hregs HR Hfr | fr_weak Hfr].
  - run 20%nat [false; true] NoReads H1SP
        [S; T; SP; E; b; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [hregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h1_scan_step OK". exact I. Qed.

Lemma h1_scan : forall f b regs m1 m DL BC OL SL ovf,
  Z.of_nat f = b + 1 -> GI m1 m DL BC OL SL -> 0 <= b <= ML - 1 -> 0 <= ovf < 600 ->
  0 <= gen_bitlen_find f (W4 DL BC OL SL) b ->
  H1S regs ovf b ->
  let r := gen_bitlen_find f (W4 DL BC OL SL) b in
  exists R,
    msteps s6u_segs (mkst regs (0x1d130 : word) m s6u_rom) (mkst R (0x1d158 : word) m s6u_rom)
    /\ H1F R ovf r (arr_get BC r) /\ 0 <= r <= b
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros b regs m1 m DL BC OL SL ovf Hf HG Hb Hovf Hr HR0; [lia|].
  cbn [gen_bitlen_find] in Hr |- *. rewrite bt_bl_count_get in Hr |- *.
  assert (Hb1 : arr_get BC b = 0 -> 1 <= b).
  { intros Cz. rewrite Cz in Hr. cbn in Hr. pose proof (GenBitlenModel.find_spec f _ (b - 1) Hr) as (A & _). cbv zeta in A. lia. }
  destruct (h1_scan_step regs m1 m DL BC OL SL ovf b HG Hb Hovf Hb1 HR0) as (R1 & Hms1 & HR1 & Hfr1).
  destruct (Z.eqb_spec (arr_get BC b) 0) as [Cz|Cz].
  - destruct (IH (b - 1) R1 m1 m DL BC OL SL ovf ltac:(lia) HG ltac:(lia) Hovf Hr HR1) as (R2 & Hms2 & HR2 & Hr2 & Hfr2).
    exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HR2|]. split; [lia|].
    intros r Hq. rewrite (Hfr2 r Hq). exact (Hfr1 r Hq).
  - exists R1. split; [exact Hms1|]. split; [exact HR1|]. split; [lia | exact Hfr1].
Qed.

Goal True. idtac "h1_scan OK". exact I. Qed.


Lemma h1_fix1 : forall regs m1 m DL BC OL SL ovf r,
  GI m1 m DL BC OL SL -> 0 <= r <= ML - 1 -> 0 <= ovf < 600 ->
  H1F regs ovf r (arr_get BC r) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d158 : word) m s6u_rom) (mkst R (0x1d17c : word) m' s6u_rom)
    /\ GI m1 m' DL (arr_set (arr_set BC r (wrap16 (arr_get BC r - 1))) (r + 1) (wrap16 (arr_get BC (r + 1) + 2))) OL SL
    /\ H1O R ovf
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL ovf r HG Hr Hovf HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as ((P10 & P11 & P12 & P19 & P24 & P26 & P2 & P16 & P13 & P14 & P15 & P22) & P17 & P5 & P6 & P7 & P28).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml.
  assert (Vr : pb BC r = arr_get BC r) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  assert (Vr1 : pb BC (r + 1) = arr_get BC (r + 1)) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RBC r ltac:(lia)) as Rb. pose proof (RBC (r + 1) ltac:(lia)) as Rb1.
  assert (P28' : getr regs 28 = zw (pb BC r)) by (rewrite Vr; exact P28).
  run 30%nat [false; false] NoReads H1FP
      [S; T; SP; E; r; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
  all: dbg_left.
  nf_in Hms. rewrite ?Vr, ?Vr1 in Hms.
  blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc r; KBlc (r + 1)]
    ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [apply blc_set_range; apply blc_set_range; exact RBC|];
          split; [rewrite !arr_len_set; exact LBC|]; split; [exact ROL | exact RSL])
    ltac:(split; [hregs HR Hfr | fr_weak Hfr]).
  all: try (rewrite ?wrap16_sx_addk; first [reflexivity | f_equal; f_equal; lia]).
Qed.

Goal True. idtac "h1_fix1 OK". exact I. Qed.

Lemma h1_fix2 : forall regs m1 m DL BC OL SL ovf,
  GI m1 m DL BC OL SL -> 0 < ovf < 600 ->
  H1O regs ovf ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1d17c : word) m s6u_rom)
           (mkst R (if 2 <? ovf then (0x1d12c : word) else (0x1d198 : word)) m' s6u_rom)
    /\ GI m1 m' DL (arr_set BC ML (wrap16 (arr_get BC ML - 1))) OL SL
    /\ (if 2 <? ovf then H1O R (ovf - 2) else H1C R)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL ovf HG Hovf HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as ((P10 & P11 & P12 & P19 & P24 & P26 & P2 & P16 & P13 & P14 & P15 & P22) & P17).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml.
  assert (Vm : pb BC ML = arr_get BC ML) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RBC ML ltac:(lia)) as Rm.
  destruct (Z.ltb_spec 2 ovf) as [Co|Co].
  - run 20%nat [false; true] NoReads H1OP
        [S; T; SP; E; 0; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    nf_in Hms. rewrite ?Vm in Hms.
    blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc ML]
      ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [apply blc_set_range; exact RBC|];
            split; [rewrite !arr_len_set; exact LBC|]; split; [exact ROL | exact RSL])
      ltac:(split; [hregs HR Hfr | fr_weak Hfr]).
    all: try (rewrite ?wrap16_sx_addk; first [reflexivity | f_equal; f_equal; lia]).
  - run 20%nat [false; false] NoReads H1OP
        [S; T; SP; E; 0; MC; K - 1; ML; 0; ovf; 0; 0; 0; 0; 0; NBC; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    nf_in Hms. rewrite ?Vm in Hms.
    blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KBlc ML]
      ltac:(split; [exact RDL|]; split; [exact LDL|]; split; [apply blc_set_range; exact RBC|];
            split; [rewrite !arr_len_set; exact LBC|]; split; [exact ROL | exact RSL])
      ltac:(split; [hregs HR Hfr | fr_weak Hfr]).
    all: try (rewrite ?wrap16_sx_addk; first [reflexivity | f_equal; f_equal; lia]).
Qed.

Goal True. idtac "h1_fix2 OK". exact I. Qed.


Lemma h1_trip : forall regs m1 m DL BC OL SL ovf,
  GI m1 m DL BC OL SL -> 0 < ovf < 600 ->
  0 <= gen_bitlen_find (Z.to_nat ML) (W4 DL BC OL SL) (ML - 1) ->
  H1O regs ovf ->
  let r := gen_bitlen_find (Z.to_nat ML) (W4 DL BC OL SL) (ML - 1) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1d12c : word) m s6u_rom)
           (mkst R (if 2 <? ovf then (0x1d12c : word) else (0x1d198 : word)) m' s6u_rom)
    /\ GI m1 m' DL (GenBitlenModel.bl_adj ML BC r) OL SL
    /\ (if 2 <? ovf then H1O R (ovf - 2) else H1C R)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL BC OL SL ovf HG Hovf Hr HR0.
  pose proof ml_range as Hml.
  pose proof HG as (_ & _ & _ & RBC & LBC & _).
  destruct (h1_head regs m ovf HR0 Hovf) as (R1 & Hms1 & HR1 & Hfr1).
  destruct (h1_scan (Z.to_nat ML) (ML - 1) R1 m1 m DL BC OL SL ovf ltac:(lia) HG ltac:(lia) ltac:(lia) Hr HR1)
    as (R2 & Hms2 & HR2 & Hr2 & Hfr2).
  cbv zeta. set (r := gen_bitlen_find (Z.to_nat ML) (W4 DL BC OL SL) (ML - 1)) in *.
  destruct (h1_fix1 R2 m1 m DL BC OL SL ovf r HG ltac:(lia) ltac:(lia) HR2) as (R3 & m3 & Hms3 & HG3 & HR3 & Hfr3).
  destruct (h1_fix2 R3 m1 m3 DL _ OL SL ovf HG3 Hovf HR3) as (R4 & m4 & Hms4 & HG4 & HR4 & Hfr4).
  exists R4, m4. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
  split.
  { unfold GenBitlenModel.bl_adj.
    rewrite (arr_get_set BC r (r + 1)). replace ((r =? r + 1) && arr_inb BC r) with false by (symmetry; rewrite Bool.andb_false_iff; left; apply Z.eqb_neq; lia).
    exact HG4. }
  split; [exact HR4|].
  intros q Hq. rewrite (Hfr4 q Hq), (Hfr3 q Hq), (Hfr2 q Hq). exact (Hfr1 q Hq).
Qed.

Goal True. idtac "h1_trip OK". exact I. Qed.

Lemma h1_loop : forall f regs m1 m DL BC OL SL ovf,
  ovf <= 2 * Z.of_nat f ->
  GI m1 m DL BC OL SL -> 0 < ovf < 600 ->
  GenBitlenModel.gb2_ok ML f (W4 DL BC OL SL) ovf ->
  H1O regs ovf ->
  exists R m' BC',
    gen_bitlen_loop2 f (W4 DL BC OL SL) ML ovf = W4 DL BC' OL SL
    /\ msteps s6u_segs (mkst regs (0x1d12c : word) m s6u_rom) (mkst R (0x1d198 : word) m' s6u_rom)
    /\ GI m1 m' DL BC' OL SL /\ H1C R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros regs m1 m DL BC OL SL ovf Hf HG Hovf HOK HR0; [lia|].
  pose proof (GenBitlenModel.gb2_ok_step t ML f ds FC DL HP 1 (K - 1) DP BC OL SL MC ovf HOK) as [Hr Hrest].
  rewrite (GenBitlenModel.GL2_step t ML f ds FC DL HP 1 (K - 1) DP BC OL SL MC ovf). cbv zeta.
  destruct (h1_trip regs m1 m DL BC OL SL ovf HG Hovf Hr HR0) as (R1 & m2 & Hms1 & HG1 & HR1 & Hfr1).
  destruct (Z.ltb_spec 2 ovf) as [C|C].
  - replace (0 <? ovf - 2) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH R1 m1 m2 DL _ OL SL (ovf - 2) ltac:(lia) HG1 ltac:(lia) (Hrest ltac:(lia)) HR1)
      as (R2 & m3 & BC' & E2 & Hms2 & HG2 & HB2 & Hfr2).
    exists R2, m3, BC'. split; [exact E2|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HG2|]. split; [exact HB2|]. intros r Hr'. rewrite (Hfr2 r Hr'). exact (Hfr1 r Hr').
  - replace (0 <? ovf - 2) with false by (symmetry; apply Z.ltb_ge; lia).
    eexists R1, m2, _. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HG1|]. split; [exact HR1 | exact Hfr1].
Qed.

Goal True. idtac "h1_loop OK". exact I. Qed.

End PhaseH.
End Walk.
End FXG.
