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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import BuildTree6u_1 BuildTree6u_2 BuildTree6u_4 BuildTree6u_6 BuildTree6u_7 BuildTree6u_8.
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


Definition stC9 : cfg :=
  CFG FB6 [] [EVar 1%nat] [0x1d1b8; 0x1d1d4; 0x1d1b0; 0x1d23c]
      [AV (EAdd (EVar 32) (EShl (EVar 36) 2)) 3008 4 2 (EVar 36);
       AV (EAdd (EVar 32) (EShl (EVar 39) 1)) 2976 2 4 (EVar 39)].

Local Ltac run fuel dirs rds pins pv FC DL HP DP BC := run_with stC9 VB7 fuel dirs rds pins pv FC DL HP DP BC.

Local Abbreviation ML := (sd_max_length t).
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

Section PhaseH2.
Variables (FC HP : arr) (DP : arr) (MC K : Z) (BC : arr) (SL : Z).
Local Abbreviation W2 DL OL := (U FC DL HP 1 (K - 1) DP BC OL SL MC).
Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LHP : arr_len HP = 573.
Hypothesis Hmc : 0 <= MC < E.
Hypothesis HK : 1 <= K <= 573.

Local Abbreviation GI m1 m DL OL := (BuildTree6u_7.GI F mem0 S p PBL ds sp t FC HP DP MC K m1 m DL BC OL SL).
Local Abbreviation H1C := (BuildTree6u_8.H1C S sp t MC).
Local Abbreviation GCR := (BuildTree6u_8.GCR S sp t).

Definition OB (R : bvmap 5 word) : Prop :=
  getr R 10 = zw T /\ getr R 11 = zw MC /\ getr R 12 = zw 572 /\ getr R 24 = zw (S + 2976) /\ getr R 19 = zw (S + 3008)
  /\ getr R 26 = zw (S + 5912) /\ getr R 22 = zw T /\ getr R 2 = zw SP.
Definition OBP : list (Z * expr) :=
  [(10, EVar 33); (11, EVar 37); (12, ELit 572); (24, EAdd (EVar 32) (ELit 2976)); (19, EAdd (EVar 32) (ELit 3008));
   (26, EAdd (EVar 32) (ELit 5912)); (22, EVar 33); (2, EVar 34)].
Definition O3REGS (R : bvmap 5 word) (bits h : Z) : Prop := OB R /\ getr R 13 = zw bits /\ getr R 14 = zw h.
Definition O3P : list (Z * expr) := OBP ++ [(13, EVar 39); (14, EVar 36)].
Definition I3REGS (R : bvmap 5 word) (bits n h : Z) : Prop := OB R /\ getr R 13 = zw bits /\ getr R 14 = zw h /\ getr R 15 = zw n.
Definition I3P : list (Z * expr) := OBP ++ [(13, EVar 39); (14, EAdd (EVar 36) (ELit 1)); (15, EVar 51)].

Local Ltac oregs HR Hfr := unfold O3REGS, I3REGS, OB, BuildTree6u_8.GCR; repeat split; reg1 HR Hfr.

Local Ltac openGI HG HC RDL LDL RBC LBC ROL RSL :=
  destruct HG as (HC & RDL & LDL & RBC & LBC & ROL & RSL).

Local Ltac blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf ks pure tregs :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [ split; [ci_tower HB HRC HAG MS MP MF HFf M ks | pure] | tregs ]
  end.


Lemma h2_entry : forall regs m,
  H1C regs ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d198 : word) m s6u_rom) (mkst R (0x1d1b8 : word) m s6u_rom)
    /\ O3REGS R ML 573
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m HR0.
  destruct HR0 as (P10 & P11 & P12 & P19 & P24 & P26 & P2 & P16 & P13 & P14 & P15 & P22).
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof ml_range as Hml. pose proof elems_range as He.
  run 20%nat [false; false] NoReads
      [(10, EVar 33); (11, EVar 37); (12, EVar 39); (19, EAdd (EVar 32) (ELit 3008)); (24, EAdd (EVar 32) (ELit 2976));
       (26, EAdd (EVar 32) (ELit 5912)); (2, EVar 34); (13, EVar 39); (22, EVar 33)]
      [S; T; SP; E; 0; MC; K - 1; ML; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC FC HP DP BC.
  all: dbg_left.
  exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "h2_entry OK". exact I. Qed.


Lemma o3_blk : forall regs m1 m DL OL bits h,
  GI m1 m DL OL -> 1 <= bits <= ML -> 0 <= h <= 573 ->
  O3REGS regs bits h ->
  let n := arr_get BC bits in
  exists R,
    msteps s6u_segs (mkst regs (0x1d1b8 : word) m s6u_rom)
           (mkst R (if n =? 0 then (0x1d1b0 : word) else (0x1d1d4 : word)) m s6u_rom)
    /\ (if n =? 0 then O3REGS R bits h else I3REGS R bits n h)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL OL bits h HG Hbits Hh HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as ((P10 & P11 & P12 & P24 & P19 & P26 & P22 & P2) & P13 & P14).
  pose proof ml_range as Hml.
  assert (Vb : pb BC bits = arr_get BC bits) by (apply (pb_get BC); [intros q Hq; apply RBC; rewrite <- LBC; exact Hq | rewrite LBC; lia]).
  pose proof (RBC bits ltac:(lia)) as Rb.
  cbv zeta. destruct (Z.eqb_spec (arr_get BC bits) 0) as [Cz|Cz].
  - run 20%nat [false] NoReads O3P [S; T; SP; E; h; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
  - run 20%nat [true] NoReads O3P [S; T; SP; E; h; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC DL HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "o3_blk OK". exact I. Qed.

Lemma l3_blk : forall regs m bits h,
  1 <= bits <= ML -> 0 <= h <= 573 -> O3REGS regs bits h ->
  exists R,
    msteps s6u_segs (mkst regs (0x1d1b0 : word) m s6u_rom)
           (mkst R (if bits - 1 =? 0 then (0x1d23c : word) else (0x1d1b8 : word)) m s6u_rom)
    /\ (if bits - 1 =? 0 then GCR R else O3REGS R (bits - 1) h)
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m bits h Hbits Hh HR0.
  destruct HR0 as ((P10 & P11 & P12 & P24 & P19 & P26 & P22 & P2) & P13 & P14).
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. pose proof Hsp as Hsp'. pose proof Htt as Htt'.
  pose proof ml_range as Hml. pose proof elems_range as He.
  destruct (Z.eqb_spec (bits - 1) 0) as [Cb|Cb].
  - run 10%nat [true] NoReads O3P [S; T; SP; E; h; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC FC HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
  - run 10%nat [false] NoReads O3P [S; T; SP; E; h; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] FC FC HP DP BC.
    all: dbg_left.
    exists R. split; [exact Hms|]. split; [oregs HR Hfr | fr_weak Hfr].
Qed.

Goal True. idtac "l3_blk OK". exact I. Qed.


Lemma i3_step : forall regs m1 m DL OL bits n h,
  GI m1 m DL OL -> 1 <= bits <= ML -> 1 <= h <= 573 -> 1 <= n < 65536 ->
  0 <= arr_get HP (h - 1) < 573 ->
  I3REGS regs bits n h ->
  let m_ := arr_get HP (h - 1) in
  exists R m',
    msteps s6u_segs (mkst regs (0x1d1d4 : word) m s6u_rom)
           (mkst R (if MC <? m_ then (0x1d1d4 : word) else if n - 1 =? 0 then (0x1d1b0 : word) else (0x1d1d4 : word)) m' s6u_rom)
    /\ GI m1 m' (if MC <? m_ then DL else if arr_get DL m_ =? bits then DL else arr_set DL m_ (wrap16 bits))
                (if MC <? m_ then OL else if arr_get DL m_ =? bits then OL else wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_))
    /\ (if MC <? m_ then I3REGS R bits n (h - 1)
        else if n - 1 =? 0 then O3REGS R bits (h - 1) else I3REGS R bits (n - 1) (h - 1))
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m DL OL bits n h HG Hbits Hh Hn Rm HR0.
  openGI HG HC RDL LDL RBC LBC ROL RSL. open_ciT HC.
  destruct HR0 as ((P10 & P11 & P12 & P24 & P19 & P26 & P22 & P2) & P13 & P14 & P15).
  pose proof Hcf as (_ & HFf & _ & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof ml_range as Hml.
  assert (P14' : getr regs 14 = zw (h - 1 + 1)) by (replace (h - 1 + 1) with h by lia; exact P14).
  assert (Vh : hv HP (h - 1) = arr_get HP (h - 1)) by (apply hv_get; lia).
  cbv zeta. set (m_ := arr_get HP (h - 1)) in *.
  destruct (Z.ltb_spec MC m_) as [Cm|Cm].
  - run 20%nat [false; false; true] NoReads I3P
        [S; T; SP; E; h - 1; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; n] FC DL HP DP BC.
    all: dbg_left.
    exists R, m. split; [exact Hms|].
    split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | repeat (split; [assumption|]); assumption] |].
    split; [oregs HR Hfr | fr_weak Hfr].
  - assert (Rm' : 0 <= m_ < tsize t).
    { pose proof tsize_elems as Hte2. pose proof elems_range as He2. lia. }
    assert (Vd : pb DL m_ = arr_get DL m_) by (apply (pb_get DL); [intros q Hq; apply RDL; rewrite <- LDL; exact Hq | rewrite LDL; lia]).
    assert (Vf : pb FC m_ = arr_get FC m_) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]).
    pose proof (RDL m_ Rm') as Rd. pose proof (RFC m_ Rm') as Rf.
    destruct (Z.eqb_spec (arr_get DL m_) bits) as [Ce|Ce]; destruct (Z.eqb_spec (n - 1) 0) as [Cn|Cn].
    + run 30%nat [false; false; false; false; false; true; true] [RVal (EApp1 1 (EApp1 2 (EVar 36)))] I3P
          [S; T; SP; E; h - 1; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; n] FC DL HP DP BC.
      all: dbg_left.
      exists R, m. split; [exact Hms|].
      split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | repeat (split; [assumption|]); assumption] |].
      split; [oregs HR Hfr | fr_weak Hfr].
    + run 30%nat [false; false; false; false; false; true; false] [RVal (EApp1 1 (EApp1 2 (EVar 36)))] I3P
          [S; T; SP; E; h - 1; MC; K - 1; bits; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; n] FC DL HP DP BC.
      all: dbg_left.
      exists R, m. split; [exact Hms|].
      split; [split; [split; [exact HB | split; [exact HRC | split; [exact HAG | exact MF]]] | repeat (split; [assumption|]); assumption] |].
      split; [oregs HR Hfr | fr_weak Hfr].
    + run 40%nat [false; false; false; false; false; false; true]
          [RVal (EApp1 1 (EApp1 2 (EVar 36))); RVal (EApp1 0 (EApp1 2 (EVar 36))); RVal (EVar 42)] I3P
          [S; T; SP; E; h - 1; MC; K - 1; bits; 0; 0; OL; 0; 0; 0; 0; 0; 0; 0; 0; n] FC DL HP DP BC.
      all: dbg_left.
      nf_in Hms. rewrite ?Vh, ?Vd, ?Vf in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW; KDl m_]
        ltac:(idtac) ltac:(split; [oregs HR Hfr | fr_weak Hfr]).
      all: try (first [reflexivity | f_equal; lia | f_equal; ring]).
      split; [|split; [rewrite arr_len_set; exact LDL | split; [exact RBC | split; [exact LBC | split; [apply wrap64_range | exact RSL]]]]].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range bits); lia | apply RDL; exact Hi].
    + run 40%nat [false; false; false; false; false; false; false]
          [RVal (EApp1 1 (EApp1 2 (EVar 36))); RVal (EApp1 0 (EApp1 2 (EVar 36))); RVal (EVar 42)] I3P
          [S; T; SP; E; h - 1; MC; K - 1; bits; 0; 0; OL; 0; 0; 0; 0; 0; 0; 0; 0; n] FC DL HP DP BC.
      all: dbg_left.
      nf_in Hms. rewrite ?Vh, ?Vd, ?Vf in Hms.
      blk_finG Hms HR Hfr HB HRC HAG MS MP MF HFf [KOptW; KDl m_]
        ltac:(idtac) ltac:(split; [oregs HR Hfr | fr_weak Hfr]).
      all: try (first [reflexivity | f_equal; lia | f_equal; ring]).
      split; [|split; [rewrite arr_len_set; exact LDL | split; [exact RBC | split; [exact LBC | split; [apply wrap64_range | exact RSL]]]]].
      intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range bits); lia | apply RDL; exact Hi].
Qed.

Goal True. idtac "i3_step OK". exact I. Qed.


Lemma gb3i_ok_S : forall f X bits n h,
  gb3i_ok t MC (Datatypes.S f) X bits n h =
  (if negb (n =? 0) then
     1 <= h <= 573 /\ 0 <= heap_get X (h - 1) < 573
     /\ (let '(X', n', h') := GenBitlenModel.GB3i t MC X bits n h in gb3i_ok t MC f X' bits n' h')
   else True).
Proof. reflexivity. Qed.

Lemma i3_loop : forall f regs m1 m DL OL bits n h,
  GI m1 m DL OL -> 1 <= bits <= ML -> 1 <= n < 65536 -> h <= Z.of_nat f ->
  gb3i_ok t MC (Datatypes.S f) (W2 DL OL) bits n h ->
  I3REGS regs bits n h ->
  let '(X', h') := gen_bitlen_loop3i (Datatypes.S f) (W2 DL OL) t MC bits n h in
  exists R m' DL' OL', X' = W2 DL' OL'
    /\ msteps s6u_segs (mkst regs (0x1d1d4 : word) m s6u_rom) (mkst R (0x1d1b0 : word) m' s6u_rom)
    /\ GI m1 m' DL' OL' /\ O3REGS R bits h' /\ 0 <= h' <= 573
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros regs m1 m DL OL bits n h HG Hbits Hn Hf HOK HR0.
  - exfalso. rewrite gb3i_ok_S in HOK. replace (negb (n =? 0)) with true in HOK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). lia.
  - rewrite GenBitlenModel.GL3i_step. rewrite gb3i_ok_S in HOK.
    replace (negb (n =? 0)) with true in * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    destruct HOK as (Hh & Rm & HOK). rewrite bt_heap_get in Rm.
    rewrite (GenBitlenModel.GB3i_flat t MC ds FC DL HP 1 (K - 1) DP BC OL SL bits n h) in HOK |- *. cbv zeta in HOK. cbv zeta.
    destruct (i3_step regs m1 m DL OL bits n h HG Hbits Hh Hn Rm HR0) as (R1 & m2 & Hms1 & HG1 & HR1 & Hfr1).
    destruct (Z.ltb_spec MC (arr_get HP (h - 1))) as [Cm|Cm].
    + specialize (IH R1 m1 m2 DL OL bits n (h - 1) HG1 Hbits Hn ltac:(lia) HOK HR1).
      destruct (gen_bitlen_loop3i (Datatypes.S f) (W2 DL OL) t MC bits n (h - 1)) as [X' h'].
      destruct IH as (R2 & m3 & DL' & OL' & E2 & Hms2 & HG2 & HR2 & Hh2 & Hfr2).
      exists R2, m3, DL', OL'. split; [exact E2|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HG2|]. split; [exact HR2|]. split; [exact Hh2|]. intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + set (DL1 := if arr_get DL (arr_get HP (h - 1)) =? bits then DL else arr_set DL (arr_get HP (h - 1)) (wrap16 bits)) in *.
      set (OL1 := if arr_get DL (arr_get HP (h - 1)) =? bits then OL else wrap64 (OL + (bits - arr_get DL (arr_get HP (h - 1))) * arr_get FC (arr_get HP (h - 1)))) in *.
      assert (EX : (if arr_get DL (arr_get HP (h - 1)) =? bits then (W2 DL OL, n - 1, h - 1)
                    else (W2 (arr_set DL (arr_get HP (h - 1)) (wrap16 bits)) (wrap64 (OL + (bits - arr_get DL (arr_get HP (h - 1))) * arr_get FC (arr_get HP (h - 1)))), n - 1, h - 1))
                   = (W2 DL1 OL1, n - 1, h - 1)) by (subst DL1 OL1; destruct (_ =? bits); reflexivity).
      rewrite EX in HOK |- *.
      destruct (Z.eqb_spec (n - 1) 0) as [Cn|Cn].
      * rewrite Cn in *. rewrite GenBitlenModel.GL3i_done.
        exists R1, m2, DL1, OL1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HG1|]. split; [exact HR1|]. split; [lia | exact Hfr1].
      * specialize (IH R1 m1 m2 DL1 OL1 bits (n - 1) (h - 1) HG1 Hbits ltac:(lia) ltac:(lia) HOK HR1).
        destruct (gen_bitlen_loop3i (Datatypes.S f) (W2 DL1 OL1) t MC bits (n - 1) (h - 1)) as [X' h'].
        destruct IH as (R2 & m3 & DL' & OL' & E2 & Hms2 & HG2 & HR2 & Hh2 & Hfr2).
        exists R2, m3, DL', OL'. split; [exact E2|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HG2|]. split; [exact HR2|]. split; [exact Hh2|]. intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "i3_loop OK". exact I. Qed.

Lemma h2_loop : forall f bits regs m1 m DL OL h,
  Z.of_nat f = bits -> GI m1 m DL OL -> 1 <= bits <= ML -> 0 <= h <= 573 ->
  gb3_ok t MC f (W2 DL OL) bits h ->
  O3REGS regs bits h ->
  exists R m' DL' OL',
    gen_bitlen_loop3 f (W2 DL OL) t MC bits h = W2 DL' OL'
    /\ msteps s6u_segs (mkst regs (0x1d1b8 : word) m s6u_rom) (mkst R (0x1d23c : word) m' s6u_rom)
    /\ GI m1 m' DL' OL' /\ GCR R
    /\ (forall r : reg, reg_in r CLOBI = false -> getr R r = getr regs r).
Proof.
  induction f as [|f IH]; intros bits regs m1 m DL OL h Hf HG Hbits Hh HOK HR0; [lia|].
  rewrite GenBitlenModel.GL3_step. cbn [gb3_ok] in HOK.
  replace (negb (bits =? 0)) with true in * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  rewrite !bt_bl_count_get in HOK |- *.
  destruct HOK as [HOKi HOK].
  pose proof HG as (_ & _ & _ & RBC & LBC & _). pose proof (RBC bits ltac:(pose proof ml_range; lia)) as Rb.
  destruct (o3_blk regs m1 m DL OL bits h HG Hbits Hh HR0) as (R1 & Hms1 & HR1 & Hfr1).
  destruct (Z.eqb_spec (arr_get BC bits) 0) as [Cz|Cz].
  - rewrite Cz in *. rewrite GenBitlenModel.GL3i_done in HOK |- *.
    destruct (l3_blk R1 m bits h Hbits Hh HR1) as (R2 & Hms2 & HR2 & Hfr2).
    destruct (Z.eqb_spec (bits - 1) 0) as [Cb|Cb].
    + replace f with 0%nat by lia. cbn [gen_bitlen_loop3].
      exists R2, m, DL, OL. split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact HG|]. split; [exact HR2|].
      intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (IH (bits - 1) R2 m1 m DL OL h ltac:(lia) HG ltac:(lia) Hh HOK HR2) as (R3 & m3 & DL' & OL' & E3 & Hms3 & HG3 & HC3 & Hfr3).
      exists R3, m3, DL', OL'. split; [exact E3|].
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      split; [exact HG3|]. split; [exact HC3|]. intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
  - pose proof (i3_loop 573 R1 m1 m DL OL bits (arr_get BC bits) h HG Hbits ltac:(lia) ltac:(lia) HOKi HR1) as HI.
    change 574%nat with (Datatypes.S 573) in HOK |- *.
    destruct (gen_bitlen_loop3i (Datatypes.S 573) (W2 DL OL) t MC bits (arr_get BC bits) h) as [X' h'].
    destruct HI as (R2 & m2 & DL1 & OL1 & E2 & Hms2 & HG2 & HR2 & Hh2 & Hfr2). subst X'.
    destruct (l3_blk R2 m2 bits h' Hbits Hh2 HR2) as (R3 & Hms3 & HR3 & Hfr3).
    destruct (Z.eqb_spec (bits - 1) 0) as [Cb|Cb].
    + replace f with 0%nat by lia. cbn [gen_bitlen_loop3].
      exists R3, m2, DL1, OL1. split; [reflexivity|].
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      split; [exact HG2|]. split; [exact HR3|].
      intros r Hr. rewrite (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
    + destruct (IH (bits - 1) R3 m1 m2 DL1 OL1 h' ltac:(lia) HG2 ltac:(lia) Hh2 HOK HR3) as (R4 & m4 & DL' & OL' & E4 & Hms4 & HG4 & HC4 & Hfr4).
      exists R4, m4, DL', OL'. split; [exact E4|].
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | eapply msteps_trans; [exact Hms3 | exact Hms4]]]|].
      split; [exact HG4|]. split; [exact HC4|].
      intros r Hr. rewrite (Hfr4 r Hr), (Hfr3 r Hr), (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Goal True. idtac "h2_loop OK". exact I. Qed.

End PhaseH2.
End Walk.
End FXG.
