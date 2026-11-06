(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsS B0_cmp_msV B0_cmp_bsV B0_cmp_fsQ B0_cmp_fsV B0_cmp_fsP B0_cmp_msW B0_cmp_msS CmpSmKit CmpHmKit.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpHmKit.rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).
Ltac split_at_cb4 cs :=
  lazymatch cs with
  | CB 4 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb4 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb4_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb4 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpSmKit.rw_cells_CB4_C4 segs m A pre bs post) in H; cbn [app] in H end end).

(* [comment removed for export] *)
Ltac cutk R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (repeat match goal with |- context [Z.of_nat ?kk] => let z := eval vm_compute in (Z.of_nat kk) in change (Z.of_nat kk) with z end; lia) end
  end.
(* [comment removed for export] *)
Ltac glue2 H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 => lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    assert (H : rw_cells segs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app_iff_c segs m A cs1 cs2)); split; [exact H1| cbn [cells_size csize Nat.add];
          lazymatch goal with |- rw_cells _ _ ?B _ => replace B with A2
            by (repeat match goal with |- context [Z.of_nat ?kk] => let z := eval vm_compute in (Z.of_nat kk) in change (Z.of_nat kk) with z end; lia) end; exact H2]) end end;
  cbn [app] in H; clear H1 H2.

(* [comment removed for export] *)
Fixpoint c8s_of (k : nat) (j : list byte) : list cell :=
  match k with O => [] | S k' => C8 (le_bytes_to_word (firstn 8 j)) :: c8s_of k' (skipn 8 j) end.
(* [comment removed for export] *)
Fixpoint c4s_of (k : nat) (j : list byte) : list cell :=
  match k with O => [] | S k' => C4 (le_bytes_to_word (firstn 4 j)) :: c4s_of k' (skipn 4 j) end.

Lemma rw_cells_junk_C8s : forall segs k m A (j : list byte),
  rw_cells segs m A [CB (8 * k) j] -> rw_cells segs m A (c8s_of k j).
Proof.
  intros segs k. induction k as [|k IH]; intros m A j H.
  - cbn. destruct H as [[Hwf Hb] Hw]. cbn in *. split; [split|]; cbn; try tauto.
    + destruct Hwf as [L _]. destruct j; [|cbn in L; lia]. cbn in Hb. exact Hb.
  - pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
    assert (H2 : rw_cells segs m A ([CB 8 (firstn 8 j)] ++ [CB (8 * k) (skipn 8 j)])).
    { destruct H as [[Hwf Hb] Hw]. split; [split|].
      - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
      - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite firstn_skipn. exact Hb.
      - cbn [cells_size csize app] in *. eapply eq_ind; [exact Hw|]. f_equal. lia. }
    apply (proj1 (rw_cells_app_iff_c segs m A _ _)) in H2. destruct H2 as [H8 Hr].
    cbn [cells_size csize Nat.add] in Hr.
    cbn [c8s_of]. change (C8 (le_bytes_to_word (firstn 8 j)) :: c8s_of k (skipn 8 j)) with ([C8 (le_bytes_to_word (firstn 8 j))] ++ c8s_of k (skipn 8 j)).
    apply (proj2 (rw_cells_app_iff_c segs m A _ _)). split.
    + destruct H8 as [[Hwf Hb] Hw]. split; [split|].
      * cbn. tauto.
      * cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite le8_of_bytes by (rewrite length_firstn; lia). exact Hb.
      * cbn [cells_size csize Nat.add] in *. exact Hw.
    + cbn [cells_size csize Nat.add]. apply IH. exact Hr.
Qed.
Lemma rw_cells_junk_C4s : forall segs k m A (j : list byte),
  rw_cells segs m A [CB (4 * k) j] -> rw_cells segs m A (c4s_of k j).
Proof.
  intros segs k. induction k as [|k IH]; intros m A j H.
  - cbn. destruct H as [[Hwf Hb] Hw]. cbn in *. split; [split|]; cbn; try tauto.
    + destruct Hwf as [L _]. destruct j; [|cbn in L; lia]. cbn in Hb. exact Hb.
  - pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
    assert (H2 : rw_cells segs m A ([CB 4 (firstn 4 j)] ++ [CB (4 * k) (skipn 4 j)])).
    { destruct H as [[Hwf Hb] Hw]. split; [split|].
      - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
      - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite firstn_skipn. exact Hb.
      - cbn [cells_size csize app] in *. eapply eq_ind; [exact Hw|]. f_equal. lia. }
    apply (proj1 (rw_cells_app_iff_c segs m A _ _)) in H2. destruct H2 as [H4 Hr].
    cbn [cells_size csize Nat.add] in Hr.
    cbn [c4s_of]. change (C4 (le_bytes_to_word (firstn 4 j)) :: c4s_of k (skipn 4 j)) with ([C4 (le_bytes_to_word (firstn 4 j))] ++ c4s_of k (skipn 4 j)).
    apply (proj2 (rw_cells_app_iff_c segs m A _ _)). split.
    + destruct H4 as [[Hwf Hb] Hw]. split; [split|].
      * cbn. tauto.
      * cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite le4_le_bytes_to_word by (rewrite length_firstn; lia). exact Hb.
      * cbn [cells_size csize Nat.add] in *. exact Hw.
    + cbn [cells_size csize Nat.add]. apply IH. exact Hr.
Qed.


Section B0BSP1.
  Variable X : msenv. Variable P : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X.
  Hypothesis YPl : (me_lo X <= P)%Z. Hypothesis YPh : (P + 640 <= bv_unsigned (me_sp X))%Z. Hypothesis YPa : (bv_unsigned (me_sp X) <= P + 656)%Z.
  Notation usp := (bv_unsigned (me_sp X)). Notation E := (me_E X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X). Notation lo := (me_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).

  Lemma B0_bs_P1 : forall (qP : Z) (m : word -> option byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk b0segs m lo usp -> mem_inv b0segs m -> aconsts B0C m -> aconsts_uar B0C m ->
    (forall m' (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 : word) (wbud k0 k1 k2 k3 k4 k5 k6 k7 k8 : word) (y11 y12 : word),
      rw_cells b0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 w400; C8 w408; C8 w416; C8 w424; C8 w432; C8 w440; C8 w448; C8 w456; C8 w464; C8 w472; C8 w480; C8 w488] ->
      rw_cells b0segs m' (P + 496) [C4 wbud] -> rw_cells b0segs m' (P + 500) [C4 k0; C4 k1; C4 k2; C4 k3; C4 k4; C4 k5; C4 k6; C4 k7; C4 k8] ->
      stk b0segs m' (P + 536) (usp + -104) -> rw_cells b0segs m' (usp + -104) (MSAVED X) ->
      stk b0segs m' lo P -> mem_inv b0segs m' -> munch [(P, usp)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 0xa09fc) (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 5216) y11 y12 a3 a4 a5 a6 a7
                            (me_s2 X) (me_s3 X) (me_s4 X) (me_s5 X) (me_s6 X) (Z_to_bv 64 E) (me_s8 X) (me_s9 X) (me_s10 X) cSB t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e334) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (me_ra X) (me_sp X) gp tp t0 t1 t2 (me_s0 X) (me_s1 X) (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7
                          (me_s2 X) (me_s3 X) (me_s4 X) (me_s5 X) (me_s6 X) (me_s7 X) (me_s8 X) (me_s9 X) (me_s10 X) (me_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0988) fc None m (seg_rom b0segs)).
  Proof.
    intros qP m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    msenv_open1 XOK.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar B0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    assert (CASE : (P = usp - 640 \/ P = usp - 656)%Z) by lia.
    assert (ELAND : Z.land (usp + -640) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - CASE EqP ALS. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 640%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 640 _ [] (8 :: 488 :: 4 :: 36 :: repeat 8 13)%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app repeat] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -640)%Z with P in FR, ST by lia.
      (* [comment removed for export] *)
      brun_to 0x3e334%Z.
      cutk FR 1%nat C0 (P + 8)%Z. cutk FR 1%nat CBIG (P + 496)%Z. cutk FR 1%nat BUDc (P + 500)%Z. cutk FR 1%nat NXc (usp + -104)%Z.
      apply (rw_cells_junk_C8s b0segs 61) in CBIG. cbn [c8s_of] in CBIG.
      apply (rw_cells_junk_C4s b0segs 9) in NXc. cbn [c4s_of] in NXc. cb4_all BUDc.
      glue2 C0 CBIG SLc.
      eapply K; [exact SLc| exact BUDc| exact NXc| | exact FR| exact ST| assumption| exact MU| exact WM].
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 656%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 656 _ [] (8 :: 8 :: 8 :: 472 :: 4 :: 36 :: 16 :: repeat 8 13)%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app repeat] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -656)%Z with P in FR, ST by lia.
      brun_to 0x3e334%Z.
      cutk FR 3%nat C0 (P + 24)%Z. cutk FR 1%nat CBIG (P + 496)%Z. cutk FR 1%nat BUDc (P + 500)%Z. cutk FR 1%nat NXc (P + 536)%Z. cutk FR 1%nat GAPc (usp + -104)%Z.
      cb8_all C0.
      apply (rw_cells_junk_C8s b0segs 59) in CBIG. cbn [c8s_of] in CBIG.
      apply (rw_cells_junk_C4s b0segs 9) in NXc. cbn [c4s_of] in NXc. cb4_all BUDc.
      glue2 C0 CBIG SLc.
      pose proof (stk_of_rw_cells b0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 536 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      eapply K; [exact SLc| exact BUDc| exact NXc| exact GAPs| exact FR| exact ST| assumption| exact MU| exact WM].
  Qed.
End B0BSP1.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WP2 := [(FB, FB + 24); (SHF, SHF + 178); (P, P + 496)]%Z.

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.
  Ltac sbf2 := wstep; change (le1 (Z_to_bv 64 (-14))) with [f2b]; mem_after_store.
  Ltac sbf1 := wstep; change (le1 (Z_to_bv 64 (-15))) with [f1b]; mem_after_store.
  Ltac sbx := first [sbf8 | sbf2 | sbf1].
  Ltac sb0 := wstep; change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store.

  Lemma B0_bs_P2sb_0 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m SHF [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17; C1 c18; C1 c19; C1 c20; C1 c21; C1 c22; C1 c23; C1 c24; C1 c25; C1 c26; C1 c27; C1 c28; C1 c29; C1 c30; C1 c31] -> mem_inv b0segs m -> munch [(SHF, SHF + 32)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' SHF [C1 f1b; C1 f1b; C1 f1b; C1 f1b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b] -> mem_inv b0segs m' -> munch [(SHF, SHF + 32)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0af0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0a70) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 32 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  Lemma B0_bs_P2sb_1 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 32) [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17; C1 c18; C1 c19; C1 c20; C1 c21; C1 c22; C1 c23; C1 c24; C1 c25; C1 c26; C1 c27; C1 c28; C1 c29; C1 c30; C1 c31] -> mem_inv b0segs m -> munch [(SHF + 32, SHF + 64)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 32) [C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f8b; C1 f8b] -> mem_inv b0segs m' -> munch [(SHF + 32, SHF + 64)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0b70) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0af0) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 32 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  Lemma B0_bs_P2sb_2 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 64) [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17; C1 c18; C1 c19; C1 c20; C1 c21; C1 c22; C1 c23; C1 c24; C1 c25; C1 c26; C1 c27; C1 c28; C1 c29; C1 c30; C1 c31] -> mem_inv b0segs m -> munch [(SHF + 64, SHF + 96)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 64) [C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b] -> mem_inv b0segs m' -> munch [(SHF + 64, SHF + 96)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0bf0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0b70) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 32 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  Lemma B0_bs_P2sb_3 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 96) [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17; C1 c18; C1 c19; C1 c20; C1 c21; C1 c22; C1 c23; C1 c24; C1 c25; C1 c26; C1 c27; C1 c28; C1 c29; C1 c30; C1 c31] -> mem_inv b0segs m -> munch [(SHF + 96, SHF + 128)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 96) [C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b] -> mem_inv b0segs m' -> munch [(SHF + 96, SHF + 128)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0c70) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0bf0) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 32 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  Lemma B0_bs_P2sb_4 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 128) [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17; C1 c18; C1 c19; C1 c20; C1 c21; C1 c22; C1 c23; C1 c24; C1 c25; C1 c26; C1 c27; C1 c28; C1 c29; C1 c30; C1 c31] -> mem_inv b0segs m -> munch [(SHF + 128, SHF + 160)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 128) [C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b] -> mem_inv b0segs m' -> munch [(SHF + 128, SHF + 160)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0cf0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0c70) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 32 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  Lemma B0_bs_P2sb_5 : forall (me m : word -> option byte) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 160) [C1 c0; C1 c1; C1 c2; C1 c3; C1 c4; C1 c5; C1 c6; C1 c7; C1 c8; C1 c9; C1 c10; C1 c11; C1 c12; C1 c13; C1 c14; C1 c15; C1 c16; C1 c17] -> mem_inv b0segs m -> munch [(SHF + 160, SHF + 178)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 160) [C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f8b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b; C1 f2b] -> mem_inv b0segs m' -> munch [(SHF + 160, SHF + 178)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0d38) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0cf0) fc None m (seg_rom b0segs)).
  Proof.
    intros me m c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    do 18 sbx.
    apply K; [exact RZ| exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_P2sb : forall (me m : word -> option byte) (bs : list byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m SHF [CB 178 bs] -> mem_inv b0segs m -> munch [(SHF, SHF + 178)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 4) (shc3 f8b) -> mem_inv b0segs m' -> munch [(SHF, SHF + 178)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0d38) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa0a70) fc None m (seg_rom b0segs)).
  Proof.
    intros me m bs ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    destruct (rw_cells_CB_C1s b0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 178 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    cutk RZ 32%nat R0 (SHF + 32)%Z. cutk RZ 32%nat R1 (SHF + 64)%Z. cutk RZ 32%nat R2 (SHF + 96)%Z. cutk RZ 32%nat R3 (SHF + 128)%Z. cutk RZ 32%nat R4 (SHF + 160)%Z.
    rename RZ into R5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_0 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R0| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB0 R0n MIn MUn WMn. clear R0 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB0 MUn WMn end. clear MUn WMn. rename MIn into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_1 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R1| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB1 R1n MIn MUn WMn. clear R1 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB1 MUn WMn end. clear MUn WMn. rename MIn into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_2 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R2| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB2 R2n MIn MUn WMn. clear R2 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB2 MUn WMn end. clear MUn WMn. rename MIn into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_3 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R3| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB3 R3n MIn MUn WMn. clear R3 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB3 MUn WMn end. clear MUn WMn. rename MIn into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_4 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R4| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB4 R4n MIn MUn WMn. clear R4 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB4 MUn WMn end. clear MUn WMn. rename MIn into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_bs_P2sb_5 mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| exact R5| exact MI| apply munch_refl| apply wmono_refl|].
    intros mB5 R5n MIn MUn WMn. clear R5 MI. lazymatch type of MUn with munch _ ?ma _ => transport_after_call b0segs ma mB5 MUn WMn end. clear MUn WMn. rename MIn into MI.
    glue2 R0n R1n G1. glue2 G1 R2n G2. glue2 G2 R3n G3. glue2 G3 R4n G4. glue2 G4 R5n RZ.
    destruct (rw_cells_cutZ b0segs _ _ _ 4 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 4) with 4%Z in RZ1.
    destruct (rw_cells_cutZ b0segs _ _ _ 166 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    apply K; [exact RZ2| exact MI| exact MU| exact WMo].
  Qed.


  (* [comment removed for export] *)
  Lemma B0_bs_P2 : forall (me m : word -> option byte) (bs : list byte) (h0 h1 h2 : word) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
    rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells b0segs m SHF [CB 178 bs] -> rw_cells b0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 w400; C8 w408; C8 w416; C8 w424; C8 w432; C8 w440; C8 w448; C8 w456; C8 w464; C8 w472; C8 w480; C8 w488] ->
    mem_inv b0segs m -> munch WP2 me m -> wmono b0segs me m ->
    (forall m' (y12 y13 y14 : word),
       rw_cells b0segs m' FB [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 81238); C8 (Z_to_bv 64 657800)] ->
       rw_cells b0segs m' (SHF + 4) (shc3 f8b) -> rw_cells b0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 w400; C8 w408; C8 w416; C8 w424; C8 w432; C8 w440; C8 w448; C8 w456; C8 w464; C8 w472; C8 w480; C8 (Z_to_bv 64 FB)] ->
       mem_inv b0segs m' -> munch WP2 me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa0d48) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 128) y12 y13 y14 x15 x16 x17
                             (Z_to_bv 64 (-8)) (Z_to_bv 64 FB) (Z_to_bv 64 (-14)) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) x23 (Z_to_bv 64 (SHF + 178)) x25 x26 cSB x28 x29 x30 x31)
                        F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 FB) x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa09fc) fc None m (seg_rom b0segs)).
  Proof.
    intros me m bs h0 h1 h2 w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 HD RZ SL MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX. destruct YSF as (AX & YSl & YSh). unfold SH_LO, SH_HI in YSl, YSh.
    assert (AFS : (FB + 5216 <= SHF \/ SHF + 652 <= FB)%Z) by (destruct YOFF as (_ & _ & _ & O4); unfold SH_LO, SH_HI in O4; lia). box_ors.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    wstep; if_cases Ks; zify_cond_z Ks; [| exfalso; lia].
    wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. lit_store. wstep. lit_store. wstep. lit_store. wstep. wstep.
    rewrite (sanchor_addr0 FB SHF AX).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    enter_with (B0_bs_P2sb m1 m1 bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact RZ| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 RZ2 MI2 MU2 WM2. clear RZ MI. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    eapply K; [exact HD| exact RZ2| exact SL| exact MI2| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_P3 : forall (me m : word -> option byte) (bs : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells b0segs m (SHF + 306) [CB 56 bs] -> mem_inv b0segs m ->
    munch [(SHF + 306, SHF + 362)]%Z me m -> wmono b0segs me m ->
    (forall m', rw_cells b0segs m' (SHF + 322) (shcB f8b) -> mem_inv b0segs m' ->
       munch [(SHF + 306, SHF + 362)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa0e38) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (-8)) x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 (Z_to_bv 64 (SHF + 362)) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (-8)) x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa0d48) fc None m (seg_rom b0segs)).
  Proof.
    intros me m bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 RZ MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX.
    destruct (rw_cells_CB_C1s b0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 56 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    do 56 sbx.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    destruct (rw_cells_cutZ b0segs _ _ _ 16 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 16) with 16%Z in RZ1.
    replace (SHF + 306 + 16)%Z with (SHF + 322)%Z in RZ1 by lia.
    destruct (rw_cells_cutZ b0segs _ _ _ 32 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    apply K; [exact RZ2| exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_P4 : forall (me m : word -> option byte) (bs : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells b0segs m (SHF + 490) [CB 16 bs] -> mem_inv b0segs m ->
    munch [(SHF + 490, SHF + 506)]%Z me m -> wmono b0segs me m ->
    (forall m', mem_inv b0segs m' ->
       munch [(SHF + 490, SHF + 506)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa0e88) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             x18 x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 (Z_to_bv 64 (SHF + 506)) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa0e38) fc None m (seg_rom b0segs)).
  Proof.
    intros me m bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 RZ MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX.
    destruct (rw_cells_CB_C1s b0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 16 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    do 16 sbf2.
    wstep. wstep. wstep. wstep.
    apply K; [exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_P6 : forall (me m : word -> option byte) (b : byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rw_cells b0segs m (SHF + 322) (shcB b) -> mem_inv b0segs m -> munch [(SHF + 322, SHF + 354)]%Z me m -> wmono b0segs me m ->
    frdW b0segs [(SHF + 322, SHF + 354)]%Z me (P + 208) [C8 (Z_to_bv 64 SHF)] ->
    (forall m', rw_cells b0segs m' (SHF + 322) (shcB z8) -> mem_inv b0segs m' -> munch [(SHF + 322, SHF + 354)]%Z me m' -> wmono b0segs me m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa1134) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (SHF + 362)) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x55310) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (SHF + 362)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa10a4) fc None m (seg_rom b0segs)).
  Proof.
    intros me m b x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 SH MI MU WMo V K.
    unfold shcB in SH.
    (* [comment removed for export] *)
    pose proof (V _ MU) as RO_. wstep. clear RO_.
    do 32 sb0. wstep. wstep. wstep.
    apply K; [unfold shcB; exact SH| exact MI| exact MU| exact WMo].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_P7 : forall (m : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    (evt b0segs Q (MS (mkR (Z_to_bv 64 0xa1140) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (SHF + 506)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x55310) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (SHF + 506)) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa1134) fc None m (seg_rom b0segs)).
  Proof.
    intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 K.
    wstep. wstep. wstep. exact K.
  Qed.
End B0MS.
End ACeilS1.
