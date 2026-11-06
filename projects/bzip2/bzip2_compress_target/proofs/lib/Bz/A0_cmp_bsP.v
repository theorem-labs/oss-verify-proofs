(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_msV A0_cmp_bsV A0_cmp_fsP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac cutk R k H sz nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R; let zn := eval cbv in (Z.to_nat sz) in change (Z.of_nat zn) with sz in R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by lia end
  end.

(* [comment removed for export] *)
Ltac slots_cut P CBIG C16a :=
  lazymatch type of CBIG with rw_cells ?segs ?m ?A _ =>
    apply (rw_cells_split_CB segs m A [] 416 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8; 8;8;8;8;8;8; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8; 8;8;8;8; 8; 8; 4; 4]%nat) in CBIG; [| reflexivity];
    cbn [mk_CB_cells app] in CBIG;
    repeat (match type of CBIG with context [CB ?k (firstn ?a ?b)] => let v := fresh "jc" in set (v := firstn a b) in CBIG; clearbody v end);
    cb8_all CBIG;
    let C16b := fresh "C16b" in let C16 := fresh "C16" in let C104 := fresh "C104" in let C152 := fresh "C152" in let C200 := fresh "C200" in
    let C216 := fresh "C216" in let C384 := fresh "C384" in let C416 := fresh "C416" in let C424 := fresh "C424" in let C432 := fresh "C432" in
    cutk CBIG 10%nat C16b 80 (P + 104)%Z;
    lazymatch type of C16a with rw_cells _ _ _ ?cs1 => lazymatch type of C16b with rw_cells _ _ _ ?cs2 =>
      assert (C16 : rw_cells segs m (P + 16)%Z (cs1 ++ cs2))
        by (apply (proj2 (rw_cells_app_iff_c segs m (P + 16)%Z cs1 cs2)); split; [exact C16a| cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8%Z; replace (P + 16 + 8)%Z with (P + 24)%Z by lia; exact C16b]) end end;
    cbn [app] in C16; clear C16a C16b;
    cutk CBIG 6%nat C104 48 (P + 152)%Z; cutk CBIG 6%nat C152 48 (P + 200)%Z; cutk CBIG 2%nat C200 16 (P + 216)%Z; cutk CBIG 21%nat C216 168 (P + 384)%Z;
    cutk CBIG 4%nat C384 32 (P + 416)%Z; cutk CBIG 1%nat C416 8 (P + 424)%Z; cutk CBIG 1%nat C424 8 (P + 432)%Z; cutk CBIG 1%nat C432 4 (P + 436)%Z
  end.

(* [comment removed for export] *)
Definition MSAVED (X : msenv) : list cell :=
  [C8 (me_s11 X); C8 (me_s10 X); C8 (me_s9 X); C8 (me_s8 X); C8 (me_s7 X); C8 (me_s6 X); C8 (me_s5 X); C8 (me_s4 X); C8 (me_s3 X);
   C8 (me_s2 X); C8 (me_s1 X); C8 (me_s0 X); C8 (me_ra X)].

Section A0BSP1.
  Variable X : msenv. Variable P : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X.
  Hypothesis YPl : (me_lo X <= P)%Z. Hypothesis YPh : (P + 544 <= bv_unsigned (me_sp X))%Z. Hypothesis YPa : (bv_unsigned (me_sp X) <= P + 560)%Z.
  Notation usp := (bv_unsigned (me_sp X)). Notation E := (me_E X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X). Notation lo := (me_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).

  Lemma A0_bs_P1 : forall (qP : Z) (m : word -> option byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk a0segs m lo usp -> mem_inv a0segs m -> aconsts A0C m -> aconsts_uar A0C m ->
    (forall m' (v0 v8 : word) (v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 : word) (v104 v112 v120 v128 v136 v144 : word) (v152 v160 v168 v176 v184 v192 : word)
            (v200 v208 : word) (v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368 v376 : word)
            (v384 v392 v400 v408 v416 v424 : word) (j432 jbud : list byte) (y11 y12 : word),
      rw_cells a0segs m' P [C8 v0; C8 v8] ->
      rw_cells a0segs m' (P + 16) [C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96] ->
      rw_cells a0segs m' (P + 104) [C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144] ->
      rw_cells a0segs m' (P + 152) [C8 v152; C8 v160; C8 v168; C8 v176; C8 v184; C8 v192] ->
      rw_cells a0segs m' (P + 200) [C8 v200; C8 v208] ->
      rw_cells a0segs m' (P + 216) [C8 v216; C8 v224; C8 v232; C8 v240; C8 v248; C8 v256; C8 v264; C8 v272; C8 v280; C8 v288; C8 v296; C8 v304; C8 v312;
                                    C8 v320; C8 v328; C8 v336; C8 v344; C8 v352; C8 v360; C8 v368; C8 v376] ->
      rw_cells a0segs m' (P + 384) [C8 v384; C8 v392; C8 v400; C8 v408] -> rw_cells a0segs m' (P + 416) [C8 v416] -> rw_cells a0segs m' (P + 424) [C8 v424] ->
      rw_cells a0segs m' (P + 432) [CB 4 j432] -> rw_cells a0segs m' (P + 436) [CB 4 jbud] ->
      stk a0segs m' (P + 440) (usp + -104) -> rw_cells a0segs m' (usp + -104) (MSAVED X) ->
      stk a0segs m' lo P -> mem_inv a0segs m' -> munch [(P, usp)]%Z m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x975fc) (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P) (Z_to_bv 64 5216) y11 y12 a3 a4 a5 a6 a7
                            (me_s2 X) cSB (me_s4 X) (me_s5 X) (me_s6 X) (me_s7 X) (me_s8 X) (Z_to_bv 64 E) (me_s10 X) (me_s11 X) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e44c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (me_ra X) (me_sp X) gp tp t0 t1 t2 (me_s0 X) (me_s1 X) (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7
                          (me_s2 X) (me_s3 X) (me_s4 X) (me_s5 X) (me_s6 X) (me_s7 X) (me_s8 X) (me_s9 X) (me_s10 X) (me_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x97588) fc None m (seg_rom a0segs)).
  Proof.
    intros qP m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    msenv_open1 XOK.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar A0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    assert (CASE : (P = usp - 544 \/ P = usp - 560)%Z) by lia.
    assert (ELAND : Z.land (usp + -544) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - CASE EqP ALS. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 544%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 544 _ [] [8;8;8; 416; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      lazymatch type of FR with context [CB 416 ?j] => set (jj := j) in FR; clearbody jj end.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -544)%Z with P in FR, ST by lia.
      (* [comment removed for export] *)
      arun_to 0x3e44c%Z.
      cb8_all FR.
      cutk FR 2%nat C0 16 (P + 16)%Z. cutk FR 1%nat C16a 8 (P + 24)%Z. cutk FR 1%nat CBIG 416 (usp + -104)%Z.
      slots_cut P CBIG C16a.
      eapply K; [exact C0| exact C16| exact C104| exact C152| exact C200| exact C216| exact C384| exact C416| exact C424| exact C432| exact CBIG| | exact FR| exact ST| assumption| exact MU| exact WM].
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 560%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 560 _ [] [8;8;8; 416; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      lazymatch type of FR with context [CB 416 ?j] => set (jj := j) in FR; clearbody jj end.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -560)%Z with P in FR, ST by lia.
      arun_to 0x3e44c%Z.
      cb8_all FR.
      cutk FR 2%nat C0 16 (P + 16)%Z. cutk FR 1%nat C16a 8 (P + 24)%Z. cutk FR 1%nat CBIG 416 (P + 440)%Z. cutk FR 2%nat GAPc 16 (usp + -104)%Z.
      pose proof (stk_of_rw_cells a0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 440 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      slots_cut P CBIG C16a.
      eapply K; [exact C0| exact C16| exact C104| exact C152| exact C200| exact C216| exact C384| exact C416| exact C424| exact C432| exact CBIG| exact GAPs| exact FR| exact ST| assumption| exact MU| exact WM].
  Qed.
End A0BSP1.
End ACeilS1.
