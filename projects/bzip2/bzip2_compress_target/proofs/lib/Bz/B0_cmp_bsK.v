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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsS B0_cmp_msV B0_cmp_bsV B0_cmp_fsQ B0_cmp_fsV B0_cmp_fsP B0_cmp_msW B0_cmp_msS.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Lemma budget_q_magic_mod : ((Z.land (wf_clamp p_wf + -1) 255 * 171) mod 18446744073709551616 / 512 = budget_q)%Z.
Proof. pose proof wf_clamp_rng as W. rewrite land255_wf. rewrite Z.mod_small by lia. apply budget_q_magic. Qed.

Section B0BSK.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis YOK : amenv_ok X Y.
  Hypothesis YSH : (2147450880 <= SHF)%Z. Hypothesis YSHh : (SHF + 652 <= me_lo X)%Z.
  Hypothesis YSHF : (am_FB Y + 5216 <= SHF \/ SHF + 652 <= am_FB Y)%Z.
  Hypothesis YSHE : (me_E X + 55768 <= SHF \/ SHF + 652 <= me_E X)%Z.
  Hypothesis LQO : (me_n X + 34 <= me_qo X <= me_n X + 35)%Z. Hypothesis ALQ : (me_qo X = 2 * me_qq X)%Z.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WP5 := [(P, P + 500); (SHF + 634, SHF + 652)]%Z.
  Ltac sbf3 := wstep; change (le1 (Z_to_bv 64 (-13))) with [f3b]; mem_after_store.

  Lemma B0_bs_P5 : forall (m : word -> option byte) (bs : list byte) (wbud : word) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 : word),
    rw_cells b0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 w400; C8 w408; C8 w416; C8 w424; C8 w432; C8 w440; C8 w448; C8 w456; C8 w464; C8 w472; C8 w480; C8 (Z_to_bv 64 FB)] -> rw_cells b0segs m (P + 496) [C4 wbud] ->
    rw_cells b0segs m (SHF + 634) [CB 18 bs] ->
    rw_cells b0segs m (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] ->
    rw_cells b0segs m (E + 40) [C8 (Z_to_bv 64 FT)] -> rw_cells b0segs m (E + 56) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] ->
    rw_cells b0segs m (E + 88) [C4 (Z_to_bv 64 WORKFACTOR)] -> rw_cells b0segs m (E + 108) [C4 (Z_to_bv 64 n)] -> rw_cells b0segs m (E + 656) [C4 (Z_to_bv 64 0)] ->
    mem_inv b0segs m -> shzW b0segs WP5 m E (E + 55768) ->
    (* [comment removed for export] *)
    (forall m' (SHn : Z) (y12 y13 y14 y15 : word), (10000 <= n)%Z -> saddr (E + 108) SHn ->
       rw_cells b0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 (Z_to_bv 64 0); C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 (Z_to_bv 64 SHF); C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 (Z_to_bv 64 n); C8 w408; C8 w416; C8 w424; C8 (Z_to_bv 64 FT); C8 w440; C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 A1); C8 w472; C8 w480; C8 (Z_to_bv 64 FB)] ->
       rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 (n * budget_q))] ->
       mem_inv b0segs m' -> munch WP5 m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR (Z_to_bv 64 0xa10a4) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 128) y12 y13 y14 y15 x16 x17
                             (Z_to_bv 64 (E + 108)) (Z_to_bv 64 FB) (Z_to_bv 64 SHn) (Z_to_bv 64 FB) (Z_to_bv 64 (n * budget_q)) (Z_to_bv 64 E)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 (SHF + 506)) cSB x28 x29 x30 x31)
                        F (Z_to_bv 64 0x55310) fc None m' (seg_rom b0segs))) ->
    (* [comment removed for export] *)
    (forall m' (SHn : Z) (y12 y13 y14 : word), (n < 10000)%Z -> saddr (E + 108) SHn ->
       rw_cells b0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 (Z_to_bv 64 0); C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 (Z_to_bv 64 SHF); C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 (Z_to_bv 64 n); C8 w408; C8 w416; C8 w424; C8 (Z_to_bv 64 FT); C8 w440; C8 w448; C8 w456; C8 (Z_to_bv 64 A1); C8 w472; C8 w480; C8 (Z_to_bv 64 FB)] ->
       rw_cells b0segs m' (P + 496) [C4 wbud] ->
       mem_inv b0segs m' -> munch WP5 m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (E + 24)) (Z_to_bv 64 (E + 32)) y12 y13 y14 x15 x16 x17
                             (Z_to_bv 64 (E + 108)) (Z_to_bv 64 FB) (Z_to_bv 64 SHn) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 E)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 (SHF + 506)) cSB x28 x29 x30 x31)
                        F (Z_to_bv 64 0xa0fe0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 FB) x20 (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 E)
                          (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 (SHF + 506)) cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa0e88) fc None m (seg_rom b0segs)).
  Proof.
    intros m bs wbud w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 SL BUD RZ EAR EFT EPB EWF ENB EVB MI SHE KB KS.
    msenv_open1 XOK. amenv_open YOK. bz_params. box_ors.
    pose proof (munch_refl WP5 m) as MU. pose proof (wmono_refl b0segs m) as WM.
    destruct (rw_cells_CB_C1s b0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 18 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    (* [comment removed for export] *)
    wstep. do 17 sbf3. wstep. sbf3. clear RZ.
    (* [comment removed for export] *)
    brun_to 0xa0f40%Z.
    set (SHn := ((E + 108) / 8 + 2147450880)%Z). assert (ASN : saddr (E + 108) SHn) by reflexivity. clearbody SHn.
    (* [comment removed for export] *)
    brun_to 0xa0f90%Z.
    (* [comment removed for export] *)
    wstep. lit_store. brun_to 0xa0fac%Z.
    wstep; if_cases Kn; zify_cond_z Kn.
    - (* [comment removed for export] *)
      brun.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (JOINQ : forall (y12 : word),
          evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                                (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 qo) y12 (Z_to_bv 64 A1) (Z_to_bv 64 A2) x15 x16 x17
                                (Z_to_bv 64 (E + 108)) (Z_to_bv 64 FB) (Z_to_bv 64 SHn) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 E)
                                (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 (SHF + 506)) cSB x28 x29 x30 x31)
                           F (Z_to_bv 64 0xa1024) fc None mm (seg_rom b0segs))) end.
      2:{ if_cases Kpar; zify_cond_z Kpar.
          - (* [comment removed for export] *) enter_with (JOINQ _). st_eq. rewrite land1_mod2 in Kpar. clear - Kpar LQO ALQ. Z.div_mod_to_equations. lia.
          - (* [comment removed for export] *)
            brun_to 0xa1024%Z. enter_with (JOINQ _). st_eq. rewrite land1_mod2 in Kpar. clear - Kpar LQO ALQ. Z.div_mod_to_equations. lia. }
      intros y12.
      (* [comment removed for export] *)
      brun.
      if_true_z.
      (* [comment removed for export] *)
      wstep. wstep.
      eapply (evt_cut b0segs (fun ms' => ms' = _)).
      { wstep; if_cases Kwf; zify_cond_z Kwf.
        - apply evt_done. rewrite <- (wf_clamp_lt100 Kwf). reflexivity.
        - wstep. apply evt_done. rewrite (wf_clamp_ge100 Kwf). reflexivity. }
      intros ms' ->. pose proof (wf_clamp_rng) as WFR.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. wstep.
      rewrite budget_q_magic_mod.
      (* [comment removed for export] *)
      pose proof (budget0_rng n ltac:(lia)) as BQR.
      brun_to 0xa1094%Z. wstep. wstep. wstep. wstep.
      enter_with (KB _ SHn _ _ _ _ ltac:(lia) ASN); [st_eq| exact SL| exact BUD| assumption| exact MU| exact WM].
    - (* [comment removed for export] *)
      brun_to 0xa0fe0%Z.
      enter_with (KS _ SHn _ _ _ ltac:(lia) ASN); [st_eq| exact SL| exact BUD| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bs_E4s : forall (m : word -> option byte) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w408 w416 w424 w440 w448 w456 w464 w472 w480 w488 : word)
      (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells b0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 (Z_to_bv 64 0); C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232; C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336; C8 w344; C8 w352; C8 w360; C8 w368; C8 w376; C8 w384; C8 w392; C8 (Z_to_bv 64 n); C8 w408; C8 w416; C8 w424; C8 (Z_to_bv 64 FT); C8 w440; C8 w448; C8 w456; C8 w464; C8 w472; C8 w480; C8 w488] ->
    rw_cells b0segs m (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> mem_inv b0segs m ->
    (evt b0segs Q (MS (mkR (Z_to_bv 64 0xa0ff8) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 n) (Z_to_bv 64 0) x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa4c28) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (E + 24)) (Z_to_bv 64 (E + 32)) x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa0fe0) fc None m (seg_rom b0segs)).
  Proof.
    intros m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w360 w368 w376 w384 w392 w408 w416 w424 w440 w448 w456 w464 w472 w480 w488 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SL EAR MI K.
    msenv_open1 XOK. amenv_open YOK.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. exact K.
  Qed.
End B0BSK.
End ACeilS1.
