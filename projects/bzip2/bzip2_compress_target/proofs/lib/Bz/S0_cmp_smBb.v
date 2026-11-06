(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 BzCFactsSmA BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpFsKit0 CmpHmKit CmpSmKit CmpSmKit2 CmpSmKit20.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smBfz S0_cmp_smBrz.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.
Module S0_cmp_smBa.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit20.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section GB.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word) (iter : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let XA20 := ident:(XA20) in let XA21 := ident:(XA21) in let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    destruct S as (?AEA1 & _).
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.

  (* [comment removed for export] *)
  Notation GR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 37708)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_bt : forall (n : nat) (t bc bt : Z) (cb cost : zarr) (m : word -> option byte)
      (ra t0 t1 t2 a3 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= bc <= 999999999)%Z -> (-1 <= bt < nG)%Z ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) -> COSTREL cb cost nG ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall bc' bt' (a6 : word), sm_best n cost t bc bt = (bc', bt') -> (0 <= bc' <= 999999999)%Z -> (-1 <= bt' < nG)%Z ->
      evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 bt') (Z_to_bv 64 bt') (Z_to_bv 64 bc') (Z_to_bv 64 bc') a6 a7 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16cf0) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (usp + 888 + 2 * t)) (Z_to_bv 64 bt) a3 (Z_to_bv 64 bc) (Z_to_bv 64 bc) a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16cc4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t bc bt cb cost m ra t0 t1 t2 a3 a6 a7 s4 s6 t3 t4 t5 t6 Ht Ht0 Hn Hbc Hbt COST [CBOK CREL] CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (zb8_length_nat cb 12) as LC.
    rewrite sm_best_S in K.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m (usp + 888) cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstep. clear RD. rewrite (zx16_lit (zget cost t)) by lia.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1.
    - (* [comment removed for export] *)
      lstep. lstep; if_cases K2; zify_cond_z K2; [exfalso; lia|]. lstep. lstep. lstep. lstep. lstep.
      replace (zget cost t <? bc)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
      lstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (t + 1)%Z bc bt cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
      + assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K.
        enter_with (K bc bt _); [st_eq| reflexivity| lia| lia].
    - (* [comment removed for export] *)
      lstep. lstep. lstep; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        lstep. lstep. lstep. lstep.
        replace (zget cost t <? bc)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        lstep; if_cases Ke; zify_cond_z Ke.
        * enter_with (IH (t + 1)%Z (zget cost t) t cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
        * assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K.
          enter_with (K (zget cost t) t _); [st_eq| reflexivity| lia| lia].
      + (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. lstep.
        replace (zget cost t <? bc)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
        lstep; if_cases Ke; zify_cond_z Ke.
        * enter_with (IH (t + 1)%Z bc bt cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
        * assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K.
          enter_with (K bc bt _); [st_eq| reflexivity| lia| lia].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_csti : forall (n : nat) (t icv : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= icv < A)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv s0segs m -> munch [(usp + 888, usp + 900)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' cb' (a3 a4 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u8arr s0segs m' (usp + 888) (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow_t n cost len icv t) nG ->
      mem_inv s0segs m' -> munch [(usp + 888, usp + 900)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra t0 t1 t2 a0 (Z_to_bv 64 (E + 37708 + 258 * nG + icv)) (Z_to_bv 64 (usp + 888 + 2 * nG)) a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16ca4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra t0 t1 t2 a0 (Z_to_bv 64 (E + 37708 + 258 * t + icv)) (Z_to_bv 64 (usp + 888 + 2 * t)) a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16c88) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t icv cb cost len m mf ra t0 t1 t2 a0 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 Ht Ht0 Hn Hicv LF LEN COST [CBOK CREL] MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (zb8_length_nat cb 12) as LC. pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    destruct (LF t icv ltac:(lia) ltac:(lia)) as [Dl Rl].
    rewrite sm_cost_slow_t_S in K.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + icv) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD.
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m (usp + 888) cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstep. clear RD.
    (* [comment removed for export] *)
    lstep. rewrite (unsigned_lit8 (zget len (258 * t + icv))) by lia.
    pose proof (u8arr_storeN_ok s0segs _ (usp + 888) _ (2 * t) 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (usp + 888 + 2 * t)%Z. zb8_store2 COST (2 * t)%Z.
    pose proof (COSTREL_set cb cost nG t (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx16 (Z_to_bv 64 (zget cost t))) + zget len (258 * t + icv)))) (conj CBOK CREL) ltac:(lia)) as CR'.
    rewrite (cost_upd_mod (zget cost t) (zget len (258 * t + icv))) in CR' by lia.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z icv _ _ len _ mf); [st_eq| lia| lia| lia| lia| exact LF| exact LEN| exact COST| exact CR'| assumption| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow_t] in K.
      enter_with (K _ _ _ _); [st_eq| exact LEN| exact COST| exact CR'| assumption| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_csto : forall (n : nat) (i ge : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (ra t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = ge + 1)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u8arr s0segs m (usp + 888) (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv s0segs m -> munch [(usp + 888, usp + 900)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' cb' (a1 a2 a3 a4 : word),
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u8arr s0segs m' (usp + 888) (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow n cost len arr1 nG i) nG ->
      mem_inv s0segs m' -> munch [(usp + 888, usp + 900)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) t1 t2 (Z_to_bv 64 (ge + 1)) a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16cb0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) t1 t2 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16c74) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i ge cb cost len m mf ra t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 Hi Hi0 Hn Hge LF AR1 LEN COST CR MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (MV i ltac:(lia)) as MVi.
    rewrite sm_cost_slow_S in K.
    (* [comment removed for export] *)
    lstep. lstep.
    pose proof (zb8_read2 s0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstep. clear RD. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    lstep. lstep.
    enter_with (S0_sm_csti (Z.to_nat nG) 0 (mtfv_at arr1 i) cb cost len m m);
      [st_eq| lia| lia| lia| lia| exact LF| exact LEN| exact COST| exact CR| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear LEN COST CR MI. intros m1 cb1 ya3 ya4 LEN COST CR MI MU1 WM1.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ge cb1 _ len m1 mf); [st_eq| lia| lia| lia| lia| exact LF| exact AR1| exact LEN| exact COST| exact CR| exact MI| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow] in K.
      enter_with (K m1 cb1 _ _ _ _); [st_eq| exact AR1| exact LEN| exact COST| exact CR| exact MI| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_rfsl : forall (n : nat) (i iend bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a2 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = iend)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (iend <= nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + Z.of_nat n <= 2000000000)%Z ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv s0segs m -> munch [(E + 45448, E + 51640)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' rf' (a2 a5 : word),
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc n rf arr1 bt i -> RFrow rf' bt A (B + Z.of_nat n) ->
      mem_inv s0segs m' -> munch [(E + 45448, E + 51640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 (A1 + 2 * iend)) (Z_to_bv 64 (A1 + 2 * iend)) a2 (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1721c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 (A1 + 2 * i)) (Z_to_bv 64 (A1 + 2 * iend)) a2 (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x171f8) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i iend bt B rf m mf ra t0 t1 t2 a2 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 Hi Hi0 Hn Hend Hbt HB HBn AR1 RFQ RFF MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (zb8_length_nat arr1 ARR1_SIZE) as LA1.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    pose proof (MV i ltac:(lia)) as MVi. destruct (RFF (mtfv_at arr1 i) MVi) as [Dr Rr].
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstep. clear RD. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 45448) rf (jseg J 45448 6192) 1548 (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(lia) Dr ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite (sx32_of_Z (zget rf (258 * bt + mtfv_at arr1 i))) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    lstep. lstep.
    pose proof (u32arr_store_ok s0segs m (E + 45448) _ (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (E + 45448 + 4 * (258 * bt + mtfv_at arr1 i))%Z.
    ovw_store RFQ (258 * bt + mtfv_at arr1 i)%Z (zget rf (258 * bt + mtfv_at arr1 i) + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset rf (258 * bt + mtfv_at arr1 i) (zget rf (258 * bt + mtfv_at arr1 i) + 1)) with (zincr rf (258 * bt + mtfv_at arr1 i)) in RFQ.
    pose proof (RFrow_incr rf bt A B (mtfv_at arr1 i) RFF MVi) as RFF'.
    rewrite sm_rfreq_inc_S in K.
    (* [comment removed for export] *)
    lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z iend bt (B + 1)%Z _ _ mf);
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact AR1| exact RFQ| exact RFF'| assumption| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
      intros m' rf' y2 y5 AR1' RFQ' E' RFF2. eapply K; [exact AR1'| exact RFQ'| exact E'| eapply RFrow_weaken; [exact RFF2| lia]].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_inc] in K.
      enter_with (K _ _ _ _); [st_eq| exact AR1| exact RFQ| reflexivity| eapply RFrow_weaken; [exact RFF'| lia]| assumption| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_self : forall (bt nSel ff : Z) (fave sel : zarr) (m mf : word -> option byte) (x584 : word)
      (ra t0 t1 t2 a4 a5 a6 a7 s6 t3 t5 t6 : word),
    (0 <= bt < nG)%Z -> (0 <= nSel < 18002)%Z -> (0 <= zget fave bt <= 18002)%Z -> (ff = 0 \/ ff = 1)%Z ->
    u32arr s0segs m (usp + 616) (zw32 fave 6) ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    mem_inv s0segs m -> munch [(E + 1704, E + 19706); (usp + 616, usp + 640)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m', ff = 1%Z ->
      u32arr s0segs m' (usp + 616) (zw32 (zincr fave bt) 6) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      mem_inv s0segs m' -> munch [(E + 1704, E + 19706); (usp + 616, usp + 640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 (usp + 616 + 4 * bt)) (Z_to_bv 64 (zget fave bt + 1)) (Z_to_bv 64 (E + 1704 + nSel)) (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 (Z_to_bv 64 nSel) s6 t3 (Z_to_bv 64 ff) t5 t6)
                       F (Z_to_bv 64 0x16d18) fc None m' (seg_rom s0segs))) ->
    (forall m', ff = 0%Z ->
      u32arr s0segs m' (usp + 616) (zw32 (zincr fave bt) 6) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      mem_inv s0segs m' -> munch [(E + 1704, E + 19706); (usp + 616, usp + 640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 (usp + 616 + 4 * bt)) (Z_to_bv 64 (zget fave bt + 1)) (Z_to_bv 64 (E + 1704 + nSel)) (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 (Z_to_bv 64 nSel) s6 t3 (Z_to_bv 64 ff) t5 t6)
                       F (Z_to_bv 64 0x171d8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 bt) (Z_to_bv 64 bt) a4 a5 a6 a7 (Z_to_bv 64 nSel) s6 t3 (Z_to_bv 64 ff) t5 t6)
                     F (Z_to_bv 64 0x16cf0) fc None m (seg_rom s0segs)).
  Proof.
    intros bt nSel ff fave sel m mf x584 ra t0 t1 t2 a4 a5 a6 a7 s6 t3 t5 t6 Hbt HnS Hfv Hff FAVE SEL C576 MI MU WM CE SPB KF KS.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (zw32_length_nat fave 6) as LFV. pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length sel (jseg J 1704 18002) 18002 ltac:(lia)) as LSL.
    (* [comment removed for export] *)
    lstep. lstep.
    pose proof (zw32_read s0segs m (usp + 616) fave 6 bt _ FAVE ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite (sx32_of_Z (zget fave bt)) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    lstep. lstep.
    pose proof (u8arr_store_ok s0segs _ (E + 1704) _ nSel _ SEL ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (E + 1704 + nSel)%Z. ovb_store1 SEL nSel.
    replace (wr8 sel nSel (bv_unsigned (Z_to_bv 64 bt))) with (zset sel nSel (bt mod 256)) in SEL by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    lstep.
    pose proof (u32arr_store_ok s0segs _ (usp + 616) _ bt _ FAVE ltac:(rewrite zw32_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2.
    lstep. store_addr (usp + 616 + 4 * bt)%Z. zw32_store FAVE bt (zget fave bt + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset fave bt (zget fave bt + 1)) with (zincr fave bt) in FAVE.
    (* [comment removed for export] *)
    lstep. lstep; if_cases Kf; zify_cond_z Kf.
    - enter_with (KS _ ltac:(lia)); [st_eq| exact FAVE| exact SEL| exact C576| assumption| exact MU| exact WM].
    - enter_with (KF _ ltac:(lia)); [st_eq| exact FAVE| exact SEL| exact C576| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_rfsg : forall (gs ge bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (ra a0 a1 a2 a4 a5 a6 a7 s4 s6 t4 t5 t6 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + (ge + 1 - gs) <= 2000000000)%Z ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    mem_inv s0segs m -> munch [(E + 45448, E + 51640)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' rf' (a0 a1 a2 a5 : word),
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc (Z.to_nat (ge + 1 - gs)) rf arr1 bt gs -> RFrow rf' bt A (B + (ge + 1 - gs)) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      mem_inv s0segs m' -> munch [(E + 45448, E + 51640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge) a0 a1 a2 (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 s4 s6 (Z_to_bv 64 (ge - gs)) t4 t5 t6)
                       F (Z_to_bv 64 0x1721c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge) a0 a1 a2 (Z_to_bv 64 (bt * 1032)) a4 a5 a6 a7 s4 s6 (Z_to_bv 64 (ge - gs)) t4 t5 t6)
                     F (Z_to_bv 64 0x171d8) fc None m (seg_rom s0segs)).
  Proof.
    intros gs ge bt B rf m mf ra a0 a1 a2 a4 a5 a6 a7 s4 s6 t4 t5 t6 Hgs Hge Hbt HB HBn AR1 RFQ RFF S8 MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    unfold sm_slots3 in S8. cbv zeta in S8.
    (* [comment removed for export] *)
    lstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep.
    replace ((ge - gs) * 4294967296 / 2147483648)%Z with ((ge - gs) * 2)%Z by (symmetry; rewrite <- (Z.div_mul ((ge - gs) * 2) 2147483648) by lia; f_equal; lia).
    lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (S0_sm_rfsl (Z.to_nat (ge + 1 - gs)) gs (ge + 1) bt B rf mm mm);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact AR1| exact RFQ| exact RFF| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|];
    clear AR1 RFQ RFF MI; intros m' rf' y2 y5 AR1 RFQ E' RFF MI MU1 WM1;
    transport_after_call s0segs mm m' MU1 WM1; clear MU1 WM1 end.
    enter_with (K m' rf' _ _ _ _); [st_eq| exact AR1| exact RFQ| exact E'| replace (B + (ge + 1 - gs))%Z with (B + Z.of_nat (Z.to_nat (ge + 1 - gs)))%Z by lia; exact RFF| exact S8| exact MI| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fastf (gs : Z) : Z := if ((nG =? 6) && (GE nMTF gs - gs =? 49))%Z%bool then 1 else 0.
  Lemma S0_sm_head : forall (gs : Z) (jc : list byte) (m mf : word -> option byte) (x584 : word)
      (ra t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> length jc = 12%nat ->
    u8arr s0segs m (usp + 888) jc ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    mem_inv s0segs m -> munch [(usp + 888, usp + 900)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (a0 : word), let ge := GE nMTF gs in fastf gs = 1%Z ->
      u8arr s0segs m' (usp + 888) (zb8 znew 12) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      mem_inv s0segs m' -> munch [(usp + 888, usp + 900)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge) a0 (Z_to_bv 64 (flag6 nG)) a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 (ge - gs)) (Z_to_bv 64 (fastf gs)) t5 t6)
                       F (Z_to_bv 64 0x161e8) fc None m' (seg_rom s0segs))) ->
    (forall m' (a0 : word), let ge := GE nMTF gs in fastf gs = 0%Z ->
      u8arr s0segs m' (usp + 888) (zb8 znew 12) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      mem_inv s0segs m' -> munch [(usp + 888, usp + 900)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge) a0 (Z_to_bv 64 (flag6 nG)) a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 (ge - gs)) (Z_to_bv 64 (fastf gs)) t5 t6)
                       F (Z_to_bv 64 0x16c6c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 gs) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x161b4) fc None m (seg_rom s0segs)).
  Proof.
    intros gs jc m mf x584 ra t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 Hgs Ljc COST C576 MI MU WM CE SPB KF KS.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    cps_destruct (cost_cells_of_junk s0segs m (usp + 888) jc COST Ljc) as (w1 & w2 & CC). clear COST.
    (* [comment removed for export] *)
    lstep. lstep. (lstep; lit_store).
    lstep.
    pose proof (cost_zero_cells s0segs _ (usp + 888) CC) as COST. clear CC.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GEd : forall ge, ge = GE nMTF gs -> forall (xt2 : word), xt2 = Z_to_bv 64 ge ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 gs) (Z_to_bv 64 gs) xt2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x161cc) fc None mm (seg_rom s0segs))) end.
    2:{ lstep; if_cases K1; zify_cond_z K1.
        - eapply (GEd (gs + 49)%Z); [unfold GE, BZ_G_SIZE; replace (nMTF <=? gs + 50 - 1)%Z with false by (symmetry; apply Z.leb_gt; lia); lia| reflexivity].
        - lstep. eapply (GEd (nMTF - 1)%Z); [unfold GE, BZ_G_SIZE; replace (nMTF <=? gs + 50 - 1)%Z with true by (symmetry; apply Z.leb_le; lia); lia| f_equal; lia]. }
    intros ge Ege xt2 ->.
    pose proof (GE_facts nMTF gs ltac:(lia)) as GF. rewrite <- Ege in GF. cps_destruct GF as (G1 & G2 & G3).
    (* [comment removed for export] *)
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    lstep. lstep. lstep. rewrite (seqz_mod64 (ge - gs + -49)) by lia. lstep. lstep. lstep.
    assert (FF : forall b, Z.land (flag6 nG) (Z.b2z b) = (if ((nG =? 6) && b)%bool then 1 else 0)%Z).
    { intros b. unfold flag6. destruct (nG =? 6)%Z, b; reflexivity. }
    lazymatch goal with |- context [Z.land (flag6 nG) (Z.b2z ?b)] =>
      rewrite (FF b); replace b with (ge - gs =? 49)%Z by (destruct (Z.eqb_spec (ge - gs) 49) as [EE|NE]; [symmetry; apply Z.eqb_eq; lia| symmetry; apply Z.eqb_neq; lia]) end.
    change (if ((nG =? 6) && (ge - gs =? 49))%bool then 1%Z else 0%Z) with (fastf gs) || (rewrite Ege; change (if ((nG =? 6) && (GE nMTF gs - gs =? 49))%bool then 1%Z else 0%Z) with (fastf gs); rewrite <- Ege).
    assert (Hff : (fastf gs = 0 \/ fastf gs = 1)%Z) by (unfold fastf; destruct (_ && _)%bool; lia).
    (* [comment removed for export] *)
    lstep; if_cases Kf; zify_cond_z Kf.
    - subst ge. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ ltac:(lia)) end; [st_eq| exact COST| exact C576| assumption| exact MU| exact WM].
    - subst ge. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KF mm _ ltac:(lia)) end; [st_eq| exact COST| exact C576| assumption| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_tail : forall (g : eg) (ge1 bc totc nSel : Z) (m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a5 a6 s6 t3 t4 t5 t6 : word),
    g_mtf g = true -> (0 <= ge1 <= nMTF)%Z -> (0 <= bc < 4294967296)%Z -> (0 <= totc)%Z -> (totc + bc < 9223372036854775808)%Z -> (0 <= nSel < 18002)%Z ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    ((ge1 < nMTF)%Z ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 ge1) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 (Z_to_bv 64 bc) a5 a6 (Z_to_bv 64 (totc + bc)) (Z_to_bv 64 (nSel + 1)) s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x161b4) fc None m (seg_rom s0segs))) ->
    ((ge1 = nMTF)%Z ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 ge1) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 (Z_to_bv 64 bc) a5 a6 (Z_to_bv 64 (totc + bc)) (Z_to_bv 64 (nSel + 1)) s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17230) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 ge1) t1 t2 a0 a1 a2 a3 (Z_to_bv 64 bc) a5 a6 (Z_to_bv 64 totc) (Z_to_bv 64 nSel) s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1721c) fc None m (seg_rom s0segs)).
  Proof.
    intros g ge1 bc totc nSel m ra t1 t2 a0 a1 a2 a3 a5 a6 s6 t3 t4 t5 t6 GM Hge Hbc Htc Htb HnS EH2 CE SPB KL KE.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    lstep. rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
    lstep. lstep. lstep; if_cases Kb; zify_cond_z Kb.
    - enter_with (KE ltac:(lia)); [st_eq].
    - lstep. enter_with (KL ltac:(lia)); [st_eq].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_btg : forall (cb cost : zarr) (m : word -> option byte) (x584 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    u8arr s0segs m (usp + 888) (zb8 cb 12) -> COSTREL cb cost nG ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall bc' bt' (a6 : word), sm_best (Z.to_nat nG) cost 0 999999999 (-1) = (bc', bt') -> (0 <= bc' <= 999999999)%Z -> (-1 <= bt' < nG)%Z ->
      evt s0segs Q (MS (GR ra t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 bt') (Z_to_bv 64 bt') (Z_to_bv 64 bc') (Z_to_bv 64 bc') a6 a7 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16cf0) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16cb0) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m x584 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 COST CR C576 CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    enter_with (S0_sm_bt (Z.to_nat nG) 0 999999999 (-1) cb cost m);
      [st_eq| lia| lia| lia| lia| lia| exact COST| exact CR| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
  Qed.
End GB.

End ACeilS1.
End S0_cmp_smBa.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBfz OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBrz OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBb.S0_cmp_smBa.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section GG.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word) (iter : Z) (lp len : zarr).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GM : g_mtf g = true.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z. Hypothesis HIT : (0 <= iter < 4)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Hypothesis LF : forall t v, (0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z.
  Hypothesis LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * v + j) = true /\ (0 <= zget lp (4 * v + j) < 2097152)%Z.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let XA20 := ident:(XA20) in let XA21 := ident:(XA21) in let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    destruct S as (?AEA1 & _).

  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Notation GR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 37708)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Definition Wg : list (Z * Z) := [(E + 1704, E + 19706); (E + 45448, E + 51640); (usp + 184, usp + 592); (usp + 616, usp + 640); (usp + 888, usp + 900)]%Z.

  (* [comment removed for export] *)
  Ltac gside :=
    lazymatch goal with
    | |- u8arr _ _ A1 _ => eassumption
    | |- u8arr _ _ (E + 37708)%Z _ => eassumption
    | |- u8arr _ _ (E + 1704)%Z _ => eassumption
    | |- u8arr _ _ (usp + 888)%Z _ => eassumption
    | |- u8arr _ _ (usp + 184)%Z _ => eassumption
    | |- u32arr _ _ (E + 51640)%Z _ => eassumption
    | |- u32arr _ _ (E + 45448)%Z _ => eassumption
    | |- u32arr _ _ (usp + 616)%Z _ => eassumption
    | |- rw_cells _ _ (usp + 8)%Z _ => first [eassumption| unfold sm_slots3; cbv zeta; eassumption]
    | |- rw_cells _ _ (usp + 576)%Z _ => eassumption
    | |- rw_cells _ _ (E + 640)%Z _ => eassumption
    | |- mem_inv _ _ => assumption
    | |- COSTREL _ _ _ => first [assumption| eapply COSTREL_le; [eassumption| lia]]
    | |- munch _ _ _ => first [eassumption| apply munch_refl]
    | |- wmono _ _ _ => first [eassumption| apply wmono_refl]
    | |- forall _, _ => first [eassumption| idtac]
    | |- _ => first [assumption| eassumption| lia| idtac]
    end.

  Lemma S0_sm_grp : forall (rf sel cost fave : zarr) (gs nSel totc : Z) (jc Jsp : list byte) (x584 : word) (m me : word -> option byte)
      (ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18001)%Z -> (0 <= totc <= 65535 * nSel)%Z ->
    (forall t, (0 <= t < nG)%Z -> RFrow rf t A gs) -> (forall t, (0 <= t < 6)%Z -> (0 <= zget fave t <= nSel)%Z) ->
    length jc = 12%nat -> length Jsp = 392%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    u8arr s0segs m (usp + 184) Jsp ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u32arr s0segs m (usp + 616) (zw32 fave 6) ->
    u8arr s0segs m (usp + 888) jc ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    mem_inv s0segs m -> munch Wg me m -> wmono s0segs me m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (Jsp' : list byte) (x584' : word) (cb' : zarr) (ra' t1' t2' a0' a1' a2' a3' a5' a6' s6' t3' t4' t5' t6' : word),
      let ge := GE nMTF gs in let cst := COSTC arr1 len lp nG gs ge cost in let r := sm_best (Z.to_nat nG) cst 0 999999999 (-1) in
      length Jsp' = 392%nat -> (0 <= snd r < nG)%Z -> (0 <= fst r <= 65535)%Z ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (sm_rfreq_inc (Z.to_nat (ge - gs + 1)) rf arr1 (snd r) gs) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (snd r mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      u8arr s0segs m' (usp + 184) Jsp' ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584'; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u32arr s0segs m' (usp + 616) (zw32 (zincr fave (snd r)) 6) ->
      u8arr s0segs m' (usp + 888) (zb8 cb' 12) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      mem_inv s0segs m' -> munch Wg me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (GR ra' (Z_to_bv 64 (ge + 1)) t1' t2' (Z_to_bv 64 nMTF) a1' a2' a3' (Z_to_bv 64 (fst r)) a5' a6' (Z_to_bv 64 (totc + fst r)) (Z_to_bv 64 (nSel + 1)) s6' t3' t4' t5' t6')
                       F (Z_to_bv 64 (if ge + 1 <? nMTF then 0x161b4 else 0x17230)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 gs) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 totc) (Z_to_bv 64 nSel) s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x161b4) fc None m (seg_rom s0segs)).
  Proof.
    intros rf sel cost fave gs nSel totc jc Jsp x584 m me ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6
           Hgs HnS Htc RFR FVB Ljc LJsp AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold Wg in MU. unfold EHEAD2 in EH2. unfold sm_slots3 in S8. cbv zeta in S8.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    set (ge := GE nMTF gs) in *.
    (* [comment removed for export] *)
    eapply (S0_sm_head cx e Q sp gp tp F fc CX SEP HM gs jc m m x584);
      [exact Hgs| exact Ljc| exact COST| exact C576| exact MI| apply munch_refl| apply wmono_refl| exact CE| exact SPB| |].
    all: clear COST C576 MI; intros m1 xa0; cbv zeta; intros Hff COST C576 MI MU1 WM1; fold ge in Hff |- *;
         transport_after_call s0segs m m1 MU1 WM1; clear MU1 WM1.
    - (* [comment removed for export] *)
      assert (NG6 : nG = 6%Z) by (unfold fastf, fastb in Hff; destruct (Z.eqb_spec nG 6); [assumption| cbn in Hff; lia]).
      assert (G49 : (ge - gs = 49)%Z).
      { unfold fastf in Hff. fold ge in Hff. destruct (Z.eqb_spec (ge - gs) 49); [assumption|]. rewrite NG6 in Hff. cbn in Hff. lia. }
      assert (FB : fastb nG nMTF gs = true).
      { unfold fastb. fold ge. rewrite NG6. replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      (* [comment removed for export] *)
      enter_with (S0_fc cx e Q sp gp tp F fc sv w24 w56 lp znew gs iter nSel totc).
      all: gside.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { intros k j Hk Hj. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj2 (LPF NG6 _ _ Hq Hj)). }
      { intros k j Hk Hj. unfold QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. exact (proj1 (LPF NG6 _ _ Hq Hj)). }
      clear AR1 LPK S8 SPL C576 COST MI.
      intros m2 S0 S1 S2 Jsp2 ys6 ya6 yt5 yt6 yra ES0 ES1 ES2 AR1 LPK S8 SPL LJ2 C576 COST MI MU2 WM2. unfold sm_slots3 in S8. cbv zeta in S8.
      transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      assert (HS0 : (0 <= S0)%Z). { rewrite ES0. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS1 : (0 <= S1)%Z). { rewrite ES1. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      assert (HS2 : (0 <= S2)%Z). { rewrite ES2. apply psum_nonneg. intros k Hk. unfold PV, QV. pose proof (MV (gs + k)%Z ltac:(lia)) as Hq. pose proof (proj2 (LPF NG6 _ 0%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 1%Z Hq ltac:(lia))). pose proof (proj2 (LPF NG6 _ 2%Z Hq ltac:(lia))). lia. }
      pose proof (COSTREL_le _ _ 6 nG (COSTREL_fast6 cost S0 S1 S2 HS0 HS1 HS2) ltac:(lia)) as CR.
      pose proof (COSTC_fast arr1 len lp nG nMTF gs cost FB) as CF. rewrite <- ES0, <- ES1, <- ES2 in CF. rewrite <- CF in CR. clear CF. fold ge in CR.
      set (cst := COSTC arr1 len lp nG gs ge cost) in *.
      pose proof (COSTC_0 arr1 len lp nG gs ge cost) as C0. fold cst in C0.
      (* [comment removed for export] *)
      lazymatch type of COST with u8arr _ _ _ (zb8 ?cbx 12) =>
        enter_with (S0_sm_btg cx e Q sp gp tp F fc CX SEP HNG cbx cst m2) end.
      all: gside.
      { st_eq. }
      intros bc bt ya6' EB Hbc Hbt.
      pose proof (sm_best_hit (Z.to_nat nG) cst 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BH. rewrite EB in BH. cbn [snd] in BH.
      (* [comment removed for export] *)
      enter_with (S0_sm_self cx e Q sp gp tp F fc CX SEP HNG bt nSel 1 fave sel m2 m2).
      all: gside.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      2:{ intros; exfalso; lia. }
      clear FAVE SEL C576 MI. intros m3 _ FAVE SEL C576 MI MU3 WM3.
      transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      enter_with (S0_fr cx e Q sp gp tp F fc rf gs bt bc nSel totc gs).
      all: gside.
      { st_eq. }
      { intros k Hk. unfold QV. apply MV. lia. }
      { apply RFR. lia. }
      clear AR1 RFQ MI. intros m4 rf4 za0 za1 AR1 RFQ ERF4 RFF4 MI MU4 WM4.
      transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
      (* [comment removed for export] *)
      assert (Hbc2 : (0 <= bc <= 65535)%Z).
      { destruct CR as [CBOK CREL]. pose proof (sm_best_fst_bound (Z.to_nat nG) cst 0 999999999 (-1) 65535 ltac:(lia) ltac:(lia)) as X.
        rewrite EB in X. cbn [fst] in X. apply X. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      rewrite ERF4 in RFQ. replace 50%nat with (Z.to_nat (ge - gs + 1)) in RFQ by lia.
      enter_with (S0_sm_tail cx e Q sp gp tp F fc CX SEP HM g (ge + 1)%Z bc totc nSel m4).
      all: gside.
      { st_eq. }
      all: intros Hc; eapply evt_eq; [| eapply (K m4 Jsp2 _ _)]; cbv zeta; fold ge; fold cst.
      all: try (rewrite EB; cbn [fst snd]).
      all: gside.
      { st_eq. replace (ge + 1 <? nMTF)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      { st_eq. replace (ge + 1 <? nMTF)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    - (* [comment removed for export] *)
      assert (FB : fastb nG nMTF gs = false).
      { unfold fastf in Hff. fold ge in Hff. unfold fastb. fold ge. destruct ((nG =? 6) && (ge - gs =? 49))%bool; [cbn in Hff; lia| reflexivity]. }
      pose proof (COSTREL_zero cost nG ltac:(lia)) as CR0.
      (* [comment removed for export] *)
      lstep; if_cases K0; zify_cond_z K0; [exfalso; lia|]. lstep.
      enter_with (S0_sm_csto cx e Q sp gp tp F fc CX SEP HA HNG HM ZB MV (Z.to_nat (ge - gs + 1)) gs ge znew (zero6 cost) len m1 m1).
      all: gside.
      { st_eq. }
      clear AR1 LEN COST MI. intros m2 cb2 ya1 ya2 ya3 ya4 AR1 LEN COST CR MI MU2 WM2.
      transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      pose proof (COSTC_slow arr1 len lp nG nMTF gs cost FB) as CS. fold ge in CS. rewrite <- CS in CR. clear CS.
      set (cst := COSTC arr1 len lp nG gs ge cost) in *.
      pose proof (COSTC_0 arr1 len lp nG gs ge cost) as C0. fold cst in C0.
      (* [comment removed for export] *)
      enter_with (S0_sm_btg cx e Q sp gp tp F fc CX SEP HNG cb2 cst m2).
      all: gside.
      { st_eq. }
      intros bc bt ya6' EB Hbc Hbt.
      pose proof (sm_best_hit (Z.to_nat nG) cst 0 999999999 (-1) ltac:(lia) ltac:(lia)) as BH. rewrite EB in BH. cbn [snd] in BH.
      (* [comment removed for export] *)
      enter_with (S0_sm_self cx e Q sp gp tp F fc CX SEP HNG bt nSel 0 fave sel m2 m2).
      all: gside.
      { st_eq. }
      { pose proof (FVB bt ltac:(lia)). lia. }
      { intros; exfalso; lia. }
      clear FAVE SEL C576 MI. intros m3 _ FAVE SEL C576 MI MU3 WM3.
      transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
      (* [comment removed for export] *)
      enter_with (S0_sm_rfsg cx e Q sp gp tp F fc sv w24 w56 iter CX SEP HA HNG HM ZB MV gs ge bt gs rf m3 m3).
      all: gside.
      { st_eq. }
      { apply RFR. lia. }
      clear AR1 RFQ S8 MI. intros m4 rf4 za0 za1 za2 za5 AR1 RFQ ERF4 RFF4 S8 MI MU4 WM4. unfold sm_slots3 in S8. cbv zeta in S8.
      transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
      (* [comment removed for export] *)
      assert (Hbc2 : (0 <= bc <= 65535)%Z).
      { destruct CR as [CBOK CREL]. pose proof (sm_best_fst_bound (Z.to_nat nG) cst 0 999999999 (-1) 65535 ltac:(lia) ltac:(lia)) as X.
        rewrite EB in X. cbn [fst] in X. apply X. intros t' Ht'. rewrite <- (CREL t' ltac:(lia)). pose proof (zbok_rd16 _ (2 * t') CBOK). lia. }
      rewrite ERF4 in RFQ. replace (ge + 1 - gs)%Z with (ge - gs + 1)%Z in RFQ by lia.
      enter_with (S0_sm_tail cx e Q sp gp tp F fc CX SEP HM g (ge + 1)%Z bc totc nSel m4).
      all: gside.
      { st_eq. }
      all: intros Hc; eapply evt_eq; [| eapply (K m4 Jsp x584 _)]; cbv zeta; fold ge; fold cst.
      all: try (rewrite EB; cbn [fst snd]).
      all: gside.
      { st_eq. replace (ge + 1 <? nMTF)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      { st_eq. replace (ge + 1 <? nMTF)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_gloop : forall (n j : nat) (s : sits) (jc Jsp : list byte) (x584 : word) (m me : word -> option byte)
      (ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6 : word),
    smB_grp e s -> it_len s = len -> it_lpk e s = lp ->
    (1 <= KSEL e <= 18002)%Z -> (50 * (KSEL e - 1) < nMTF <= 50 * KSEL e)%Z ->
    (Z.of_nat j + Z.of_nat n = KSEL e)%Z -> (1 <= n)%nat ->
    length jc = 12%nat -> length Jsp = 392%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (g_rfreq (Gj e s j)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (g_sel (Gj e s j)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    u8arr s0segs m (usp + 184) Jsp ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    u32arr s0segs m (usp + 616) (zw32 (g_fave (Gj e s j)) 6) ->
    u8arr s0segs m (usp + 888) jc ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    mem_inv s0segs m -> munch Wg me m -> wmono s0segs me m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (Jsp' : list byte) (x584' : word) (jc' : list byte) (ra' t1' t2' a1' a2' a3' a4' a5' a6' s6' t3' t4' t5' t6' : word),
      length jc' = 12%nat -> length Jsp' = 392%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      u8arr s0segs m' (usp + 184) Jsp' ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584'; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      u32arr s0segs m' (usp + 616) (zw32 (g_fave (Gend e s)) 6) ->
      u8arr s0segs m' (usp + 888) jc' ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      mem_inv s0segs m' -> munch Wg me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (GR ra' (Z_to_bv 64 nMTF) t1' t2' (Z_to_bv 64 nMTF) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (g_totc (Gend e s))) (Z_to_bv 64 (g_nSel (Gend e s))) s6' t3' t4' t5' t6')
                       F (Z_to_bv 64 0x17230) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 (g_gs (Gj e s j))) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (g_totc (Gj e s j))) (Z_to_bv 64 (g_nSel (Gj e s j))) s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x161b4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j s jc Jsp x584 m me ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6 HGF Elen Elp HK1 HK2 Hj Hn Ljc LJsp
           AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI MU WM CE SPB K.
    destruct HGF as [GF GEND].
    pose proof (GF j ltac:(lia)) as Fj. cbv zeta in Fj. cps_destruct Fj as (Egs & EnS & Htc & RFF & FVB & SLF).
    remember (Gj e s j) as gj eqn:EGJ.
    destruct gj as [rf sel cost fave nSel totc gs]. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in *.
    subst nSel. assert (Egs' : gs = (50 * Z.of_nat j)%Z) by (rewrite Egs; apply Z.min_l; lia).
    eapply (S0_sm_grp rf sel cost fave gs (Z.of_nat j) totc jc Jsp x584 m me);
      [lia| lia| lia| | | exact Ljc| exact LJsp| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2| exact MI| exact MU| exact WM| exact CE| exact SPB|].
    { intros t Ht v Hv. apply RFF; lia. }
    { intros t Ht. apply FVB. lia. }
    clear AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI MU WM.
    intros m' Jsp' x584' cb' ra' t1' t2' a0' a1' a2' a3' a5' a6' s6' t3' t4' t5' t6'. cbv zeta.
    intros LJsp' Hbt Hbc AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI MU WM.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    (* [comment removed for export] *)
    assert (EG' : Gj e s (S j) = sm_group_iter arr1 len lp nG nMTF (SGS rf sel cost fave (Z.of_nat j) totc gs)).
    { rewrite Gj_S, Elen, Elp, <- EGJ. reflexivity. }
    rewrite sm_group_iter_eq in EG'. cbv zeta in EG'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in EG'.
    destruct (Z.ltb_spec (GE nMTF gs + 1) nMTF) as [LT|GEQ].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) < KSEL e)%Z) by (destruct (Z.lt_ge_cases (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      pose proof (IH (S j) s (zb8 cb' 12) Jsp' x584' m' me) as IH'. rewrite EG' in IH'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in IH'.
      enter_with IH';
        [st_eq| split; [exact GF| exact GEND]| exact Elen| exact Elp| lia| lia| lia| lia| apply zb8_length_nat| exact LJsp'
        | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2| exact MI| exact MU| exact WM| exact CE| exact SPB| exact K].
    - (* [comment removed for export] *)
      assert (Hj1 : (Z.of_nat (S j) = KSEL e)%Z) by (destruct (Z.eq_dec (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; nia]).
      assert (EEND : Gend e s = Gj e s (S j)) by (unfold Gend; f_equal; lia).
      pose proof (K m' Jsp' x584' (zb8 cb' 12)) as K'. rewrite EEND, EG' in K'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in K'.
      enter_with K';
        [st_eq| apply zb8_length_nat| exact LJsp'| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2| exact MI| exact MU| exact WM].
  Qed.
End GG.

End ACeilS1.
