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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GB.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z. Hypothesis FVL : (0 < FV)%Z. Hypothesis FVH : (FV + 24 <= CEIL)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Hypothesis SEFV : id ((c_E cx + 55768 <= FV)%Z \/ (FV + 24 <= c_E cx)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.

  (* [comment removed for export] *)
  Notation GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 (E + 37708)) cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) (Z_to_bv 64 (E + 668)) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_bt : forall (n : nat) (t bc bt : Z) (cb cost : zarr) (m : word -> option byte)
      (ra t1 t2 a2 a3 a6 s2 s5 s6 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= bc <= 999999999)%Z -> (-1 <= bt < nG)%Z ->
    u8arr a0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    shpW a0segs [] m CO (CO + 12) ->
    (forall bc' bt' (t1 a3 : word), sm_best n cost t bc bt = (bc', bt') -> (0 <= bc' <= 999999999)%Z -> (-1 <= bt' < nG)%Z ->
      evt a0segs Q (MS (GA ra (Z_to_bv 64 bc') t1 t2 (Z_to_bv 64 (CO + 2 * nG)) (Z_to_bv 64 nG) (Z_to_bv 64 bc') a3 (Z_to_bv 64 0) (Z_to_bv 64 (CO + 2 * nG)) (Z_to_bv 64 bt') (Z_to_bv 64 bt')
                           s2 s5 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8cac0) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra (Z_to_bv 64 bc) t1 t2 (Z_to_bv 64 (CO + 2 * t)) (Z_to_bv 64 t) a2 a3 (Z_to_bv 64 (nG - t)) (Z_to_bv 64 (CO + 2 * t)) a6 (Z_to_bv 64 bt)
                         s2 s5 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ca64) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t bc bt cb cost m ra t1 t2 a2 a3 a6 s2 s5 s6 t3 t4 t5 t6 Ht Ht0 Hn Hbc Hbt COST [CBOK CREL] SHc K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    pose proof (munch_refl [] m) as MU.
    pose proof (zb8_length_nat cb 12) as LC.
    rewrite sm_best_S in K.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    (* [comment removed for export] *)
    arun_to 0x8ca6c%Z. ack_rd (CO + 2 * t)%Z 2%Z. ack_merge.
    (* [comment removed for export] *)
    pose proof (zb8_read2 a0segs m CO cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstep. clear RD. rewrite (zx16_lit (zget cost t)) by lia.
    (* [comment removed for export] *)
    lstep. lstep; if_cases K1; zify_cond_z K1.
    - (* [comment removed for export] *)
      lstep. lstep; if_cases K2; zify_cond_z K2; [exfalso; lia|]. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
      replace (zget cost t <? bc)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
      lstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (t + 1)%Z bc bt cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| exact SHc| exact K].
      + assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K. lstep.
        enter_with (K bc bt _ _); [st_eq| reflexivity| lia| lia].
    - (* [comment removed for export] *)
      lstep. lstep. lstep; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. lstep. lstep.
        replace (zget cost t <? bc)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
        lstep; if_cases Ke; zify_cond_z Ke.
        * enter_with (IH (t + 1)%Z (zget cost t) t cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| exact SHc| exact K].
        * assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K. lstep.
          enter_with (K (zget cost t) t _ _); [st_eq| reflexivity| lia| lia].
      + (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. lstep. lstep. lstep.
        replace (zget cost t <? bc)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
        lstep; if_cases Ke; zify_cond_z Ke.
        * enter_with (IH (t + 1)%Z bc bt cb cost m); [st_eq| lia| lia| lia| lia| lia| exact COST| split; [exact CBOK| exact CREL]| exact SHc| exact K].
        * assert (n = 0)%nat by lia. subst n. cbn [sm_best] in K. lstep.
          enter_with (K bc bt _ _); [st_eq| reflexivity| lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wc := [(CO, CO + 12)]%Z.
  Lemma A0_sm_csti : forall (n : nat) (t icv : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a2 a3 a7 s2 s5 s6 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= icv < A)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr a0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv a0segs m -> munch Wc mf m -> wmono a0segs mf m ->
    shzW a0segs Wc mf E (E + ESTATE_SIZE) -> shpW a0segs Wc mf CO (CO + 12) ->
    (forall m' cb' (t0 a3 a7 : word),
      u8arr a0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow_t n cost len icv t) nG ->
      mem_inv a0segs m' -> munch Wc mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * nG + icv)) (Z_to_bv 64 (CO + 2 * nG)) a2 a3 (Z_to_bv 64 (E + 37708 + 258 * nG + icv)) (Z_to_bv 64 0)
                           (Z_to_bv 64 (CO + 2 * nG)) a7 s2 s5 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8d934) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + icv)) (Z_to_bv 64 (CO + 2 * t)) a2 a3 (Z_to_bv 64 (E + 37708 + 258 * t + icv)) (Z_to_bv 64 (nG - t))
                         (Z_to_bv 64 (CO + 2 * t)) a7 s2 s5 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8d8cc) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t icv cb cost len m mf ra t0 t1 t2 a2 a3 a7 s2 s5 s6 t3 t4 t5 t6 Ht Ht0 Hn Hicv LF VLEN COST [CBOK CREL] MI MU WM SHe SHc K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe.
    pose proof (zb8_length_nat cb 12) as LC. pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    destruct (LF t icv ltac:(lia) ltac:(lia)) as [Dl Rl].
    rewrite sm_cost_slow_t_S in K.
    (* [comment removed for export] *)
    arun_to 0x8d8e4%Z. ack_rd (CO + 2 * t)%Z 2%Z.
    (* [comment removed for export] *)
    pose proof (VLEN m MU) as LEN.
    pose proof (ovb_read1 a0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + icv) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD LEN.
    ack_merge.
    (* [comment removed for export] *)
    pose proof (zb8_read2 a0segs m CO cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstep. clear RD.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. rewrite (unsigned_lit8 (zget len (258 * t + icv))) by lia.
    pose proof (u8arr_storeN_ok a0segs _ CO _ (2 * t) 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (CO + 2 * t)%Z. zb8_store2 COST (2 * t)%Z.
    pose proof (COSTREL_set cb cost nG t (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx16 (Z_to_bv 64 (zget cost t))) + zget len (258 * t + icv)))) (conj CBOK CREL) ltac:(lia)) as CR'.
    rewrite (cost_upd_mod (zget cost t) (zget len (258 * t + icv))) in CR' by lia.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z icv _ _ len _ mf); [st_eq| lia| lia| lia| lia| exact LF| exact VLEN| exact COST| exact CR'| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact SHc| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow_t] in K. lstep.
      enter_with (K _ _ _ _ _); [st_eq| exact COST| exact CR'| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_csto : forall (n : nat) (i ge : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (ra t0 a0 a1 a3 a4 a5 a6 a7 s2 s5 s6 t3 t5 t6 : word),
    (i + Z.of_nat n = ge + 1)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr a0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv a0segs m -> munch Wc mf m -> wmono a0segs mf m ->
    shzW a0segs Wc mf A1 (A1 + ARR1_SIZE) -> shzW a0segs Wc mf E (E + ESTATE_SIZE) -> shpW a0segs Wc mf CO (CO + 12) ->
    (forall m' cb' (t0 a0 a1 a3 a4 a5 a6 a7 : word),
      u8arr a0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow n cost len arr1 nG i) nG ->
      mem_inv a0segs m' -> munch Wc mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 CO) a0 a1 (Z_to_bv 64 (ge + 1)) a3 a4 a5 a6 a7 s2 s5 s6 t3 (Z_to_bv 64 (ge + 1)) t5 t6)
                       F (Z_to_bv 64 0x8ca4c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 CO) a0 a1 (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s5 s6 t3 (Z_to_bv 64 (ge + 1)) t5 t6)
                     F (Z_to_bv 64 0x8d89c) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i ge cb cost len m mf ra t0 a0 a1 a3 a4 a5 a6 a7 s2 s5 s6 t3 t5 t6 Hi Hi0 Hn Hge LF VAR1 VLEN COST CR MI MU WM SHa SHe SHc K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    pose proof (MV i ltac:(lia)) as MVi.
    rewrite sm_cost_slow_S in K.
    (* [comment removed for export] *)
    arun.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 a0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstep. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    enter_with (A0_sm_csti (Z.to_nat nG) 0 (mtfv_at arr1 i) cb cost len m m);
      [st_eq| lia| lia| lia| lia| exact LF| | exact COST| exact CR| exact MI| apply munch_refl| apply wmono_refl| | |].
    { apply (vw_sub _ Wc Wc mf m VLEN MU). a_sub_fp. }
    { eapply (shzW_sub a0segs Wc Wc mf m); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shpW_sub a0segs Wc Wc mf m); [exact SHc| exact MU| a_sub_fp| lia| lia]. }
    clear COST CR MI. intros m1 cb1 yt0 ya3 ya7 COST CR MI MU1 WM1.
    transport_after_call a0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ge cb1 _ len m1 mf); [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM| exact SHa| exact SHe| exact SHc| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow] in K. lstep.
      enter_with (K m1 cb1 _ _ _ _ _ _ _ _); [st_eq| exact COST| exact CR| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Lemma A0_sm_rfsl : forall (n : nat) (i bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a1 a2 a3 a7 s2 s5 s6 t4 t5 t6 : word),
    (0 <= i)%Z -> (1 <= n)%nat -> (i + Z.of_nat n <= nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + Z.of_nat n <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr a0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv a0segs m -> munch Wrf mf m -> wmono a0segs mf m ->
    shzW a0segs Wrf mf A1 (A1 + ARR1_SIZE) -> shzW a0segs Wrf mf E (E + ESTATE_SIZE) ->
    (forall m' rf' (a1 a3 a7 : word),
      u32arr a0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc n rf arr1 bt i -> RFrow rf' bt A (B + Z.of_nat n) ->
      mem_inv a0segs m' -> munch Wrf mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 (A1 + 2 * (i + Z.of_nat n))) a1 a2 a3 (Z_to_bv 64 (bt * 1032)) (Z_to_bv 64 (A1 + 2 * (i + Z.of_nat n))) (Z_to_bv 64 0) a7
                           s2 s5 s6 (Z_to_bv 64 (E + 45448)) t4 t5 t6)
                       F (Z_to_bv 64 0x8d870) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 (A1 + 2 * i)) a1 a2 a3 (Z_to_bv 64 (bt * 1032)) (Z_to_bv 64 (A1 + 2 * i)) (Z_to_bv 64 (Z.of_nat n)) a7
                         s2 s5 s6 (Z_to_bv 64 (E + 45448)) t4 t5 t6)
                     F (Z_to_bv 64 0x8d964) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i bt B rf m mf ra t0 t1 t2 a1 a2 a3 a7 s2 s5 s6 t4 t5 t6 Hi0 Hn Hend Hbt HB HBn VAR1 RFQ RFF MI MU WM SHa SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    pose proof (MV i ltac:(lia)) as MVi. destruct (RFF (mtfv_at arr1 i) MVi) as [Dr Rr].
    (* [comment removed for export] *)
    arun.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 a0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstep. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs m (E + 45448) rf (jseg J 45448 6192) 1548 (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(lia) Dr ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite (sx32_of_Z (zget rf (258 * bt + mtfv_at arr1 i))) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    lstep. wstep. lstep.
    pose proof (u32arr_store_ok a0segs m (E + 45448) _ (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (E + 45448 + 4 * (258 * bt + mtfv_at arr1 i))%Z.
    ovw_store RFQ (258 * bt + mtfv_at arr1 i)%Z (zget rf (258 * bt + mtfv_at arr1 i) + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset rf (258 * bt + mtfv_at arr1 i) (zget rf (258 * bt + mtfv_at arr1 i) + 1)) with (zincr rf (258 * bt + mtfv_at arr1 i)) in RFQ.
    pose proof (RFrow_incr rf bt A B (mtfv_at arr1 i) RFF MVi) as RFF'.
    rewrite sm_rfreq_inc_S in K.
    (* [comment removed for export] *)
    lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z bt (B + 1)%Z _ _ mf);
        [st_eq| lia| lia| lia| lia| lia| lia| exact VAR1| exact RFQ| exact RFF'| assumption| assumption| assumption| exact SHa| unfold ESTATE_SIZE; exact SHe|].
      intros m' rf' y1 y3 y7 RFQ' E' RFF2 MI' MU' WM'.
      enter_with (K m' rf' y1 y3 y7); [st_eq| exact RFQ'| exact E'| eapply RFrow_weaken; [exact RFF2| lia]| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_inc] in K. lstep.
      enter_with (K _ _ _ _ _); [st_eq| exact RFQ| reflexivity| eapply RFrow_weaken; [exact RFF'| lia]| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wself := [(E + 1704, E + 19706); (FV, FV + 24)]%Z.
  Lemma A0_sm_self : forall (bt nSel ff : Z) (fave sel : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s2 t3 t4 t5 t6 : word),
    (0 <= bt < nG)%Z -> (0 <= nSel < 18002)%Z -> (0 <= zget fave bt <= 18002)%Z -> (ff = 0 \/ ff = 1)%Z ->
    u32arr a0segs m FV (zw32 fave 6) ->
    u8arr a0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    mem_inv a0segs m -> munch Wself mf m -> wmono a0segs mf m ->
    shzW a0segs Wself mf FV (FV + 24) -> shzW a0segs Wself mf E (E + ESTATE_SIZE) ->
    frdW a0segs Wself mf (P + 1384) [C8 (Z_to_bv 64 FV)] -> frdW a0segs Wself mf (P + 1392) [C8 (Z_to_bv 64 (E + 1704))] ->
    (forall m' (a1 : word), ff = 1%Z ->
      u32arr a0segs m' FV (zw32 (zincr fave bt) 6) ->
      u8arr a0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      mem_inv a0segs m' -> munch Wself mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 1032) a1 a2 a3 (Z_to_bv 64 (bt * 1032)) a5 (Z_to_bv 64 bt) a7 s2 (Z_to_bv 64 nSel) (Z_to_bv 64 ff) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8cb10) fc None m' (seg_rom a0segs))) ->
    (forall m' (a1 : word), ff = 0%Z ->
      u32arr a0segs m' FV (zw32 (zincr fave bt) 6) ->
      u8arr a0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      mem_inv a0segs m' -> munch Wself mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 t1 t2 (Z_to_bv 64 1032) a1 a2 a3 (Z_to_bv 64 (bt * 1032)) a5 (Z_to_bv 64 bt) a7 s2 (Z_to_bv 64 nSel) (Z_to_bv 64 ff) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8d868) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 bt) a7 s2 (Z_to_bv 64 nSel) (Z_to_bv 64 ff) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8cac0) fc None m (seg_rom a0segs)).
  Proof.
    intros bt nSel ff fave sel m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s2 t3 t4 t5 t6 Hbt HnS Hfv Hff FAVE SEL MI MU WM SHf SHe V1384 V1392 KF KS.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe.
    pose proof (zw32_length_nat fave 6) as LFV. pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length sel (jseg J 1704 18002) 18002 ltac:(lia)) as LSL.
    (* [comment removed for export] *)
    lstep. pose proof (V1384 m MU) as RO. lstep. clear RO. lstep.
    replace (FV + bt * 4)%Z with (FV + 4 * bt)%Z by lia.
    arun.
    pose proof (zw32_read a0segs m FV fave 6 bt _ FAVE ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite (sx32_of_Z (zget fave bt)) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    lstep.
    pose proof (u32arr_store_ok a0segs _ FV _ bt _ FAVE ltac:(rewrite zw32_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2.
    lstep. store_addr (FV + 4 * bt)%Z. zw32_store FAVE bt (zget fave bt + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset fave bt (zget fave bt + 1)) with (zincr fave bt) in FAVE.
    (* [comment removed for export] *)
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V1392 mm MU') as RO end. lstep. clear RO.
    arun.
    pose proof (u8arr_store_ok a0segs _ (E + 1704) _ nSel _ SEL ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (E + 1704 + nSel)%Z. ovb_store1 SEL nSel.
    replace (wr8 sel nSel (bv_unsigned (Z_to_bv 64 bt))) with (zset sel nSel (bt mod 256)) in SEL by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Kf; zify_cond_z Kf.
    - enter_with (KS _ _ ltac:(lia)); [st_eq| exact FAVE| exact SEL| assumption| assumption| assumption].
    - enter_with (KF _ _ ltac:(lia)); [st_eq| exact FAVE| exact SEL| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_rfsg : forall (gs ge bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 t4 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + (ge + 1 - gs) <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr a0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv a0segs m -> munch Wrf mf m -> wmono a0segs mf m ->
    shzW a0segs Wrf mf A1 (A1 + ARR1_SIZE) -> shzW a0segs Wrf mf E (E + ESTATE_SIZE) ->
    (forall m' rf' (a0 a1 a3 a5 a6 a7 : word),
      u32arr a0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc (Z.to_nat (ge + 1 - gs)) rf arr1 bt gs -> RFrow rf' bt A (B + (ge + 1 - gs)) ->
      mem_inv a0segs m' -> munch Wrf mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (bt * 1032)) a5 a6 a7 (Z_to_bv 64 (ge - gs)) s5 (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 45448)) t4 (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                       F (Z_to_bv 64 0x8d870) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (bt * 1032)) a5 a6 a7 (Z_to_bv 64 (ge - gs)) s5 s6 (Z_to_bv 64 (E + 45448)) t4 (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                     F (Z_to_bv 64 0x8d868) fc None m (seg_rom a0segs)).
  Proof.
    intros gs ge bt B rf m mf ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s5 s6 t4 Hgs Hge Hbt HB HBn VAR1 RFQ RFF MI MU WM SHa SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    (* [comment removed for export] *)
    lstep. lstep; if_cases K0; zify_cond_z K0; [|exfalso; lia].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep.
    enter_with (A0_sm_rfsl (Z.to_nat (ge + 1 - gs)) gs bt B rf m m);
      [st_eq| lia| lia| lia| lia| lia| lia| | exact RFQ| exact RFF| exact MI| apply munch_refl| apply wmono_refl| | |].
    { apply (vw_sub _ Wrf Wrf mf m VAR1 MU). a_sub_fp. }
    { eapply (shzW_sub a0segs Wrf Wrf mf m); [exact SHa| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub a0segs Wrf Wrf mf m); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    clear RFQ RFF MI. intros m' rf' y1 y3 y7 RFQ E' RFF MI MU1 WM1.
    transport_after_call a0segs m m' MU1 WM1. clear MU1 WM1.
    enter_with (K m' rf' _ _ _ _ _ _); [st_eq| exact RFQ| exact E'| replace (B + (ge + 1 - gs))%Z with (B + Z.of_nat (Z.to_nat (ge + 1 - gs)))%Z by lia; exact RFF| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_csg : forall (gs ge : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (ra t0 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr a0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv a0segs m -> munch Wc mf m -> wmono a0segs mf m ->
    shzW a0segs Wc mf A1 (A1 + ARR1_SIZE) -> shzW a0segs Wc mf E (E + ESTATE_SIZE) -> shpW a0segs Wc mf CO (CO + 12) ->
    frdW a0segs Wc mf (P + 1376) [C8 (Z_to_bv 64 CO)] -> frdW a0segs Wc mf (P + 1400) [C8 (Z_to_bv 64 (E + 45448))] ->
    (forall m' cb' (t0 a0 a1 a2 a3 a4 a5 a6 a7 : word),
      u8arr a0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow (Z.to_nat (ge + 1 - gs)) cost len arr1 nG gs) nG ->
      mem_inv a0segs m' -> munch Wc mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 CO) a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                       F (Z_to_bv 64 0x8ca4c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                     F (Z_to_bv 64 0x8ca40) fc None m (seg_rom a0segs)).
  Proof.
    intros gs ge cb cost len m mf ra t0 t2 t3 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 Hgs Hge LF VAR1 VLEN COST CR MI MU WM SHa SHe SHc V1376 V1400 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    (* [comment removed for export] *)
    pose proof (V1376 m MU) as RO. lstep. clear RO. pose proof (V1400 m MU) as RO. lstep. clear RO.
    lstep; if_cases K0; zify_cond_z K0; [|exfalso; lia].
    lstep.
    enter_with (A0_sm_csto (Z.to_nat (ge + 1 - gs)) gs ge cb cost len m mf);
      [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM| exact SHa| exact SHe| exact SHc|].
    intros m' cb' y0 y1 y2 y3 y4 y5 y6 y7 COST' CR' MI' MU' WM'.
    enter_with (K m' cb' _ _ _ _ _ _ _ _ _); [st_eq| exact COST'| exact CR'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_btg : forall (cb cost : zarr) (m : word -> option byte)
      (ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 : word),
    u8arr a0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    shpW a0segs [] m CO (CO + 12) -> frdW a0segs [] m (P + 1352) [C8 (Z_to_bv 64 999999999)] ->
    (forall bc' bt' (t1 a3 : word), sm_best (Z.to_nat nG) cost 0 999999999 (-1) = (bc', bt') -> (0 <= bc' <= 999999999)%Z -> (-1 <= bt' < nG)%Z ->
      evt a0segs Q (MS (GA ra (Z_to_bv 64 bc') t1 (Z_to_bv 64 CO) (Z_to_bv 64 (CO + 2 * nG)) (Z_to_bv 64 nG) (Z_to_bv 64 bc') a3 (Z_to_bv 64 0) (Z_to_bv 64 (CO + 2 * nG)) (Z_to_bv 64 bt') (Z_to_bv 64 bt')
                           s2 s5 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8cac0) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 (Z_to_bv 64 CO) a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ca4c) fc None m (seg_rom a0segs)).
  Proof.
    intros cb cost m ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 COST CR SHc V1352 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    pose proof (V1352 m (munch_refl [] m)) as RO. lstep. clear RO.
    enter_with (A0_sm_bt (Z.to_nat nG) 0 999999999 (-1) cb cost m);
      [st_eq| lia| lia| lia| lia| lia| exact COST| exact CR| exact SHc| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fastf (gs : Z) : Z := if ((nG =? 6) && (GE nMTF gs - gs =? 49))%Z%bool then 1 else 0.
  Lemma A0_sm_head : forall (gs : Z) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z ->
    frdW a0segs [] m (P + 1432) [C8 (Z_to_bv 64 gs)] -> frdW a0segs [] m (P + 1368) [C8 (Z_to_bv 64 (flag6 nG))] ->
    frdW a0segs [] m (P + 1344) [C8 (Z_to_bv 64 (E + 37708))] ->
    (forall (a0 : word), let ge := GE nMTF gs in fastf gs = 1%Z ->
      evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) t2 a0 (Z_to_bv 64 (flag6 nG)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ge - gs)) s5 (Z_to_bv 64 (fastf gs)) t3 (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                       F (Z_to_bv 64 0x8ac68) fc None m (seg_rom a0segs))) ->
    (forall (a0 : word), let ge := GE nMTF gs in fastf gs = 0%Z ->
      evt a0segs Q (MS (GA ra t0 (Z_to_bv 64 (E + 37708)) t2 a0 (Z_to_bv 64 (flag6 nG)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ge - gs)) s5 (Z_to_bv 64 (fastf gs)) t3 (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 gs) (Z_to_bv 64 ge))
                       F (Z_to_bv 64 0x8ca40) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nMTF) s5 (Z_to_bv 64 (gs + 49)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac34) fc None m (seg_rom a0segs)).
  Proof.
    intros gs m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 Hgs V1432 V1368 V1344 KF KS.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    lstep.
    assert (GEd : forall ge, ge = GE nMTF gs -> forall (xt6 : word), xt6 = Z_to_bv 64 ge ->
      evt a0segs Q (MS (GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nMTF) s5 (Z_to_bv 64 (gs + 49)) t3 t4 t5 xt6)
                     F (Z_to_bv 64 0x8ac40) fc None m (seg_rom a0segs))).
    2:{ lstep; if_cases K1; zify_cond_z K1.
        - eapply (GEd (gs + 49)%Z); [unfold GE, BZ_G_SIZE; replace (nMTF <=? gs + 50 - 1)%Z with false by (symmetry; apply Z.leb_gt; lia); lia| reflexivity].
        - lstep. eapply (GEd (nMTF - 1)%Z); [unfold GE, BZ_G_SIZE; replace (nMTF <=? gs + 50 - 1)%Z with true by (symmetry; apply Z.leb_le; lia); lia| f_equal; lia]. }
    intros ge Ege xt6 ->.
    pose proof (GE_facts nMTF gs ltac:(lia)) as GF. rewrite <- Ege in GF. cps_destruct GF as (G1 & G2 & G3).
    (* [comment removed for export] *)
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    pose proof (V1432 m MU) as RO. lstep. clear RO.
    lstep. lstep. lstep. rewrite (seqz_mod64 (ge - gs + -49)) by lia.
    pose proof (V1368 m MU) as RO. lstep. clear RO. lstep. lstep.
    pose proof (V1344 m MU) as RO. lstep. clear RO.
    assert (FF : forall b, Z.land (flag6 nG) (Z.b2z b) = (if ((nG =? 6) && b)%bool then 1 else 0)%Z).
    { intros b. unfold flag6. destruct (nG =? 6)%Z, b; reflexivity. }
    lazymatch goal with |- context [Z.land (flag6 nG) (Z.b2z ?b)] =>
      rewrite (FF b); replace b with (ge - gs =? 49)%Z by (destruct (Z.eqb_spec (ge - gs) 49) as [EE|NE]; [symmetry; apply Z.eqb_eq; lia| symmetry; apply Z.eqb_neq; lia]) end.
    change (if ((nG =? 6) && (ge - gs =? 49))%bool then 1%Z else 0%Z) with (fastf gs) || (rewrite Ege; change (if ((nG =? 6) && (GE nMTF gs - gs =? 49))%bool then 1%Z else 0%Z) with (fastf gs); rewrite <- Ege).
    assert (Hff : (fastf gs = 0 \/ fastf gs = 1)%Z) by (unfold fastf; destruct (_ && _)%bool; lia).
    (* [comment removed for export] *)
    lstep; if_cases Kf; zify_cond_z Kf.
    - subst ge. enter_with (KF _ ltac:(lia)); [st_eq].
    - lstep. subst ge. enter_with (KS _ ltac:(lia)); [st_eq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wt := [(P + 1424, P + 1440)]%Z.
  Lemma A0_sm_tail : forall (g : eg) (gs ge1 bc totc nSel : Z) (w1360 : word) (m mf : word -> option byte)
      (ra t0 t1 a0 a1 a3 a4 a5 a6 a7 s2 t3 t5 t6 : word),
    g_mtf g = true -> (0 <= ge1 <= nMTF)%Z -> (0 <= bc < 4294967296)%Z -> (0 <= totc)%Z -> (totc + bc < 9223372036854775808)%Z -> (0 <= nSel < 18002)%Z ->
    rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    mem_inv a0segs m -> munch Wt mf m -> wmono a0segs mf m ->
    frdW a0segs Wt mf (E + 640) (EHEAD2 cx g e) -> shzW a0segs Wt mf E (E + ESTATE_SIZE) ->
    ((ge1 < nMTF)%Z -> forall m',
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360 (totc + bc) ge1) ->
      mem_inv a0segs m' -> munch Wt mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (GA (Z_to_bv 64 0x8ac34) t0 t1 (Z_to_bv 64 CO) (Z_to_bv 64 CO) (Z_to_bv 64 0) (Z_to_bv 64 12) a3 a4 a5 a6 a7
                           (Z_to_bv 64 nMTF) (Z_to_bv 64 (nSel + 1)) (Z_to_bv 64 (ge1 + 49)) t3 (Z_to_bv 64 ge1) t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    ((ge1 = nMTF)%Z ->
      evt a0segs Q (MS (GA ra t0 t1 (Z_to_bv 64 CO) (Z_to_bv 64 (totc + bc)) (Z_to_bv 64 ge1) (Z_to_bv 64 bc) a3 a4 a5 a6 a7
                           (Z_to_bv 64 nMTF) (Z_to_bv 64 (nSel + 1)) (Z_to_bv 64 (E + 668)) t3 (Z_to_bv 64 ge1) t5 t6)
                       F (Z_to_bv 64 0x8f16c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (GA ra t0 t1 (Z_to_bv 64 CO) a0 a1 (Z_to_bv 64 bc) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 nSel) (Z_to_bv 64 (E + 668)) t3 (Z_to_bv 64 ge1) t5 t6)
                     F (Z_to_bv 64 0x8d870) fc None m (seg_rom a0segs)).
  Proof.
    intros g gs ge1 bc totc nSel w1360 m mf ra t0 t1 a0 a1 a3 a4 a5 a6 a7 s2 t3 t5 t6 GM Hge Hbc Htc Htb HnS HI MI MU WM VEH2 SHe KL KE.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold sm_hi in HI. cbv zeta in HI.
    (* [comment removed for export] *)
    pose proof (VEH2 m MU) as EH2. unfold EHEAD2 in EH2. rewrite GM in EH2.
    arun_to 0x8d87c%Z. clear EH2. try rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      lstep. enter_with (KE ltac:(lia)); [st_eq].
    - (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. wstep. lstep. lstep. lstep. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KL ltac:(lia) mm) end;
        [st_eq| unfold sm_hi; cbv zeta; lazymatch type of HI with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact HI| CmpFast.rlf] end end| assumption| assumption| assumption].
  Qed.
End GB.
End ACeilS1.
