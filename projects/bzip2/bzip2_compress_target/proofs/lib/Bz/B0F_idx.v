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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTac2 CmpCut AsanKit AsanCut AsanCutB0 AsanKitB0 B0F_leafCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section P.
  Variables (ra sp gp tp s0 s1 x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (CF lo : Z) (ws : list word).
  Notation usp := (bv_unsigned sp).
  Hypothesis LEN : length ws = 257%nat.
  Hypothesis Hlo : (lo + 16 <= usp)%Z.
  Hypothesis SPc : (usp <= CF \/ CF + 1028 <= usp - 16)%Z.
  Hypothesis AL4 : (CF mod 4 = 0)%Z.
  Hypothesis Himg : (0x62b000 <= lo)%Z. Hypothesis HimgC : (0x62b000 <= CF)%Z.

  Definition W : list (Z * Z) := [(usp - 16, usp)]%Z.
  Hypothesis SHc : shzW b0segs W m0 CF (CF + 1028).

  Notation indx := (bv_signed x).
  Notation POST := (indexIntoF_apostF 16 b0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed x) CF ws lo m0).
  Notation cSP := (Z_to_bv 64 (usp + -16)). Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Definition MEMc (jf : list byte) (m : word -> option byte) : Prop :=
    u32arr b0segs m CF ws /\ mem_inv b0segs m /\ munch W m0 m /\ wmono b0segs m0 m /\
    stk b0segs m lo (usp + -16) /\ rw_cells b0segs m (usp + -16) [CB 8 jf; C8 ra].

  (* [comment removed for export] *)
  Notation ST pc nb na t0 t1 t2 a3 t3 t4 t5 t6 m :=
    (MS (mkR ra cSP gp tp t0 t1 t2 s0 s1 x (Z_to_bv 64 CF) (Z_to_bv 64 nb) a3 cSB (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 na)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0_iif_loop : forall (k : nat) (nb na : Z) (jf : list byte) (m : word -> option byte) (t0 t1 t2 a3 t3 t4 t5 t6 : word),
    (na - nb = 2 ^ (Z.of_nat k))%Z -> (1 <= k)%nat -> (0 <= nb)%Z -> (na <= 256)%Z ->
    MEMc jf m ->
    index_into_f indx (sv32 ws) = fst (iif_loop (sv32 ws) indx nb na k) ->
    evt b0segs POST (ST 0x83e04 nb na t0 t1 t2 a3 t3 t4 t5 t6 m).
  Proof.
    induction k as [|k IH]; intros nb na jf m t0 t1 t2 a3 t3 t4 t5 t6 HK Hk NB NA MEM RES; [lia|].
    pose proof MEM as MEM'. destruct MEM' as (ARR & MI & MU & WM & STK & FR).
    pose proof (u32arr_bound b0segs m CF ws ARR) as CFB. rewrite LEN in CFB.
    assert (P2 : (0 < 2 ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in HK by lia.
    unfold W in MU, SHc.
    set (mid := ((nb + na) / 2)%Z) in *.
    assert (HM : (mid = nb + 2 ^ Z.of_nat k)%Z) by (subst mid; mlia).
    destruct (nth_error_ok ws mid 257 LEN ltac:(lia)) as [w NTH].
    assert (AL4' : ((CF + 4 * mid) mod 4 = 0)%Z) by (clear - AL4; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    brun_to 0x83e54%Z.
    pose proof (u32arr_read b0segs m CF ws mid w _ ARR NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    (* [comment removed for export] *)
    cbn [iif_loop] in RES. rewrite (zb_shiftr_div (nb + na) 1) in RES by lia. change (2^1)%Z with 2%Z in RES.
    fold mid in RES. rewrite (sv32_nth ws mid w NTH) in RES.
    pose proof (swrap32_range (bv_unsigned w)) as WR.
    (* [comment removed for export] *)
    wstep. wstep. if_cases K; zify_cond K; rewrite sx32_signed in K.
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with false in RES by (symmetry; apply Z.leb_gt; lia).
      replace (mid - nb)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      (* [comment removed for export] *)
      wstep. if_cases K'; zify_cond K'; rewrite sx32_signed in K'; [| exfalso; lia].
      (* [comment removed for export] *)
      brun. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        enter_with (IH nb mid jf m); [st_eq| ..]; try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. wstep. wstep. release_frame FR STK (bv_unsigned sp).
        replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. rewrite <- RES. unfold indexIntoF_apostF. finish.
    - (* [comment removed for export] *)
      replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with true in RES by (symmetry; apply Z.leb_le; lia).
      replace (na - mid)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      (* [comment removed for export] *)
      wstep. wstep. if_cases K'; zify_cond K'; rewrite sx32_signed in K'; [exfalso; lia|].
      brun. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        enter_with (IH mid na jf m); [st_eq| ..]; try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. wstep. wstep. release_frame FR STK (bv_unsigned sp).
        replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. unfold mid in RES. rewrite <- RES. unfold indexIntoF_apostF. finish.
  Qed.

  Lemma B0_indexIntoF_walk : forall t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6,
    x11 = Z_to_bv 64 CF ->
    u32arr b0segs m0 CF ws -> mem_inv b0segs m0 -> stk b0segs m0 lo usp -> aconsts B0C m0 ->
    evt b0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x83de0) fc None m0 (seg_rom b0segs)).
  Proof.
    intros until t6. intros -> ARR MI STK AC.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl b0segs m0) as WM. unfold W in MU.
    pose proof (u32arr_bound b0segs m0 CF ws ARR) as CFB. rewrite LEN in CFB.
    carve_frame 16%nat STK.
    (* [comment removed for export] *)
    brun_to 0x83e04%Z.
    eapply (B0_iif_loop 8 0 256 _ _); try reflexivity; try lia.
    split; [exact ARR|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact STK| exact FR].
  Qed.
End P.

Theorem B0_indexIntoF : indexIntoF_aspecF B0C B0_indexIntoF_pc B0_FR_indexIntoF.
Proof.
  unfold indexIntoF_aspecF, B0_FR_indexIntoF. cbn [aci_segs aci_hi aci_c ci_segs ci_hi B0C]. intros. subst.
  eapply B0_indexIntoF_walk; try eassumption; try lia; reflexivity.
Qed.

End ACeilS1.
