(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NatLit.
Module S0_indexIntoF.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.
Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Definition S0_indexIntoF_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (indx : Z) (CF : Z) (ws : list word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (index_into_f indx (sv32 ws))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [] m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ u32arr s0segs m' CF ws.

Section P.
  Variables (ra sp gp tp t2 s0 s1 x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (CF : Z) (ws : list word).
  Hypothesis ARR : u32arr s0segs m CF ws.
  Hypothesis LEN : length ws = 257%nat.
  Hypothesis MI : mem_inv s0segs m.
  Hypothesis CF0 : (0 < CF)%Z.
  Hypothesis AL4 : (CF mod 4 = 0)%Z.

  Notation indx := (bv_signed x).
  Notation POST := (S0_indexIntoF_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed x) CF ws m).
  Notation ST nb na t0 t1 a6 a7 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x (Z_to_bv 64 CF) (Z_to_bv 64 nb) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 na) a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x146d4) fc None m (seg_rom s0segs)).

  Lemma S0_iif_loop : forall (k : nat) (nb na : Z) (t0 t1 a6 a7 : word),
    (na - nb = 2 ^ (Z.of_nat k))%Z -> (1 <= k)%nat -> (0 <= nb)%Z -> (na <= 256)%Z ->
    munch [] m m -> wmono s0segs m m ->
    index_into_f indx (sv32 ws) = fst (iif_loop (sv32 ws) indx nb na k) ->
    evt s0segs POST (ST nb na t0 t1 a6 a7).
  Proof.
    induction k as [|k IH]; intros nb na t0 t1 a6 a7 HK Hk NB NA MU WM RES; [lia|].
    pose proof (u32arr_bound s0segs m CF ws ARR) as CFB. rewrite LEN in CFB.
    assert (P2 : (0 < 2 ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in HK by lia.
    wstep. wstep. wstep. notrap.
    wstep.
    set (mid := ((nb + na) / 2)%Z) in *.
    assert (HM : (mid = nb + 2 ^ Z.of_nat k)%Z) by (subst mid; mlia).
    destruct (nth_error_ok ws mid 257 LEN ltac:(lia)) as [w NTH].
    assert (AL4' : ((CF + 4 * mid) mod 4 = 0)%Z) by (clear - AL4; Z.div_mod_to_equations; lia).
    wstep. wstep. fstep. wstep. notrap.
    fstep. fstep. wstep. wstep. wstep. notrap.
    wstep. notrap.
    wstep. wstep. notrap.
    pose proof (u32arr_read s0segs m CF ws mid w _ ARR NTH ltac:(lia) eq_refl) as RD.
    wstep. clear RD.
    cbn [iif_loop] in RES. rewrite (zb_shiftr_div (nb + na) 1) in RES by lia. change (2^1)%Z with 2%Z in RES.
    fold mid in RES. rewrite (sv32_nth ws mid w NTH) in RES.
    pose proof (swrap32_range (bv_unsigned w)) as WR.
    wstep. wstep. if_cases K; zify_cond K; rewrite sx32_signed in K.
    - replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with false in RES by (symmetry; apply Z.leb_gt; lia).
      replace (mid - nb)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      wstep. if_cases K'; zify_cond K'; rewrite sx32_signed in K'; [| exfalso; lia].
      wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        apply (IH nb mid); try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. rewrite <- RES. unfold S0_indexIntoF_post. finish.
    - replace (bv_swrap 32 (bv_unsigned w) <=? indx)%Z with true in RES by (symmetry; apply Z.leb_le; lia).
      replace (na - mid)%Z with (2 ^ Z.of_nat k)%Z in RES by lia.
      wstep. wstep. if_cases K'; zify_cond K'; rewrite sx32_signed in K'; [exfalso; lia|]. wstep.
      wstep. wstep. wstep. notrap.
      wstep. wstep. wstep. if_cases K2; zify_cond K2.
      + replace (2 ^ Z.of_nat k =? 1)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia).
        apply (IH mid na); try assumption; try lia. destruct k; [cbn in K2; lia| lia].
      + replace (2 ^ Z.of_nat k =? 1)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia).
        cbn [fst] in RES. wstep. wstep. rewrite <- RES. unfold S0_indexIntoF_post. finish.
  Qed.

  Lemma S0_indexIntoF_walk : forall t0 t1 x11 x12 x13 x14 x15 x16 x17,
    x11 = Z_to_bv 64 CF ->
    evt s0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146c4) fc None m (seg_rom s0segs)).
  Proof.
    intros until x17. intros ->.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    pose proof (u32arr_bound s0segs m CF ws ARR) as CFB. rewrite LEN in CFB.
    wstep. wstep. fstep. wstep.
    apply (S0_iif_loop 8); try assumption; try reflexivity; lia.
  Qed.
End P.

Lemma S0_indexIntoF_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (CF : Z) (ws : list word),
  u32arr s0segs m CF ws -> length ws = 257%nat -> mem_inv s0segs m ->
  (0 < CF)%Z -> (CF mod 4 = 0)%Z ->
  a1 = Z_to_bv 64 CF ->
  evt s0segs (S0_indexIntoF_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_signed a0) CF ws m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146c4) fc None m (seg_rom s0segs)).
Proof. intros. eapply S0_indexIntoF_walk; eassumption. Qed.

End ACeilS1.
End S0_indexIntoF.
