(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzArr BzCMem CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ACeilS1. Context {ACEIL__ : ACeil}.

Definition U0_makeMaps_d_pc : Z := 0x288c4%Z.

Definition makeMaps_d_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S lo : Z) (c0 c1 c2 k3 k4 k5 k6 : word) (inUse s2u : zarr) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [(S + 3192, S + 3196); (S + 3468, S + 3724)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ stk s0segs m' lo (bv_unsigned sp)
    /\ rw_cells s0segs m' (S + 3152)%Z [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 (Z_to_bv 64 (snd (BzDBlock.mkmaps 256 0 inUse s2u 0)))]
    /\ u8arr s0segs m' (S + 3196)%Z (zb8 inUse 256)
    /\ u8arr s0segs m' (S + 3468)%Z (zb8 (fst (BzDBlock.mkmaps 256 0 inUse s2u 0)) 256).

Section P.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (DS lo : Z) (c0 c1 c2 k3 k4 k5 k6 : word) (inUse s2u0 : zarr).
  Hypothesis AL8 : (DS mod 8 = 0)%Z.
  Hypothesis DS0 : (0 < DS)%Z.
  Hypothesis DSH : (DS + 64144 < 18446744073709551616)%Z.
  Hypothesis IUB : forall i, (0 <= i < 256)%Z -> (0 <= zget inUse i < 256)%Z.

  Definition W : list (Z * Z) := [(DS + 3192, DS + 3196); (DS + 3468, DS + 3724)]%Z.

  Notation POST := (makeMaps_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS lo c0 c1 c2 k3 k4 k5 k6 inUse s2u0 m0).

  Definition MEMc (n : Z) (s2u : zarr) (m : word -> option byte) : Prop :=
    rw_cells s0segs m (DS + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 (Z_to_bv 64 n)] /\
    u8arr s0segs m (DS + 3196) (zb8 inUse 256) /\ u8arr s0segs m (DS + 3468) (zb8 s2u 256) /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo (bv_unsigned sp).

  Notation ST i n x6 m :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 255) x6 t2 s0 s1
              (Z_to_bv 64 (DS + 2047)) (Z_to_bv 64 n) (Z_to_bv 64 i) (Z_to_bv 64 256) (Z_to_bv 64 (DS + 3196)) (Z_to_bv 64 (DS + 3468))
              (Z_to_bv 64 (18446744073709551615 - (DS + 3196))) (Z_to_bv 64 (18446744073709551615 - (DS + 3468)))
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x288f0) fc None m (seg_rom s0segs)).

  Lemma U0_mm_loop : forall (k : nat) (i n : Z) (s2u : zarr) (m : word -> option byte) (x6 : word),
    (i + Z.of_nat k = 256)%Z -> (1 <= k)%nat -> (0 <= i)%Z -> (0 <= n <= i)%Z ->
    MEMc n s2u m ->
    forall res : zarr * Z, BzDBlock.mkmaps k i inUse s2u n = res -> res = BzDBlock.mkmaps 256 0 inUse s2u0 0 ->
    evt s0segs POST (ST i n x6 m).
  Proof.
    induction k as [|k IH]; intros i n s2u m x6 Hik Hk Hi Hn MEM res RES REQ; [lia|].
    destruct MEM as (MID & IU & S2U & MI & MU & WM & STK).
    pose proof (u8arr_bound s0segs m _ _ IU) as IUBD. rewrite zb8_length_nat in IUBD.
    pose proof (u8arr_bound s0segs m _ _ S2U) as S2BD. rewrite zb8_length_nat in S2BD.
    pose proof (zb8_length inUse 256 ltac:(lia)) as LIU. pose proof (zb8_length s2u 256 ltac:(lia)) as LS2.
    pose proof (IUB i ltac:(lia)) as Bi.
    unfold W in MU.
    urun_to 0x288f8%Z.
    pose proof (zb8_read1 s0segs m (DS + 3196) inUse 256 i _ IU ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget inUse i)) by lia.
    cbn [BzDBlock.mkmaps] in RES.
    wstep. if_cases Kb; zify_cond_z Kb.
    - replace (zget inUse i =? 0)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in RES.
      urun_to 0x2891c%Z. wstep. if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z n s2u m); [st_eq | lia | lia | lia | lia | | exact RES | exact REQ].
        split; [exact MID|]. split; [exact IU|]. split; [exact S2U|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM| exact STK].
      + assert (k = 0)%nat by lia. subst k. cbn [BzDBlock.mkmaps] in RES.
        wstep. unfold makeMaps_d_post. rewrite <- REQ, <- RES. cbn [fst snd]. finish.
    - replace (zget inUse i =? 0)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in RES.
      urun_to 0x28910%Z.
      assert (SO : store_ok s0segs m (wa (DS + 3468 + n)) 1 = true)
        by (eapply (u8arr_storeN_ok s0segs m (DS + 3468) _ n 1 _ S2U); [lia| rewrite zb8_length_nat; lia| reflexivity]).
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
        pose proof (zb8_write1 s0segs mm (DS + 3468) s2u 256 n (Z_to_bv 64 i) S2U ltac:(lia)) as ARw; clear S2U;
        change bs with (le1 (Z_to_bv 64 i)); store_done; rename ARw into S2U end.
      rewrite (unsigned_lit i) in S2U by lia. unfold wr8 in S2U. rewrite (Z.mod_small i 256) in S2U by lia.
      urun_to 0x2891c%Z. wstep. if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (n + 1)%Z (zset s2u n i)); [st_eq | lia | lia | lia | lia | | exact RES | exact REQ].
        split; [eassumption|]. split; [eassumption|]. split; [exact S2U|]. split; [eassumption|]. split; [unfold W; eassumption|]. split; eassumption.
      + assert (k = 0)%nat by lia. subst k. cbn [BzDBlock.mkmaps] in RES.
        wstep. unfold makeMaps_d_post. rewrite <- REQ, <- RES. cbn [fst snd]. finish.
  Qed.

  Lemma U0_makeMaps_d_walk : forall (t0 t1 x11 x12 x13 x14 x15 x16 x17 n0 : word),
    rw_cells s0segs m0 (DS + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 n0] ->
    u8arr s0segs m0 (DS + 3196) (zb8 inUse 256) -> u8arr s0segs m0 (DS + 3468) (zb8 s2u0 256) ->
    mem_inv s0segs m0 -> stk s0segs m0 lo (bv_unsigned sp) ->
    evt s0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DS) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 U0_makeMaps_d_pc) fc None m0 (seg_rom s0segs)).
  Proof.
    intros until n0. intros MID IU S2U MI STK. unfold U0_makeMaps_d_pc.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl s0segs m0) as WM. unfold W in MU.
    pose proof (u8arr_bound s0segs m0 _ _ IU) as IUBD. rewrite zb8_length_nat in IUBD.
    pose proof (u8arr_bound s0segs m0 _ _ S2U) as S2BD. rewrite zb8_length_nat in S2BD.
    assert (LE7 : Z.land DS 7 = 0%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact AL8).
    wstep. rewrite LE7. wstep; notrap.
    urun_to 0x288f0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_mm_loop 256 0 0 s2u0 mm _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [st_eq | | reflexivity | reflexivity] end.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [unfold W; eassumption|]. split; eassumption.
  Qed.
End P.

Theorem makeMaps_d_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (DS lo : Z) (c0 c1 c2 k3 k4 k5 k6 n0 : word) (inUse s2u : zarr),
    a0 = Z_to_bv 64 DS ->
    rw_cells s0segs m (DS + 3152)%Z [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 n0] ->
    u8arr s0segs m (DS + 3196)%Z (zb8 inUse 256) -> u8arr s0segs m (DS + 3468)%Z (zb8 s2u 256) ->
    (forall i, 0 <= i < 256 -> 0 <= zget inUse i < 256)%Z ->
    mem_inv s0segs m -> stk s0segs m lo (bv_unsigned sp) ->
    (DS mod 8 = 0)%Z -> (0 < DS)%Z -> (DS + 64144 < 18446744073709551616)%Z ->
    (bv_unsigned sp <= DS \/ DS + 64144 <= bv_unsigned sp)%Z ->
    evt s0segs
      (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (ret_pc ra) fc None m' (seg_rom s0segs)
         /\ munch [(DS + 3192, DS + 3196); (DS + 3468, DS + 3724)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
         /\ stk s0segs m' lo (bv_unsigned sp)
         /\ rw_cells s0segs m' (DS + 3152)%Z [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 (Z_to_bv 64 (snd (BzDBlock.mkmaps 256 0 inUse s2u 0)))]
         /\ u8arr s0segs m' (DS + 3196)%Z (zb8 inUse 256)
         /\ u8arr s0segs m' (DS + 3468)%Z (zb8 (fst (BzDBlock.mkmaps 256 0 inUse s2u 0)) 256))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x288c4) fc None m (seg_rom s0segs)).
Proof.
  intros. subst.
  exact (U0_makeMaps_d_walk ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m DS lo c0 c1 c2 k3 k4 k5 k6 inUse s2u
           ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) t0 t1 a1 a2 a3 a4 a5 a6 a7 n0
           ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
Qed.

End ACeilS1.
