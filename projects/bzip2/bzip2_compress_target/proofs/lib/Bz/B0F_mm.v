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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTac2 BzArr BzCMem CmpMem CmpCut AsanKit AsanCut AsanCutB0 AsanKitB0 B0F_leafCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
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
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (DS lo : Z) (c0 c1 c2 k3 k4 k5 k6 : word) (inUse s2u0 : zarr).
  Notation usp := (bv_unsigned sp).
  Hypothesis Hlo : (lo + 16 <= usp)%Z.
  Hypothesis SPc : (usp <= DS \/ DS + 64144 <= usp - 16)%Z.
  Hypothesis AL8 : (DS mod 8 = 0)%Z. Hypothesis DS0 : (0 < DS)%Z. Hypothesis DSH : (DS + 64144 <= 18446744073709551616)%Z.
  Hypothesis IUB : forall i, (0 <= i < 256)%Z -> (0 <= zget inUse i < 256)%Z.
  Hypothesis Himg : (0x62b000 <= lo)%Z. Hypothesis HimgC : (0x62b000 <= DS)%Z.
  Variable SHS : Z. Hypothesis AX : sanchor DS SHS.

  Definition W : list (Z * Z) := [(DS + 3192, DS + 3196); (DS + 3468, DS + 3724); (usp - 16, usp)]%Z.
  Hypothesis SHd : shzW b0segs W m0 DS (DS + 64144).

  Notation POST := (makeMaps_d_apostF 16 b0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS c0 c1 c2 k3 k4 k5 k6 inUse s2u0 lo m0).
  Notation cSP := (Z_to_bv 64 (usp + -16)). Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Definition MEMc (n : Z) (s2u : zarr) (jf : list byte) (m : word -> option byte) : Prop :=
    rw_cells b0segs m (DS + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 (Z_to_bv 64 n)] /\
    u8arr b0segs m (DS + 3196) (zb8 inUse 256) /\ u8arr b0segs m (DS + 3468) (zb8 s2u 256) /\
    mem_inv b0segs m /\ munch W m0 m /\ wmono b0segs m0 m /\
    stk b0segs m lo (usp + -16) /\ rw_cells b0segs m (usp + -16) [CB 8 jf; C8 ra].

  (* [comment removed for export] *)
  Notation ST pc i x5 x11 x29 x30 x31 m :=
    (MS (mkR ra cSP gp tp x5 (Z_to_bv 64 (18446744073709551615 - (DS + 3196))) (Z_to_bv 64 (18446744073709551615 - (DS + 3468))) s0 s1
              (Z_to_bv 64 (DS + 3192)) x11 cSB (Z_to_bv 64 (SHS + 399)) (Z_to_bv 64 i) (Z_to_bv 64 (DS + 3196)) (Z_to_bv 64 (DS + 3468)) (Z_to_bv 64 256)
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 255) x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0_mm_loop : forall (k : nat) (i n : Z) (s2u : zarr) (jf : list byte) (m : word -> option byte) (x5 x11 x29 x30 x31 : word),
    (i + Z.of_nat k = 256)%Z -> (1 <= k)%nat -> (0 <= i)%Z -> (0 <= n <= i)%Z ->
    MEMc n s2u jf m ->
    forall res : zarr * Z, BzDBlock.mkmaps k i inUse s2u n = res -> res = BzDBlock.mkmaps 256 0 inUse s2u0 0 ->
    evt b0segs POST (ST 0xb5c34 i x5 x11 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros i n s2u jf m x5 x11 x29 x30 x31 Hik Hk Hi Hn MEM res RES REQ; [lia|].
    destruct MEM as (MID & IU & S2U & MI & MU & WM & STK & FR).
    pose proof (u8arr_bound b0segs m _ _ IU) as IUBD. rewrite zb8_length_nat in IUBD.
    pose proof (u8arr_bound b0segs m _ _ S2U) as S2BD. rewrite zb8_length_nat in S2BD.
    pose proof (zb8_length inUse 256 ltac:(lia)) as LIU. pose proof (zb8_length s2u 256 ltac:(lia)) as LS2.
    pose proof (IUB i ltac:(lia)) as Bi.
    unfold W in MU, SHd.
    (* [comment removed for export] *)
    brun_to 0xb5c4c%Z.
    pose proof (zb8_read1 b0segs m (DS + 3196) inUse 256 i _ IU ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget inUse i)) by lia.
    cbn [BzDBlock.mkmaps] in RES.
    (* [comment removed for export] *)
    wstep. if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      replace (zget inUse i =? 0)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in RES.
      (* [comment removed for export] *)
      brun. if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z n s2u jf m); [st_eq| lia| lia| lia| lia| | exact RES| exact REQ].
        split; [exact MID|]. split; [exact IU|]. split; [exact S2U|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact STK| exact FR].
      + assert (k = 0)%nat by lia. subst k. cbn [BzDBlock.mkmaps] in RES.
        (* [comment removed for export] *)
        wstep. wstep. wstep. release_frame FR STK (bv_unsigned sp).
        replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. unfold makeMaps_d_apostF. rewrite <- REQ, <- RES. cbn [fst snd]. finish.
    - (* [comment removed for export] *)
      replace (zget inUse i =? 0)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in RES.
      (* [comment removed for export] *)
      brun_to 0xb5c7c%Z.
      assert (SO : store_ok b0segs m (wa (DS + 3468 + n)) 1 = true)
        by (eapply (u8arr_storeN_ok b0segs m (DS + 3468) _ n 1 _ S2U); [lia| rewrite zb8_length_nat; lia| reflexivity]).
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
        pose proof (zb8_write1 b0segs mm (DS + 3468) s2u 256 n (Z_to_bv 64 i) S2U ltac:(lia)) as ARw; clear S2U;
        change bs with (le1 (Z_to_bv 64 i)); store_done; rename ARw into S2U end.
      rewrite (unsigned_lit i) in S2U by lia. unfold wr8 in S2U. rewrite (Z.mod_small i 256) in S2U by lia.
      (* [comment removed for export] *)
      brun. if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (n + 1)%Z (zset s2u n i) jf); [st_eq| lia| lia| lia| lia| | exact RES| exact REQ].
        split; [eassumption|]. split; [eassumption|]. split; [exact S2U|]. split; [eassumption|]. split; [unfold W; eassumption|]. split; [eassumption|]. split; eassumption.
      + assert (k = 0)%nat by lia. subst k. cbn [BzDBlock.mkmaps] in RES.
        wstep. wstep. wstep.
        lazymatch goal with FRx : rw_cells _ _ (usp + -16)%Z _, STx : stk _ _ _ _ |- _ => release_frame FRx STx (bv_unsigned sp) end.
        replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. unfold makeMaps_d_apostF. rewrite <- REQ, <- RES. cbn [fst snd]. finish.
  Qed.

  Lemma B0_makeMaps_d_walk : forall t0 t1 t2 x11 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 (n0 : word),
    rw_cells b0segs m0 (DS + 3152) [C8 c0; C8 c1; C8 c2; C4 k3; C4 k4; C4 k5; C4 k6; C4 n0] ->
    u8arr b0segs m0 (DS + 3196) (zb8 inUse 256) -> u8arr b0segs m0 (DS + 3468) (zb8 s2u0 256) ->
    mem_inv b0segs m0 -> stk b0segs m0 lo usp -> aconsts B0C m0 ->
    evt b0segs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DS) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb5bd8) fc None m0 (seg_rom b0segs)).
  Proof.
    intros until n0. intros MID IU S2U MI STK AC.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl b0segs m0) as WM. unfold W in MU, SHd.
    pose proof (u8arr_bound b0segs m0 _ _ IU) as IUBD. rewrite zb8_length_nat in IUBD.
    pose proof (u8arr_bound b0segs m0 _ _ S2U) as S2BD. rewrite zb8_length_nat in S2BD.
    pose proof (zb8_length inUse 256 ltac:(lia)) as LIU. pose proof (zb8_length s2u0 256 ltac:(lia)) as LS2.
    carve_frame 16%nat STK.
    (* [comment removed for export] *)
    brun_to 0xb5c34%Z. sh_norm.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_mm_loop 256 0 0 s2u0 _ mm _ _ _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); [st_eq| | reflexivity | reflexivity] end.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [unfold W; eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.
End P.

Theorem B0_makeMaps_d : makeMaps_d_aspecF B0C B0_makeMaps_d_pc B0_FR_makeMaps_d.
Proof.
  unfold makeMaps_d_aspecF, B0_FR_makeMaps_d. cbn [aci_segs aci_hi aci_c ci_segs ci_hi B0C]. intros. subst.
  eapply (B0_makeMaps_d_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DS lo c0 c1 c2 k3 k4 k5 k6 inUse s2u
            ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(lia) _ (sanchor_intro DS ltac:(assumption)));
    try eassumption.
Qed.

End ACeilS1.
