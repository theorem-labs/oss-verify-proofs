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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut AsanKit AsanCut AsanCutB0.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section ASG.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo : Z) (code0 len : zarr) (Jc Jl : list byte).
  Notation usp := (bv_unsigned sp).
  Hypothesis Hcb : (0 <= cb)%Z. Hypothesis HcbN : (cb + alphaSize <= NC)%Z.
  Hypothesis Hlb : (0 <= lb)%Z. Hypothesis HlbN : (lb + alphaSize <= NL)%Z.
  Hypothesis Hal : (0 <= alphaSize <= 258)%Z.
  Hypothesis Hmin : (1 <= minLen <= 32)%Z. Hypothesis Hmax : (0 <= maxLen <= 17)%Z.
  Hypothesis Hc4 : (Ecode mod 4 = 0)%Z. Hypothesis Hc0 : (0 < Ecode)%Z. Hypothesis HcC : (Ecode + 4 * NC <= CEIL)%Z.
  Hypothesis Hl0 : (0 < Elen)%Z. Hypothesis HlC : (Elen + NL <= CEIL)%Z.
  Hypothesis AP : apart Ecode (4 * NC) Elen NL.
  Hypothesis SPc : (usp <= Ecode \/ Ecode + 4 * NC <= usp - 32)%Z.
  Hypothesis SPl : (usp <= Elen \/ Elen + NL <= usp - 32)%Z.
  Hypothesis Hlo : (lo + 32 <= usp)%Z.
  Hypothesis LDEF : forall i, (0 <= i < alphaSize)%Z -> zdef len (lb + i) = true /\ (minLen <= zget len (lb + i) <= maxLen)%Z.
  (* [comment removed for export] *)
  Hypothesis Himg : (0x62b000 <= lo)%Z. Hypothesis HimgC : (0x62b000 <= Ecode)%Z. Hypothesis HimgL : (0x62b000 <= Elen)%Z.

  Definition W : list (Z * Z) := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (usp - 32, usp)]%Z.
  Hypothesis SHc : shzW b0segs W m0 Ecode (Ecode + 4 * NC).
  Hypothesis SHl : shzW b0segs W m0 Elen (Elen + NL).

  Notation POST := (hbAssignCodes_post b0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      Ecode (hbAssignCodes code0 len cb lb minLen maxLen alphaSize) Jc NC lo W m0).
  (* [comment removed for export] *)
  Definition MEMc (codec : zarr) (m : word -> option byte) : Prop :=
    u32arr b0segs m Ecode (ovw codec Jc NC) /\ u8arr b0segs m Elen (ovb len Jl NL) /\ mem_inv b0segs m /\
    munch W m0 m /\ wmono b0segs m0 m /\ stk b0segs m lo (usp + -32) /\ rw_cells b0segs m (usp + -32) [C8 s2; C8 s1; C8 s0; C8 ra].

  Notation cC := (Z_to_bv 64 (Ecode + 4 * cb)). Notation cL := (Z_to_bv 64 (Elen + lb)).
  Notation c1 := (Z_to_bv 64 1). Notation cSP := (Z_to_bv 64 (usp + -32)). Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Lemma asg_inner : forall (r : nat) (i vec n : Z) (codec : zarr) (m : word -> option byte) (x9 : word),
    (i + Z.of_nat r = alphaSize)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> (0 <= vec)%Z -> (vec + Z.of_nat r <= 2^27)%Z -> (minLen <= n <= maxLen)%Z ->
    MEMc codec m ->
    (forall codex vecx m' (x9' : word),
        (codex, vecx) = ha_inner r codec len cb lb n i vec -> (vec <= vecx <= vec + Z.of_nat r)%Z -> MEMc codex m' ->
        evt b0segs POST (MS (mkR ra cSP gp tp c1 cSB (Z_to_bv 64 alphaSize) (Z_to_bv 64 (Ecode + 4 * (cb + alphaSize))) x9' cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen)
                                  (Z_to_bv 64 alphaSize) (Z_to_bv 64 (Elen + lb + alphaSize)) (Z_to_bv 64 (Ecode + 4 * (cb + alphaSize))) (Z_to_bv 64 vecx)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c1 c1 (Z_to_bv 64 0) (Z_to_bv 64 (Elen + lb + alphaSize)))
                             F (Z_to_bv 64 0xa8e64) fc None m' (seg_rom b0segs))) ->
    evt b0segs POST (MS (mkR ra cSP gp tp c1 cSB (Z_to_bv 64 alphaSize) (Z_to_bv 64 (Ecode + 4 * (cb + i))) x9 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen)
                              (Z_to_bv 64 alphaSize) (Z_to_bv 64 (Elen + lb + i)) (Z_to_bv 64 (Ecode + 4 * (cb + i))) (Z_to_bv 64 vec)
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c1 c1 (Z_to_bv 64 (Z.of_nat r)) (Z_to_bv 64 (Elen + lb + i)))
                         F (Z_to_bv 64 0xa8dcc) fc None m (seg_rom b0segs)).
  Proof.
    induction r as [|r IH]; intros i vec n codec m x9 Hi Hi0 Hr Hv0 Hv1 Hn MEM K; [lia|].
    cps_destruct MEM as (COD & LEN & MI & MU & WM & ST & FR).
    pose proof (u32arr_bound b0segs m _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound b0segs m _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    pose proof (ovw_length (zset codec (cb + i) vec) Jc NC ltac:(lia)) as LC'. pose proof (ovb_length len Jl NL ltac:(lia)) as LL'.
    destruct (LDEF i ltac:(lia)) as [DEFi RNGi].
    bz_ceil; bz_params; unfold CEIL in *. pose proof AP as AP'. unfold apart in AP'. unfold W in MU, K, SHc, SHl |- *.
    (* [comment removed for export] *)
    wstep; notrap.
    (* [comment removed for export] *)
    wstep; flags. wstep. wstep; notrap.
    (* [comment removed for export] *)
    wstep; notrap.
    (* [comment removed for export] *)
    arun_to 0xa8df0%Z.
    pose proof (ovb_read1 b0segs m Elen len Jl NL (lb + i) _ LEN ltac:(lia) DEFi ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget len (lb + i))) by lia.
    cbn [ha_inner] in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - replace (zget len (lb + i) =? n)%Z with false in K by (symmetry; apply Z.eqb_neq; lia).
      wstep. wstep. wstep. wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z vec n codec m); [st_eq|lia|lia|lia|lia|lia|lia| |].
        { split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR]. }
        intros codex vecx m' x9' RES Hvx MEM'. apply (K codex vecx m'); [exact RES| lia| exact MEM'].
      + assert (r = 0)%nat by lia. subst r. cbn [ha_inner] in K.
        wstep.
        enter_with (K codec vec m); [st_eq| reflexivity| lia|].
        split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
    - replace (zget len (lb + i) =? n)%Z with true in K by (symmetry; apply Z.eqb_eq; lia).
      (* [comment removed for export] *)
      wstep; notrap. wstep; flags. wstep. wstep; notrap. wstep; notrap.
      (* [comment removed for export] *)
      arun_to 0xa8e20%Z.
      pose proof (u32arr_store_ok b0segs m Ecode _ (cb + i) _ COD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
      wstep.
      pose proof (ovw_write b0segs m Ecode codec Jc NC (cb + i) (Z_to_bv 64 vec) vec COD ltac:(lia) ltac:(rewrite unsigned_lit by lia; reflexivity)) as COD'.
      clear COD. store_done. rename COD' into COD.
      (* [comment removed for export] *)
      wstep; notrap. wstep.
      wstep. wstep. wstep. wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (vec + 1)%Z n (zset codec (cb + i) vec)); [st_eq|lia|lia|lia|lia|lia|lia| |].
        { split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR]. }
        intros codex vecx m' x9' RES Hvx MEM'. apply (K codex vecx m'); [exact RES| lia| exact MEM'].
      + assert (r = 0)%nat by lia. subst r. cbn [ha_inner] in K.
        wstep.
        enter_with (K (zset codec (cb + i) vec) (vec + 1)%Z); [st_eq| reflexivity| lia|].
        split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
  Qed.

  (* [comment removed for export] *)
  Lemma asg_outer : forall (k : nat) (n vec : Z) (codec : zarr) (m : word -> option byte) (x8 x9 x15 x16 x30 x31 : word),
    (n + Z.of_nat k = maxLen + 1)%Z -> (1 <= k)%nat -> (minLen <= n)%Z ->
    (0 <= vec <= VB (Z.to_nat (n - minLen)))%Z -> MEMc codec m ->
    fst (ha_outer k codec len cb lb alphaSize n vec) = hbAssignCodes code0 len cb lb minLen maxLen alphaSize ->
    evt b0segs POST (MS (mkR ra cSP gp tp c1 cSB (Z_to_bv 64 alphaSize) x8 x9 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                              x15 x16 (Z_to_bv 64 vec) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c1 c1 x30 x31)
                         F (Z_to_bv 64 0xa8db4) fc None m (seg_rom b0segs)).
  Proof.
    induction k as [|k IH]; intros n vec codec m x8 x9 x15 x16 x30 x31 Hk Hk1 Hn Hv MEM RES; [lia|].
    pose proof (VB_bound (Z.to_nat (n - minLen)) ltac:(lia)) as VBB.
    bz_ceil; bz_params; unfold CEIL in *. pose proof AP as AP'. unfold apart in AP'.
    cps_destruct MEM as (COD & LEN & MI & MU & WM & ST & FR). unfold W in MU.
    pose proof (u32arr_bound b0segs m _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound b0segs m _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    cbn [ha_outer] in RES.
    (* [comment removed for export] *)
    assert (TAIL : forall codex vecx m' (y8 y9 y15 y16 y30 y31 : word),
        (codex, vecx) = ha_inner (Z.to_nat alphaSize) codec len cb lb n 0 vec -> (vec <= vecx <= vec + alphaSize)%Z -> MEMc codex m' ->
        evt b0segs POST (MS (mkR ra cSP gp tp c1 cSB (Z_to_bv 64 alphaSize) y8 y9 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                                  y15 y16 (Z_to_bv 64 vecx) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c1 c1 y30 y31)
                             F (Z_to_bv 64 0xa8e64) fc None m' (seg_rom b0segs))).
    { intros codex vecx m' y8 y9 y15 y16 y30 y31 RESi Hvx MEM'.
      rewrite <- RESi in RES.
      cps_destruct MEM' as (COD' & LEN' & MI' & MU' & WM' & ST' & FR'). unfold W in MU'.
      clear COD LEN MI MU WM ST FR CB LB. rename m into mold. rename m' into m.
      (* [comment removed for export] *)
      wstep. wstep; notrap.
      (* [comment removed for export] *)
      wstep. wstep; notrap.
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      - (* [comment removed for export] *)
        enter_with (IH (n + 1)%Z (vecx * 2)%Z codex m); [st_eq| lia| lia| lia| | |].
        + replace (Z.to_nat (n + 1 - minLen)) with (S (Z.to_nat (n - minLen))) by lia. cbn [VB]. lia.
        + split; [exact COD'|]. split; [exact LEN'|]. split; [exact MI'|]. split; [unfold W; exact MU'|]. split; [exact WM'|]. split; [exact ST'| exact FR'].
        + rewrite <- RES. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
      - (* [comment removed for export] *)
        assert (k = 0)%nat by lia. subst k. cbn [ha_outer fst] in RES.
        wstep. wstep. wstep. wstep. wstep.
        rewrite <- RES. release_frame FR' ST' (bv_unsigned sp).
        replace (Z_to_bv 64 (usp + -32 + 32)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. unfold hbAssignCodes_post. finish. }
    wstep; if_cases Ka; zify_cond_z Ka.
    - (* [comment removed for export] *)
      replace (Z.to_nat alphaSize) with 0%nat in TAIL by lia. cbn [ha_inner] in TAIL.
      apply (TAIL codec vec m); [reflexivity| lia|].
      split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
    - wstep. wstep. wstep. wstep. wstep.
      enter_with (asg_inner (Z.to_nat alphaSize) 0 vec n codec m); [st_eq| lia| lia| lia| lia| lia| lia| |].
      + split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
      + intros codex vecx m' x9' RESi Hvx MEM'. enter_with (TAIL codex vecx m'); [st_eq| exact RESi| lia| exact MEM'].
  Qed.

  Lemma asg_entry : forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word),
    u32arr b0segs m0 Ecode (ovw code0 Jc NC) -> u8arr b0segs m0 Elen (ovb len Jl NL) -> mem_inv b0segs m0 ->
    stk b0segs m0 lo usp -> aconsts B0C m0 ->
    evt b0segs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 cC cL (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                              x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0xa8d70) fc None m0 (seg_rom b0segs)).
  Proof.
    intros until x31. intros COD LEN MI ST AC. bz_ceil; bz_params; unfold CEIL in *.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl b0segs m0) as WM. unfold W in MU.
    pose proof AP as AP'. unfold apart in AP'.
    pose proof (u32arr_bound b0segs m0 _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound b0segs m0 _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    pose proof (ovw_length code0 Jc NC ltac:(lia)) as LC'. pose proof (ovb_length len Jl NL ltac:(lia)) as LL'.
    carve_frame 32%nat ST.
    wstep. wstep. wstep. wstep. wstep.
    wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep. release_frame FR ST (bv_unsigned sp).
      replace (Z_to_bv 64 (usp + -32 + 32)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      wstep. unfold hbAssignCodes_post, hbAssignCodes. replace (Z.to_nat (maxLen - minLen + 1)) with 0%nat by lia. cbn [ha_outer fst]. finish.
    - (* [comment removed for export] *)
      wstep. wstep. wstep. wstep; flags. wstep. wstep. wstep. wstep. wstep; flagsb. wstep; flags. wstep; flags.
      rewrite (Z.div_mul alphaSize 4294967296) by lia.
      eapply (asg_outer (Z.to_nat (maxLen - minLen + 1)) minLen 0 code0); [lia| lia| lia| | | reflexivity].
      + replace (Z.to_nat (minLen - minLen)) with 0%nat by lia. cbn [VB]. lia.
      + split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
  Qed.
End ASG.

Theorem B0_hbAssignCodes : hbAssignCodes_aspecF B0C 32.
Proof.
  unfold hbAssignCodes_aspecF. cbn [aci_segs aci_hi aci_c ci_segs ci_hi ci_hbAssignCodes B0C]. intros. subst.
  eapply asg_entry; try eassumption; try lia.
Qed.

End ACeilS1.
