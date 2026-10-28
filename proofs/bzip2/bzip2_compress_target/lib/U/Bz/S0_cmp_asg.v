(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCHuff BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Ltac zres :=
  repeat (match goal with
          | |- context [?a <? ?b] => first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ]
          | |- context [?a =? ?b] => first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia) ]
          end); cbn [Z.b2z]; try reflexivity.

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
  Hypothesis SPc : (usp <= Ecode \/ Ecode + 4 * NC <= usp - 16)%Z.
  Hypothesis SPl : (usp <= Elen \/ Elen + NL <= usp - 16)%Z.
  Hypothesis Hlo : (lo + 16 <= usp)%Z.
  Hypothesis LDEF : forall i, (0 <= i < alphaSize)%Z -> zdef len (lb + i) = true /\ (minLen <= zget len (lb + i) <= maxLen)%Z.

  Definition W : list (Z * Z) := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (usp - 16, usp)]%Z.
  Notation POST := (hbAssignCodes_post s0segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                      Ecode (hbAssignCodes code0 len cb lb minLen maxLen alphaSize) Jc NC lo W m0).
  (* [comment removed for export] *)
  Definition MEMc (j8 : word) (codec : zarr) (m : word -> option byte) : Prop :=
    u32arr s0segs m Ecode (ovw codec Jc NC) /\ u8arr s0segs m Elen (ovb len Jl NL) /\ mem_inv s0segs m /\
    munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo (usp + -16) /\ rw_cells s0segs m (usp + -16) [C8 j8; C8 s0].

  Notation cC := (Z_to_bv 64 (Ecode + 4 * cb)). Notation cL := (Z_to_bv 64 (Elen + lb)).
  Notation c1 := (Z_to_bv 64 1). Notation cSP := (Z_to_bv 64 (usp + -16)).

  (* [comment removed for export] *)
  Lemma asg_inner : forall (r : nat) (i vec n : Z) (j8 : word) (codec : zarr) (m : word -> option byte) (x8 : word),
    (i + Z.of_nat r = alphaSize)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> (0 <= vec)%Z -> (vec + Z.of_nat r <= 2^27)%Z -> (minLen <= n <= maxLen)%Z ->
    MEMc j8 codec m ->
    (forall codex vecx m' (x8' : word),
        (codex, vecx) = ha_inner r codec len cb lb n i vec -> (vec <= vecx <= vec + Z.of_nat r)%Z -> MEMc j8 codex m' ->
        evt s0segs POST (MS (mkR ra cSP gp tp c1 c1 (Z_to_bv 64 0) x8' s1 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen)
                                  (Z_to_bv 64 alphaSize) (Z_to_bv 64 vecx) c1 (Z_to_bv 64 alphaSize)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Elen + lb + alphaSize)) (Z_to_bv 64 (Ecode + 4 * (cb + alphaSize)))
                                  (Z_to_bv 64 (Elen + lb + alphaSize)) (Z_to_bv 64 (Ecode + 4 * (cb + alphaSize))))
                             F (Z_to_bv 64 0x242a8) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra cSP gp tp c1 c1 (Z_to_bv 64 (Z.of_nat r)) x8 s1 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen)
                              (Z_to_bv 64 alphaSize) (Z_to_bv 64 vec) c1 (Z_to_bv 64 alphaSize)
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Elen + lb + i)) (Z_to_bv 64 (Ecode + 4 * (cb + i)))
                              (Z_to_bv 64 (Elen + lb + i)) (Z_to_bv 64 (Ecode + 4 * (cb + i))))
                         F (Z_to_bv 64 0x24250) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]; intros i vec n j8 codec m x8 Hi Hi0 Hr Hv0 Hv1 Hn MEM K; [lia|].
    cps_destruct MEM as (COD & LEN & MI & MU & WM & ST & FR).
    pose proof (u32arr_bound s0segs m _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound s0segs m _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    pose proof (ovw_length (zset codec (cb + i) vec) Jc NC ltac:(lia)) as LC'. pose proof (ovb_length len Jl NL ltac:(lia)) as LL'.
    destruct (LDEF i ltac:(lia)) as [DEFi RNGi].
    (* [comment removed for export] *)
    bz_ceil; bz_params; unfold CEIL in *. pose proof AP as AP'. unfold apart in AP'. unfold W in MU, K |- *.
    wstep; notrap.
    wstep; flags. wstep. wstep; notrap.
    wstep; notrap.
    pose proof (ovb_read1 s0segs m Elen len Jl NL (lb + i) _ LEN ltac:(lia) DEFi ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget len (lb + i))) by lia.
    cbn [ha_inner] in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (zget len (lb + i) =? n)%Z with false in K by (symmetry; apply Z.eqb_neq; lia).
      wstep. wstep. wstep. wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + (* [comment removed for export] *)
        enter_with (IH (i + 1)%Z vec n j8 codec m); [st_eq|lia|lia|lia|lia|lia|lia| |].
        { split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR]. }
        intros codex vecx m' x8' RES Hvx MEM'. apply (K codex vecx m'); [exact RES| lia| exact MEM'].
      + (* [comment removed for export] *)
        assert (r = 0)%nat by lia. subst r. cbn [ha_inner] in K.
        enter_with (K codec vec m); [st_eq| reflexivity| lia|].
        split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
    - (* [comment removed for export] *)
      replace (zget len (lb + i) =? n)%Z with true in K by (symmetry; apply Z.eqb_eq; lia).
      wstep; notrap. wstep; flags. wstep. wstep; notrap. wstep; notrap.
      wstep.
      pose proof (u32arr_store_ok s0segs m Ecode _ (cb + i) _ COD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
      wstep.
      pose proof (ovw_write s0segs m Ecode codec Jc NC (cb + i) (Z_to_bv 64 vec) vec COD ltac:(lia) ltac:(rewrite unsigned_lit by lia; reflexivity)) as COD'.
      clear COD. store_done. rename COD' into COD.
      wstep; notrap. wstep. (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      + enter_with (IH (i + 1)%Z (vec + 1)%Z n j8 (zset codec (cb + i) vec)); [st_eq|lia|lia|lia|lia|lia|lia| |].
        { split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR]. }
        intros codex vecx m' x8' RES Hvx MEM'. apply (K codex vecx m'); [exact RES| lia| exact MEM'].
      + assert (r = 0)%nat by lia. subst r. cbn [ha_inner] in K.
        enter_with (K (zset codec (cb + i) vec) (vec + 1)%Z); [st_eq| reflexivity| lia|].
        split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
  Qed.

  (* [comment removed for export] *)
  Lemma asg_outer : forall (k : nat) (n vec : Z) (j8 : word) (codec : zarr) (m : word -> option byte) (x7 x8 x28 x29 x30 x31 : word),
    (n + Z.of_nat k = maxLen + 1)%Z -> (1 <= k)%nat -> (minLen <= n)%Z ->
    (0 <= vec <= VB (Z.to_nat (n - minLen)))%Z -> MEMc j8 codec m ->
    fst (ha_outer k codec len cb lb alphaSize n vec) = hbAssignCodes code0 len cb lb minLen maxLen alphaSize ->
    evt s0segs POST (MS (mkR ra cSP gp tp c1 c1 x7 x8 s1 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                              (Z_to_bv 64 vec) c1 (Z_to_bv 64 alphaSize) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x24238) fc None m (seg_rom s0segs)).
  Proof.
    induction k as [|k IH]; intros n vec j8 codec m x7 x8 x28 x29 x30 x31 Hk Hk1 Hn Hv MEM RES; [lia|].
    pose proof (VB_bound (Z.to_nat (n - minLen)) ltac:(lia)) as VBB.
    bz_ceil; bz_params; unfold CEIL in *. pose proof AP as AP'. unfold apart in AP'.
    cps_destruct MEM as (COD & LEN & MI & MU & WM & ST & FR). unfold W in MU.
    pose proof (u32arr_bound s0segs m _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound s0segs m _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    cbn [ha_outer] in RES.
    (* [comment removed for export] *)
    assert (TAIL : forall codex vecx m' (y7 y8 y28 y29 y30 y31 : word),
        (codex, vecx) = ha_inner (Z.to_nat alphaSize) codec len cb lb n 0 vec -> (vec <= vecx <= vec + alphaSize)%Z -> MEMc j8 codex m' ->
        evt s0segs POST (MS (mkR ra cSP gp tp c1 c1 y7 y8 s1 cC cL (Z_to_bv 64 n) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                                  (Z_to_bv 64 vecx) c1 (Z_to_bv 64 alphaSize) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                             F (Z_to_bv 64 0x242a8) fc None m' (seg_rom s0segs))).
    { intros codex vecx m' y7 y8 y28 y29 y30 y31 RESi Hvx MEM'.
      rewrite <- RESi in RES.
      cps_destruct MEM' as (COD' & LEN' & MI' & MU' & WM' & ST' & FR'). unfold W in MU'.
      clear COD LEN MI MU WM ST FR CB LB. rename m into mold. rename m' into m.
      wstep. wstep; notrap. (* [comment removed for export] *)
      wstep. wstep; notrap. (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Ke; zify_cond_z Ke.
      - (* [comment removed for export] *)
        enter_with (IH (n + 1)%Z (vecx * 2)%Z j8 codex m); [st_eq| lia| lia| lia| | |].
        + replace (Z.to_nat (n + 1 - minLen)) with (S (Z.to_nat (n - minLen))) by lia. cbn [VB]. lia.
        + split; [exact COD'|]. split; [exact LEN'|]. split; [exact MI'|]. split; [unfold W; exact MU'|]. split; [exact WM'|]. split; [exact ST'| exact FR'].
        + rewrite <- RES. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
      - (* [comment removed for export] *)
        assert (k = 0)%nat by lia. subst k. cbn [ha_outer fst] in RES.
        wstep. wstep.
        rewrite <- RES. release_frame FR' ST' (bv_unsigned sp).
        replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
        wstep. unfold hbAssignCodes_post. finish. }
    wstep; if_cases Ka; zify_cond_z Ka.
    - (* [comment removed for export] *)
      replace (Z.to_nat alphaSize) with 0%nat in TAIL by lia. cbn [ha_inner] in TAIL.
      apply (TAIL codec vec m); [reflexivity| lia|].
      split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
    - wstep. wstep. wstep. wstep. wstep.
      enter_with (asg_inner (Z.to_nat alphaSize) 0 vec n j8 codec m); [st_eq| lia| lia| lia| lia| lia| lia| |].
      + split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR].
      + intros codex vecx m' x8' RESi Hvx MEM'. enter_with (TAIL codex vecx m'); [st_eq| exact RESi| lia| exact MEM'].
  Qed.

  Lemma asg_entry : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    u32arr s0segs m0 Ecode (ovw code0 Jc NC) -> u8arr s0segs m0 Elen (ovb len Jl NL) -> mem_inv s0segs m0 ->
    stk s0segs m0 lo usp ->
    evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 cC cL (Z_to_bv 64 minLen) (Z_to_bv 64 maxLen) (Z_to_bv 64 alphaSize)
                              a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x2420c) fc None m0 (seg_rom s0segs)).
  Proof.
    intros until t6. intros COD LEN MI ST. bz_ceil; bz_params; unfold CEIL in *.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl s0segs m0) as WM. unfold W in MU.
    pose proof AP as AP'. unfold apart in AP'.
    pose proof (u32arr_bound s0segs m0 _ _ COD) as CB. rewrite ovw_length_nat in CB.
    pose proof (u8arr_bound s0segs m0 _ _ LEN) as LB. rewrite ovb_length_nat in LB.
    pose proof (ovw_length code0 Jc NC ltac:(lia)) as LC'. pose proof (ovb_length len Jl NL ltac:(lia)) as LL'.
    assert (ALc : Z.land (Ecode + 4 * cb) 3 = 0%Z).
    { change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
      rewrite <- Z.add_mod_idemp_l by lia. rewrite Hc4, Z.add_0_l, Z.mul_comm. apply Z.mod_mul. lia. }
    carve_frame 16%nat ST.
    cps_destruct (CmpHmKit.rw_cells_junk16_C8 s0segs _ _ _ FR) as (nd & rr & FR8). clear FR.
    wstep. wstep.
    wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      wstep. wstep. release_frame FR8 ST (bv_unsigned sp).
      replace (Z_to_bv 64 (usp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      wstep. unfold hbAssignCodes_post, hbAssignCodes. replace (Z.to_nat (maxLen - minLen + 1)) with 0%nat by lia. cbn [ha_outer fst]. finish.
    - do 8 wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      enter_with (asg_outer (Z.to_nat (maxLen - minLen + 1)) minLen 0 (Z_to_bv 64 nd) code0 m1);
        [st_eq; rewrite ?ALc; rewrite ?(Z.div_mul alphaSize 4294967296) by lia; zres| lia| lia| lia| | | reflexivity].
      + replace (Z.to_nat (minLen - minLen)) with 0%nat by lia. cbn [VB]. lia.
      + split; [exact COD|]. split; [exact LEN|]. split; [exact MI|]. split; [unfold W; exact MU|]. split; [exact WM|]. split; [exact ST| exact FR8].
  Qed.
End ASG.

Theorem S0_hbAssignCodes : hbAssignCodes_spec S0C.
Proof.
  unfold hbAssignCodes_spec. cbn [ci_segs ci_hbAssignCodes S0C]. intros. subst.
  eapply asg_entry; try eassumption; try lia.
Qed.

End ACeilS1.
