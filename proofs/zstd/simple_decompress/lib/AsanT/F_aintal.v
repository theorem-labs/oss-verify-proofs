(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF StrwF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a4 a5 a6 a7 : word) (A n : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section IMemset.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Hypothesis MI0 : mem_inv bsegs m.
  Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Ltac with_arr tac :=
    lazymatch goal with
    | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
    end.
  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    unfold imemset_post; finish; subst; assumption.

  (* [comment removed for export] *)
  Lemma imemset_bloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF bsegs RNG POST (ST 0x65f18 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi x13 ->.
    mst i 1%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia|f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
    - zstep. fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma imemset_wloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF bsegs RNG POST (ST 0x65f4c m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi [qi Hqi] [qn Hqn] x13 ->.
    mst i 8%nat ltac:(reflexivity).
    mst (i + 8)%Z 8%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) (i + 16) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia| exists (qi + 1); lia| exists qn; lia| f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|]. destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia]).
  Qed.

  Lemma imemset_body : forall junk,
    rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
    evtF bsegs RNG POST (ST 0x65f00 m (Z_to_bv 64 0) a2 a3).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 0) junk) as FIL.
    zstep. zstep.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      do 7 zstep. zstep.
      assert (HA : A mod 16 = 0 /\ n mod 16 = 0).
      { rewrite Z.land_lor_distr_l in K0. apply Z.lor_eq_0_iff in K0. destruct K0 as [Kn KA].
        change 15 with (Z.ones 4) in Kn, KA. rewrite Z.land_ones in Kn, KA by lia. change (2^4) with 16 in Kn, KA. lia. }
      eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| exists 0; lia| exists (n / 16); lia| symmetry; apply Z_to_bv_plus0].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep.
      eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| symmetry; apply Z_to_bv_plus0].
  Qed.
End IMemset.

Lemma imemset_spec : forall (A n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (junk : list byte),
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> 0 <= A -> 0 < n -> A + n < 2^64 ->
  rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
  mem_inv bsegs m ->
  rng RNG A n ->
  evtF bsegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x65f00) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
  pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
  rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xd0f00) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x15f788 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xd0f00 (0xd0f00 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma internal_allocator_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells bsegs m 0xc72e8 [C8 (Z_to_bv 64 0x15f7a0)] -> rw_cells bsegs m 0x15f7a0 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x60400) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RSTK.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.                                   (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  destruct ia.
  - (* [comment removed for export] *)
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold ia_post. finish.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros q Hq; lia.
    + intros j Hj. pose proof (Z2 eq_refl j ltac:(lia)) as B. eapply bytes_at_agree; [exact B|].
      intros i Hi. apply MU. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
  - (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4)]%Z) in MU.
    2:{ unfold sub_fp; cbn [outside]; intros q Hq; lia. }
    clear Z2.
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    do 8 zstep.                                (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in FL. change (0 + 256 * 0) with 0 in FL.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. zstep. step. if_lit.                (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in FL.
    lstep. step. if_lit.                       (* [comment removed for export] *)
    step. step. zstep. zstep. zstep. step. step.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 40%nat IA.
    step. call (imemset_spec 0x151f08 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
    rename POST into Z1.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xd0f00 0xd0f08 (855808 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
    clear IA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xd0f00 0xd0f08 IA0 ltac:(lia)) as [junk1 FR1] end.
    clear IA0. change (Z.to_nat (0xd0f08 - 0xd0f00)) with 8%nat in FR1.
    step.
    (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xd0f08 0x110f08 (855808 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
    clear IA1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xd0f08 0x110f08 IA2 ltac:(lia)) as [junk2 DST2] end.
    clear IA2. change (0x110f08 - 0xd0f08) with 0x40000 in DST2.
    step. call (imemset_spec 0xd0f08 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
    rename POST into Z2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MAP : forall j, 0 <= j < 32768 -> bytes_at bsegs mm (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0)))
        by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
      pose proof (stk_of_cb mm 0xd0f08 0x40000 _ Z2 ltac:(lia)) as IA2 end.
    clear Z2. box MAP. snapshot [(0x110f40, 0x151f08); (0x15f788, 0x15f78c)]%Z MUm WMm.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0x110f08 0x110f40 (855808 + 528392) IA3 ltac:(lia)) as [IAg IA4];
      destruct (stk_split bsegs mm 0x110f40 0x111cc0 (855808 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
      destruct (stk_cb mm 0x110f40 0x111cc0 IA5 ltac:(lia)) as [junk3 DST3] end.
    clear IA3 IA4 IA5. change (0x111cc0 - 0x110f40) with 0xd80 in DST3.
    step. call (imemset_spec 0x110f40 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0x110f40 0xd80 _ POST ltac:(lia)) as IA5 end.
    clear POST.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. step.           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0x111cc0 (855808 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
    clear IA6. change (855808 + 528392 - 0x111cc0) with 0x40248 in DST4.
    step. call (imemset_spec 0x111cc0 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0x111cc0 0x40248 _ POST ltac:(lia)) as IA6 end.
    clear POST.
    (* [comment removed for export] *)
    step. step. step. step. if_lit.            (* [comment removed for export] *)
    zstep. zstep. zstep. step.                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0x111cc0 0x111cd0 (0x111cc0 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
      destruct (stk_cb mm 0x111cc0 0x111cd0 IA7 ltac:(lia)) as [junk5 FR5] end.
    clear IA6 IA7. change (Z.to_nat (0x111cd0 - 0x111cc0)) with 16%nat in FR5.
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells bsegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
      pose proof (stk_of_rw_cells bsegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
      pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
    assert (IA : stk bsegs m1 0xd0f00 (0xd0f00 + 0x81030)).
    { eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
      eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
      eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
    unfold ia_post. finish.
    intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
    intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.
End CANSEC1.
