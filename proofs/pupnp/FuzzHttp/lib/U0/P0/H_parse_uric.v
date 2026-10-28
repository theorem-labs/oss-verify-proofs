(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memchr F_ctype HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parse_uric_entry := 0x170e4%Z.
Notation MARKTAB := 0x106de%Z.
Notation RESVTAB := 0x1044b%Z.
Ltac sstep := step; fix_lit_store.

Definition mark10 : list byte := map (Z_to_bv 8) [45; 95; 46; 33; 126; 42; 39; 40; 41; 0]%Z.
Definition resv13 : list byte := map (Z_to_bv 8) [59; 47; 63; 58; 64; 38; 61; 43; 36; 44; 123; 125; 0]%Z.
Lemma mark_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m MARKTAB mark10.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m MARKTAB mark10 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma resv_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m RESVTAB resv13.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m RESVTAB resv13 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
Lemma memchr_ok_mark : forall A c, memchr_ok A c 10 mark10.
Proof. intros A c. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat 10) mark10)); cbn; lia. Qed.
Lemma memchr_ok_resv : forall A c, memchr_ok A c 13 resv13.
Proof. intros A c. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat 13) resv13)); cbn; lia. Qed.
Lemma memchr_res_small' : forall A c n buf, (0 <= A)%Z -> (0 <= memchr_res A c n buf <= A + Z.of_nat (length buf))%Z.
Proof.
  intros A c n buf HA. unfold memchr_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (L & _ & _). rewrite firstn_length in L. lia.
Qed.

Definition parse_uric_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (IN O max : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (i : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (O, O + 16)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 112) (bv_unsigned sp)
    /\ rw_cells rsegs m' O [C8 (wz IN); C8 (wz i)]
    /\ bytes_at rsegs m' IN bs
    /\ (0 <= i <= max)%Z.

Definition parse_uric_stmt : Prop :=
  forall (IN O max : Z) (bs : list byte) (ow1 ow2 : word)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at rsegs m IN bs -> (Z.of_nat (length bs) >= max)%Z -> (0 <= max)%Z ->
  rw_cells rsegs m O [C8 ow1; C8 ow2] ->
  stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) -> (256 <= bv_unsigned sp)%Z ->

  (IN + Z.of_nat (length bs) <= bv_unsigned sp - 112)%Z -> (0 < IN)%Z ->
  (bv_unsigned sp <= O)%Z -> (O + 16 < 2^63)%Z -> (O mod 8 = 0)%Z ->
  mem_inv rsegs m -> a0 = wz IN -> a1 = wz max -> a2 = wz O ->
  evt rsegs (parse_uric_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IN O max bs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_uric_entry) fc None m (seg_rom rsegs)).

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (IN O max : Z) (bs : list byte) (ow1 ow2 : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis SPR : (256 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis LBS : (Z.of_nat (length bs) >= max)%Z.
  Hypothesis MAX : (0 <= max)%Z.
  Hypothesis BLO : (IN + Z.of_nat (length bs) <= bv_unsigned sp - 112)%Z.
  Hypothesis INNZ : (0 < IN)%Z.
  Hypothesis LO : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 16 < 2^63)%Z.
  Hypothesis OAL : (O mod 8 = 0)%Z.

  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation POST := (parse_uric_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IN O max bs m0).

  Definition minv (m : mem) : Prop :=
    (exists j8, rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk rsegs m (bv_unsigned sp + -112) (bv_unsigned sp + -112)
    /\ rw_cells rsegs m O [C8 ow1; C8 ow2]
    /\ bytes_at rsegs m IN bs
    /\ mem_inv rsegs m
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (O, O + 16)]%Z m0 m
    /\ wmono rsegs m0 m.

  Notation LST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x27 x28 x29 x30 x31 mm :=
    (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 IN) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 max) (Z_to_bv 64 MARKTAB) (Z_to_bv 64 RESVTAB) x22 (Z_to_bv 64 (Z.lxor IN 18446744073709551615)) (Z_to_bv 64 37) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma tail : forall (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    minv m -> (0 <= i <= max)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 IN) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 i) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x171dc) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ([j8 FR] & ST & OC & BUF & MI & MU & WM) HI.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    sstep. sstep. do 16 step.
    release_frame FR ST (bv_unsigned sp).
    unfold parse_uric_post. finish. all: first [exact OC | exact BUF | lia].
  Qed.

  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma tailA : forall (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    minv m -> (0 <= i <= max)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 IN) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 i) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x171d4) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MV HI.
    pose proof (munch_refl [] m) as MUx.
    ub_align.
    apply (tail i); assumption.
  Qed.

  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.
  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma nth_bs : forall i, (0 <= i < max)%Z -> exists b, nth_error bs (Z.to_nat i) = Some b.
  Proof.
    intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  Ltac mv_tac FR := split; [eexists; exact FR|]; repeat (split; [assumption|]); assumption.
  Ltac get_mv FR := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let MV := fresh "MV" in assert (MV : minv mm) by mv_tac FR end.

  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 m,
    (max - i < Z.of_nat k)%Z -> (0 <= i < max)%Z -> minv m ->
    evt rsegs POST (LST 0x17160 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 i) x22 x27 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK HI MV; [lia|].
    pose proof MV as ([j8 FR] & ST & OC & BUF & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bs i ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m IN bs i b (Z_to_bv 64 (IN + i)) BUF Hb ltac:(lia) eq_refl) as RD.

    assert (CONT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y27 y28 y29 y30 y31 m',
      minv m' ->
      evt rsegs POST (LST 0x17158 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 i) y22 y27 y28 y29 y30 y31 m')).
    { intros until m'. intros MV'. zstep. zstep. if_cases KC; zify_cond KC.
      -   zstep. apply (tailA max); [exact MV'| lia].
      - apply (IH (i + 1)%Z); [lia| lia| exact MV']. }
    step. ubr.
    zstep. zstep. zstep. zstep.
    call isalnum_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K1; zify_cond K1.
    {   apply CONT. exact MV. }
    zstep. zstep. zstep. zstep.
    call memchr_spec.
    all: side (rewrite ?unsigned_lit by lia; first [apply mark_bytes; exact MI | apply memchr_ok_mark | exact MI]).
    clear MV. rename MI0 into MI. get_mv FR.
    rewrite !unsigned_lit by lia.
    pose proof (memchr_res_small' MARKTAB (bv_unsigned b mod 256) 10 mark10 ltac:(lia)) as MR. cbn [length mark10 map Z.of_nat Pos.of_succ_nat Pos.succ] in MR.
    zstep. if_cases K2; zify_cond K2.
    {   apply CONT. exact MV. }
    clear MR. zstep. zstep. zstep. zstep.
    call memchr_spec.
    all: side (rewrite ?unsigned_lit by lia; first [apply resv_bytes; exact MI | apply memchr_ok_resv | exact MI]).
    clear MV. rename MI0 into MI. get_mv FR.
    rewrite !unsigned_lit by lia.
    pose proof (memchr_res_small' RESVTAB (bv_unsigned b mod 256) 13 resv13 ltac:(lia)) as MR. cbn [length resv13 map Z.of_nat Pos.of_succ_nat Pos.succ] in MR.
    zstep. if_cases K3; zify_cond K3.
    {   apply CONT. exact MV. }
    clear MR. zstep. zstep. if_cases K4; zify_cond K4.
    {   apply (tailA i); [exact MV| lia]. }
    zstep. if_cases K5; zify_cond K5.
    {   apply (tailA i); [exact MV| lia]. }
    step.
    first [ ubr
          | ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; try change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia) ].
    destruct (nth_bs (i + 1) ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
    pose proof (u8ro_read rsegs _ IN bs (i + 1) b1 (Z_to_bv 64 (IN + i + 1)) BUF Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1.
    zstep. zstep.
    call isxdigit_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K6; zify_cond K6.
    {   apply (tailA i); [exact MV| lia]. }
    step.
    first [ ubr
          | ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; try change ((-3) mod 18446744073709551616) with 18446744073709551613 in KU; lia) ].
    destruct (nth_bs (i + 2) ltac:(lia)) as [b2 Hb2]. pose proof (byte_range b2) as BR2.
    pose proof (u8ro_read rsegs _ IN bs (i + 2) b2 (Z_to_bv 64 (IN + i + 2)) BUF Hb2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
    zstep. zstep.
    call isxdigit_spec. 1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact MI. }
    rewrite unsigned_lit by lia.
    zstep. if_cases K7; zify_cond K7.
    { apply CONT. exact MV. }
    zstep. apply (tailA i); [exact MV| lia].
  Qed.

  #[using="SPR LBS MAX BLO INNZ LO OHI OAL"] Lemma body : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    bytes_at rsegs m0 IN bs -> rw_cells rsegs m0 O [C8 ow1; C8 ow2] ->
    stk rsegs m0 (bv_unsigned sp - 112) (bv_unsigned sp) -> mem_inv rsegs m0 ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 IN) (Z_to_bv 64 max) (Z_to_bv 64 O) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 parse_uric_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until x31. intros BUF OC ST MI. unfold parse_uric_entry.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (O, O + 16)]%Z m0) as MU.
    pose proof (wmono_refl rsegs m0) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ OC) as OB. cbn [cells_size csize Nat.add] in OB.
    carve_frame 112%nat ST.
    do 14 sstep.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    {   zstep. zstep. step. ubr3. apply (tail 0); [mv_tac FR| lia]. }
    ub_null.
    do 11 zstep.
    apply (loop (Datatypes.S (Z.to_nat max)) 0); [lia| lia| mv_tac FR].
  Qed.
End WALK.

Lemma parse_uric_spec : parse_uric_stmt.
Proof.
  unfold parse_uric_stmt. intros until m.
  intros BUF LBS MAX OC ST SPLO BLO INNZ LO OHI OAL MI -> -> ->.
  eapply body; eauto. pose proof (word_lt64 sp). lia.
Qed.

