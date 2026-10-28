(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memchr F_memcmp F_syscalls F_twoway_A.
Import ListNotations.
Open Scope bv_scope.

Notation w z := (Z_to_bv 64 z) (only parsing).

Ltac zs := zstep; fix_lit_store.
Ltac cstep := zs; try (first [ if_true | if_false ]).

Section Setup.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H h0 : Z) (hay slack : list byte) (canary : word) (lo : Z).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) hay.
  Hypothesis PAD : ((- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis BND : (0 <= H /\ H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPH : (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= H)%Z.
  Hypothesis SEPG : (got_ssp + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPC : (ssp_guard + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPN : (NAD + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis HPOS : (0 < H)%Z.
  Hypothesis H0 : (H <= h0 <= H + Z.of_nat (length hay))%Z.

  Notation len := (Z.of_nat (length hay)).
  Notation full := (hay ++ Z_to_bv 8 0 :: slack).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z.
  Notation POST := (twoway_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m).

  #[using="LO BND"] Lemma tw_exit1 : forall m1 (cs : list cell) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x9 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    INVc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m H hay slack canary lo m1 ->
    rw_cells rsegs m1 (SP + -2240) cs -> cells_size cs = 2128%nat ->
    evt rsegs POST (MS (mkR x1 (w (SP + -2240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (w ssp_guard) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (w 0x24f88) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros Ic FRlo CS. pose proof Ic as Ic'.
    destruct Ic as (HAY & NEE & MI & MU & WM & STK & GOT & GUARD & FRhi); unfold HICELLS in FRhi. pose proof BND as BD.
    unfold NAD, NAD1, got_ssp, ssp_guard, M1, BSW1 in *.
    do 6 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    eapply tw_epi; eauto.
  Qed.

  #[using="NONUL"] Lemma hay_read' : forall m1 i a, bytes_at rsegs m1 H full -> (0 <= i < len)%Z -> a = w (H + i) ->
    exists b, ov_read_bytes rsegs m1 a 1 = Some [b] /\ (0 < bv_unsigned b < 256)%Z.
  Proof.
    intros m1 i a HAY Hi Ha. destruct (hay_read H hay slack NONUL m1 i a HAY Hi Ha) as (b & RD & _ & R). exists b; auto.
  Qed.
  #[using="Type"] Lemma nul_read : forall m1 a, bytes_at rsegs m1 H full -> a = w (H + len) ->
    ov_read_bytes rsegs m1 a 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m1 a HAY Ha. eapply (u8ro_read rsegs m1 H full len); eauto; [|lia].
    rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity.
  Qed.

  Ltac bundle_invc := repeat (split; [eassumption|]); eassumption.

  Ltac iter1 l :=
    let K := fresh "K" in
    destruct (Z.eq_dec (h0 + l) (H + len)) as [?E|?NE];
    [ (let RD := fresh "RDZ" in
       pose proof (nul_read _ (w (h0 + l)) ltac:(eassumption) ltac:(f_equal; lia)) as RD;
       do 3 zs; if_cases K; zify_cond K; [ | exfalso; apply K; reflexivity ];
       eapply tw_exit1; [ bundle_invc | eassumption | reflexivity ])
    | (let RD := fresh "RD" in let b := fresh "b" in let NZ := fresh "NZ" in
       destruct (hay_read' _ (h0 - H + l) (w (h0 + l)) ltac:(eassumption) ltac:(lia) ltac:(f_equal; lia)) as (b & RD & NZ);
       do 3 zs; if_cases K; zify_cond K; [ exfalso; lia | ]) ].

  Ltac run_until stop := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail | _ => cstep end).

  Definition LOCELLS1 (ja jb jc jd je jf : list byte) : list cell :=
    [CB 840 ja; C8 (w 1); C8 (w 7); C8 (w 6); CB 16 jb; C8 (w 2); CB 16 jc; C8 (w 5); CB 16 jd; C8 (w 4); CB 48 je; C8 (w 3); CB 1104 jf;
     C8 (w 0); C8 (w BSW1); C8 (w 0); C8 (w 0)].

  #[using="NONUL PAD LO BND SEPH SEPG SEPC HPOS H0"] Lemma tw_setup3 : forall m1 ja jb jc jd je jf x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x26 x27 x28 x29 x30 x31,
    INVc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m H hay slack canary lo m1 ->
    rw_cells rsegs m1 (SP + -2240) (LOCELLS1 ja jb jc jd je jf) ->
    evt rsegs POST (MS (mkR x1 (w (SP + -2240)) gp tp x5 x6 x7 (w NAD) (w h0) (w NAD) (w (NAD + 5)) (w 2) x13 x14 x15 x16 x17
                            (w 2) (w ssp_guard) x20 x21 (w NAD1) (w 7) (w 1) (w 5) x26 x27 x28 x29 x30 x31)
                       F (w 0x24f5c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros Ic FRlo.
    destruct Ic as (HAY & NEE & MI & MU & WM & STK & GOT & GUARD & FRhi); unfold HICELLS in FRhi. unfold LOCELLS1 in FRlo.
    pose proof BND as BD. unfold NAD, NAD1, got_ssp, ssp_guard, M1, BSW1 in *. unfold chunked_bytes in NEE.
    destruct (proj1 (bytes_at_app rsegs _ 66514 [Z_to_bv 8 99; Z_to_bv 8 104; Z_to_bv 8 117; Z_to_bv 8 110; Z_to_bv 8 107]
                                   [Z_to_bv 8 101; Z_to_bv 8 100; Z_to_bv 8 0]) NEE) as [_ NEE5].
    replace (66514 + Z.of_nat (length _))%Z with 66519%Z in NEE5 by reflexivity.
    zs. call memcmp_spec.
    1:{ rewrite unsigned_lit by lia. exact NEE. }
    1:{ rewrite unsigned_lit by lia. exact NEE5. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ exact MI. }
    run_until 0x24fe4%Z.
    eapply tw_loop; try eassumption.
    all: lazymatch goal with
         | |- INV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => split; [ bundle_invc | do 7 eexists; eassumption ]
         | |- _ = _ => reflexivity
         | _ => idtac end.
    all: lazymatch goal with
         | |- (_ < _)%nat => apply Nat.lt_succ_diag_r
         | _ => lia end.
  Qed.

  #[using="NONUL PAD LO BND SEPH SEPG SEPC HPOS H0"] Lemma tw_setup2 : forall m1 ja jb jc jd je jf x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31,
    INVc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m H hay slack canary lo m1 ->
    rw_cells rsegs m1 (SP + -2240) (LOCELLS1 ja jb jc jd je jf) ->
    evt rsegs POST (MS (mkR x1 (w (SP + -2240)) gp tp x5 x6 x7 (w NAD) (w h0) x10 x11 x12 x13 x14 x15 x16 x17
                            x18 (w ssp_guard) x20 x21 (w NAD1) (w 7) x24 x25 x26 x27 x28 x29 x30 x31)
                       F (w 0x24eac) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros Ic FRlo. pose proof Ic as Ic'.
    destruct Ic as (HAY & NEE & MI & MU & WM & STK & GOT & GUARD & FRhi); unfold HICELLS in FRhi.
    pose proof FRlo as FRlo'. unfold LOCELLS1 in FRlo.
    pose proof BND as BD. unfold NAD, NAD1, got_ssp, ssp_guard, M1, BSW1 in *. unfold chunked_bytes in NEE.
    pose proof (nee_read H hay slack _ 0 _ (w 66514) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN0.
    pose proof (nee_read H hay slack _ 1 _ (w 66515) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN1.
    pose proof (nee_read H hay slack _ 2 _ (w 66516) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN2.
    pose proof (nee_read H hay slack _ 3 _ (w 66517) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN3.
    pose proof (nee_read H hay slack _ 4 _ (w 66518) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN4.
    pose proof (nee_read H hay slack _ 5 _ (w 66519) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN5.
    pose proof (nee_read H hay slack _ 6 _ (w 66520) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN6.
    pose proof (nee_read H hay slack _ 7 _ (w 66521) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN7.

    run_until 0x24f5c%Z.
    apply (tw_setup3 m1 ja jb jc jd je jf); [exact Ic'|exact FRlo'].
  Qed.
End Setup.
