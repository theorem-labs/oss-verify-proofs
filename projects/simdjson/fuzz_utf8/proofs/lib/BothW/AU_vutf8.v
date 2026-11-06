(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import RtCells AU_vutf8_ck.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.
Definition AVUTF8 : Z := 0xb7cc4.
Definition VUTF8_STACK : Z := 112.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z).
  Notation n := (zlength pl).
  Notation SP := (bv_unsigned sp).
  Hypothesis BA : bytes_at bsegs m D (map (Z_to_bv 8) pl).
  Hypothesis UNP0 : unpoisoned m D (D + n).
  Hypothesis D8 : D mod 8 = 0.
  Hypothesis DLO : 0 < D.                          (* [comment removed for export] *)
  Hypothesis DE : D + n + 8 <= KEND.
  Hypothesis NLT : n < 2^26.
  Hypothesis LO : lo <= SP - 112.
  Hypothesis CLO : KHIGH <= lo.                    (* [comment removed for export] *)
  Hypothesis DLE : D + n <= lo.
  Hypothesis GOT0 : rt_got m.
  Hypothesis SHB0 : rt_shbase m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH : rng RNG (shad D) (nshad n).


  Notation W := [(SP - 112, SP)].
  Notation bs := (map (Z_to_bv 8) pl).

  Definition FRAME (m1 : word -> option byte) : Prop := exists junk8,
    rw_cells bsegs m1 (SP + -112) [CB 8 junk8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at bsegs m1 D bs /\ unpoisoned m1 D (D + n) /\ FRAME m1 /\ stk bsegs m1 lo (SP + -112)
    /\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Definition vu_post : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ (a0' = Z_to_bv 64 0 \/ a0' = Z_to_bv 64 1)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SP.

  (* [comment removed for export] *)
  Lemma payload_rdx : forall m1 k, bytes_at bsegs m1 D bs -> 0 <= k < n ->
    exists b : byte, ov_read_bytes bsegs m1 (wa (D + k)) 1 = Some [b].
  Proof.
    intros m1 k B Hk. unfold zlength in Hk.
    pose proof (bytes_at_read bsegs m1 D bs k 1 B ltac:(lia) ltac:(rewrite length_map; lia)) as R.
    destruct (skipn (Z.to_nat k) bs) as [|b r] eqn:E.
    { exfalso. assert (L : length (skipn (Z.to_nat k) bs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn, length_map in L. lia. }
    exists b. exact R.
  Qed.

  (* [comment removed for export] *)
  Notation GST pc mm xr xa0 xa3 xa4 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xt :=
    (MS (mkR xr (Z_to_bv 64 (SP + -112)) gp tp (Z_to_bv 64 224) (Z_to_bv 64 128) (Z_to_bv 64 27) (Z_to_bv 64 (-1048576)) (Z_to_bv 64 (-8)) xa0
             (Z_to_bv 64 D) (Z_to_bv 64 n) xa3 xa4 (Z_to_bv 64 (Z.lxor D 18446744073709551615)) (Z_to_bv 64 192) (Z_to_bv 64 (-65))
             x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xt (Z_to_bv 64 2147450880) (Z_to_bv 64 240) (Z_to_bv 64 (-1114112)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma vu_epi : forall m1 v (yr y5 y6 y7 x0 x1 ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31 : word),
    INV m1 -> (v = 0 \/ v = 1) ->
    evtF bsegs RNG vu_post
      (MS (mkR yr (Z_to_bv 64 (SP + -112)) gp tp y5 y6 y7 x0 x1 (Z_to_bv 64 v) ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb8090) fc None m1 (seg_rom bsegs)).
  Proof.
    intros m1 v yr y5 y6 y7 x0 x1 ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31 (BA1 & UNP1 & [junk8 FR] & ST & MU & WM & MI) HV.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold vu_post.
    do 15 eexists. exists m1. split; [unfold mkR; reflexivity|].
    split; [destruct HV as [-> | ->]; [left|right]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Ltac pc_is p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
  Ltac ckrd UNP A b RDb CKb :=
    destruct (unpoisoned_check_rd bsegs _ D (D + n) A 1 UNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDb & CKb);
    unfold shad, ASHOFF in RDb; replace (2147450880 + Z.shiftr A 3) with (Z.shiftr A 3 + 2147450880) in RDb by lia.
  Ltac ckcut L A bb CKb :=
    eapply evtF_cut;
    [ eapply L with (b := bb);
      [ lia
      | first [ exact CKb | lazymatch goal with |- _ \/ (_ /\ ?P mod 8 + _ - _ < _) => replace P with A by lia end; exact CKb ] ]
    | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO; subst ms' ].
  (* [comment removed for export] *)
  Ltac br K :=
    if_cases K; try (zify_cond K; rewrite ?unsigned_lit in K by lia);
    try (pc_is 0xb80cc; exfalso; rewrite ?zb_lxor_ones in K by lia;
         try (change (bv_unsigned (Z_to_bv 64 (-8))) with 18446744073709551608 in K); lia).
  Ltac fin NEXT FALSE INV1 :=
    first [ pc_is 0xb7d44; apply NEXT; lia
          | pc_is 0xb808c; apply FALSE
          | pc_is 0xb8090; apply vu_epi; [exact INV1| left; reflexivity]
          | pc_is 0xb7d40; zstep; apply NEXT; lia ].

  Lemma vu_loop : forall fuel pos m1 (xr xa0 xa3 xa4 x2 x4 x5 x6 x7 x8 x9 x10 x11 xt : word),
    Z.of_nat fuel > n - pos -> 0 <= pos < n -> INV m1 ->
    evtF bsegs RNG vu_post (GST 0xb7d4c m1 xr xa0 xa3 xa4 x2 (Z_to_bv 64 pos) x4 x5 x6 x7 x8 x9 x10 x11 xt).
  Proof.
    induction fuel as [|fuel IH]; intros pos m1 xr xa0 xa3 xa4 x2 x4 x5 x6 x7 x8 x9 x10 x11 xt FU PR INV1; [lia|].
    pose proof INV1 as (BA1 & UNP1 & FR & ST & MU & WM & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. unfold KEND in DE'.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    (* [comment removed for export] *)
    assert (NEXT : forall q (yr ya0 ya3 ya4 y3 y4 y5 y6 y7 y8 y9 y10 y11 yt : word), pos < q <= n ->
              evtF bsegs RNG vu_post (GST 0xb7d44 m1 yr ya0 ya3 ya4 (Z_to_bv 64 q) y3 y4 y5 y6 y7 y8 y9 y10 y11 yt)).
    { intros q yr ya0 ya3 ya4 y3 y4 y5 y6 y7 y8 y9 y10 y11 yt Hq.
      zstep. zstep. if_cases Kq; zify_cond Kq; rewrite ?unsigned_lit in Kq by lia.
      - zstep. zstep. apply vu_epi; [exact INV1| right; reflexivity].
      - apply IH; [lia| lia| exact INV1]. }
    (* [comment removed for export] *)
    assert (FALSE : forall (yr ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 yt : word),
              evtF bsegs RNG vu_post (GST 0xb808c m1 yr ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 yt)).
    { intros. zstep. apply vu_epi; [exact INV1| left; reflexivity]. }
    (* [comment removed for export] *)
    assert (SLOW1 : forall (yr ya3 ya4 y2 y4 y5 y6 y7 y8 y9 y10 y11 yt : word),
              evtF bsegs RNG vu_post (GST 0xb7e70 m1 yr (Z_to_bv 64 (D + pos)) ya3 ya4 y2 (Z_to_bv 64 pos) y4 y5 y6 y7 y8 y9 y10 y11 yt)).
    { intros.
      destruct (payload_rdx m1 pos BA1 ltac:(lia)) as [c0 R0].
      zstep. br G0.                                            (* [comment removed for export] *)
      ckrd UNP1 (D + pos) b RDb CKb. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7b24 (D + pos) b CKb. clear RDb CKb.
      zstep. zstep. br K; try fin NEXT FALSE INV1.          (* [comment removed for export] *)
      zstep. zstep. zstep. br K2; try fin NEXT FALSE INV1.    (* [comment removed for export] *)
      { (* [comment removed for export] *)
        zstep. zstep. br K3; try fin NEXT FALSE INV1.        (* [comment removed for export] *)
        { (* [comment removed for export] *)
          zstep. zstep. br K4; try fin NEXT FALSE INV1.      (* [comment removed for export] *)
          zstep. zstep. br Kb4; try fin NEXT FALSE INV1.     (* [comment removed for export] *)
          destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1]. destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
          destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
          zstep. zstep. br G1. zstep.                           (* [comment removed for export] *)
          ckrd UNP1 (D + (pos + 1)) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7c2c (D + (pos + 1)) b1 CKb1. clear RDb1 CKb1.
          zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.  (* [comment removed for export] *)
          zstep. zstep. br G2. zstep.
          ckrd UNP1 (D + (pos + 2)) b2 RDb2 CKb2. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7c54 (D + (pos + 2)) b2 CKb2. clear RDb2 CKb2.
          zstep. zstep. br Kc2; try fin NEXT FALSE INV1.         (* [comment removed for export] *)
          zstep. zstep. br G3. zstep.
          ckrd UNP1 (D + (pos + 3)) b3 RDb3 CKb3. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7c78 (D + (pos + 3)) b3 CKb3. clear RDb3 CKb3.
          zstep. zstep. br Kc3; try fin NEXT FALSE INV1.         (* [comment removed for export] *)
          do 6 zstep. zstep. br Kc4; try fin NEXT FALSE INV1.    (* [comment removed for export] *)
          zstep. fin NEXT FALSE INV1. }
        (* [comment removed for export] *)
        zstep. zstep. br Kb3; try fin NEXT FALSE INV1.       (* [comment removed for export] *)
        destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1]. destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
        zstep. zstep. br G1. zstep.
        ckrd UNP1 (D + (pos + 1)) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7ba0 (D + (pos + 1)) b1 CKb1. clear RDb1 CKb1.
        zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.    (* [comment removed for export] *)
        zstep. zstep. br G2. zstep.
        ckrd UNP1 (D + (pos + 2)) b2 RDb2 CKb2. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7bc8 (D + (pos + 2)) b2 CKb2. clear RDb2 CKb2.
        zstep. zstep. br Kc2; try fin NEXT FALSE INV1.           (* [comment removed for export] *)
        do 6 zstep. zstep. br Kc3; try fin NEXT FALSE INV1.      (* [comment removed for export] *)
        zstep. br Kc4; try fin NEXT FALSE INV1.                  (* [comment removed for export] *)
        zstep. zstep. zstep. br Kc5; try fin NEXT FALSE INV1.    (* [comment removed for export] *)
        zstep. fin NEXT FALSE INV1. }
      (* [comment removed for export] *)
      zstep. zstep. br Kb2; try fin NEXT FALSE INV1.         (* [comment removed for export] *)
      destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
      zstep. zstep. br G1. zstep.                               (* [comment removed for export] *)
      ckrd UNP1 (D + (pos + 1)) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7b5c (D + (pos + 1)) b1 CKb1. clear RDb1 CKb1.
      zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.      (* [comment removed for export] *)
      zstep. zstep. br Kc2; try fin NEXT FALSE INV1.             (* [comment removed for export] *)
      zstep. fin NEXT FALSE INV1. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. br K16.                               (* [comment removed for export] *)
    all: try (pc_is 0xb7e70; apply SLOW1).
    (* [comment removed for export] *)
    zstep. br G0. zstep. br G8.                                (* [comment removed for export] *)
    ckrd UNP1 (D + pos) b0 RDb0 CKb0. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7a10 (D + pos) b0 CKb0. clear RDb0 CKb0.
    zstep. ckrd UNP1 (D + pos + 7) b7 RDb7 CKb7. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7a24 (D + pos + 7) b7 CKb7. clear RDb7 CKb7.
    destruct (payload_rdx m1 (pos + 0) BA1 ltac:(lia)) as [c0 R0]. destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
    destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2]. destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
    zstep. zstep. zstep. zstep. clear R0 R1 R2 R3.
    destruct (payload_rdx m1 (pos + 4) BA1 ltac:(lia)) as [c4 R4]. destruct (payload_rdx m1 (pos + 5) BA1 ltac:(lia)) as [c5 R5].
    destruct (payload_rdx m1 (pos + 6) BA1 ltac:(lia)) as [c6 R6]. destruct (payload_rdx m1 (pos + 7) BA1 ltac:(lia)) as [c7 R7].
    zstep. ckrd UNP1 (D + pos + 8) b8 RDb8 CKb8. zstep. zstep. zstep. rewrite sxb_sval.
    zstep. zstep. zstep. zstep. clear R4 R5 R6 R7.
    ckcut ckb_b7a58 (D + pos + 8) b8 CKb8. clear RDb8 CKb8.
    zstep. ckrd UNP1 (D + pos + 15) b15 RDb15 CKb15. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b7a6c (D + pos + 15) b15 CKb15. clear RDb15 CKb15.
    do 10 zstep.
    destruct (payload_rdx m1 (pos + 8) BA1 ltac:(lia)) as [c8 R8]. destruct (payload_rdx m1 (pos + 9) BA1 ltac:(lia)) as [c9 R9].
    destruct (payload_rdx m1 (pos + 10) BA1 ltac:(lia)) as [c10 R10]. destruct (payload_rdx m1 (pos + 11) BA1 ltac:(lia)) as [c11 R11].
    zstep. zstep. zstep. zstep. clear R8 R9 R10 R11.
    do 4 zstep.
    destruct (payload_rdx m1 (pos + 12) BA1 ltac:(lia)) as [c12 R12]. destruct (payload_rdx m1 (pos + 13) BA1 ltac:(lia)) as [c13 R13].
    destruct (payload_rdx m1 (pos + 14) BA1 ltac:(lia)) as [c14 R14]. destruct (payload_rdx m1 (pos + 15) BA1 ltac:(lia)) as [c15 R15].
    zstep. zstep. zstep. zstep. clear R12 R13 R14 R15.
    do 13 zstep.
    zstep.                                                     (* [comment removed for export] *)
    do 4 zstep.
    zstep. br Km.                                              (* [comment removed for export] *)
    all: first [ pc_is 0xb7d44; apply NEXT; lia | pc_is 0xb7e70; apply SLOW1 ].
  Qed.

  (* [comment removed for export] *)
  Lemma vu_body : stk bsegs m lo SP -> mem_inv bsegs m ->
    evtF bsegs RNG vu_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVUTF8) fc None m (seg_rom bsegs)).
  Proof.
    intros ST MI. unfold AVUTF8.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. unfold KEND in DE'.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    assert (BL : D + Z.of_nat (length bs) <= lo) by (rewrite length_map; pose proof DLE as X; unfold zlength in X; lia).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof BA as BA1.
    carve_frame 112%nat ST.
    do 14 zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (INV1 : INV mx);
      [ split; [exact BA1|]; split;
        [ eapply unpoisoned_munch; [exact UNP0| exact MU|];
          cbn [disjoint_from]; split; [| exact I]; left; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia |];
        split; [eexists; exact FR|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM| exact MI] |]
    end.
    zstep. br K0.
    - (* [comment removed for export] *) zstep. zstep. apply vu_epi; [exact INV1| right; reflexivity].
    - zstep. br K1.                                            (* [comment removed for export] *)
      do 15 zstep.
      eapply (vu_loop (S (Z.to_nat n)) 0); [lia| lia| exact INV1].
  Qed.
End P.

(* [comment removed for export] *)
Definition validate_utf8_stmtB : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z),
    bytes_at bsegs m D (map (Z_to_bv 8) pl) -> unpoisoned m D (D + zlength pl) ->
    D mod 8 = 0 -> 0 < D -> D + zlength pl + 8 <= KEND -> zlength pl < 2 ^ 26 ->
    lo <= bv_unsigned sp - VUTF8_STACK -> KHIGH <= lo -> D + zlength pl <= lo ->
    rt_got m -> rt_shbase m ->
    rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG D (zlength pl) -> rng RNG (shad D) (nshad (zlength pl)) ->
    stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
    a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength pl) ->
    evtF bsegs RNG (vu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVUTF8) fc None m (seg_rom bsegs)).

Theorem validate_utf8_proofB : validate_utf8_stmtB.
Proof.
  unfold validate_utf8_stmtB, VUTF8_STACK. intros until lo. intros BA UNP D8 D0 DE NLT LO CLO DLE GOT SHB RI RSTK RD RSH ST MI -> ->.
  eapply vu_body; eassumption.
Qed.
End CANSEC1.
Print Assumptions validate_utf8_proofB.
