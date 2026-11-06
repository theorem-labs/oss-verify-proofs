(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AU_vutf8_ck.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Section CANSEC1. Context {rc : runConstT}.
Definition AVUTF8 : Z := 0xb6970.
Definition VUTF8_STACK : Z := 112.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z).
  Notation n := (zlength pl).
  Notation SP := (bv_unsigned sp).
  Hypothesis BA : bytes_at asegs m D (map (Z_to_bv 8) pl).
  Hypothesis UNP0 : unpoisoned m D (D + n).
  Hypothesis D8 : D mod 8 = 0.
  Hypothesis DLO : 0 <= D.
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
    rw_cells asegs m1 (SP + -112) [CB 8 junk8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition INV (m1 : word -> option byte) : Prop :=
    bytes_at asegs m1 D bs /\ unpoisoned m1 D (D + n) /\ FRAME m1 /\ stk asegs m1 lo (SP + -112)
    /\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.

  (* [comment removed for export] *)
  Definition vu_post : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ (a0' = Z_to_bv 64 0 \/ a0' = Z_to_bv 64 1)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP.

  (* [comment removed for export] *)
  Lemma payload_rdx : forall m1 k, bytes_at asegs m1 D bs -> 0 <= k < n ->
    exists b : byte, ov_read_bytes asegs m1 (wa (D + k)) 1 = Some [b].
  Proof.
    intros m1 k B Hk. unfold zlength in Hk.
    pose proof (bytes_at_read asegs m1 D bs k 1 B ltac:(lia) ltac:(rewrite length_map; lia)) as R.
    destruct (skipn (Z.to_nat k) bs) as [|b r] eqn:E.
    { exfalso. assert (L : length (skipn (Z.to_nat k) bs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn, length_map in L. lia. }
    exists b. exact R.
  Qed.

  (* [comment removed for export] *)
  Notation GST pc mm x0 x1 xa0 xa3 xa4 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -112)) gp tp (Z_to_bv 64 128) (Z_to_bv 64 27) (Z_to_bv 64 2147450880) x0 x1 xa0 (Z_to_bv 64 D) (Z_to_bv 64 n) xa3 xa4
             (Z_to_bv 64 192) (Z_to_bv 64 (-65)) (Z_to_bv 64 224) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
             (Z_to_bv 64 7) (Z_to_bv 64 240) (Z_to_bv 64 (-1114112)) (Z_to_bv 64 (-1048576)))
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma vu_epi : forall m1 v (y5 y6 y7 x0 x1 ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31 : word),
    INV m1 -> (v = 0 \/ v = 1) ->
    evtF asegs RNG vu_post
      (MS (mkR ra (Z_to_bv 64 (SP + -112)) gp tp y5 y6 y7 x0 x1 (Z_to_bv 64 v) ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb6cf4) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 v y5 y6 y7 x0 x1 ya1 ya2 xa3 xa4 ya5 ya6 ya7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y28 y29 y30 y31 (BA1 & UNP1 & [junk8 FR] & ST & MU & WM & MI) HV.
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
  (* [comment removed for export] *)
  Ltac ckrd UNP A b RDb CKb :=
    destruct (unpoisoned_check_rd asegs _ D (D + n) A 1 UNP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDb & CKb);
    unfold shad, ASHOFF in RDb; replace (2147450880 + Z.shiftr A 3) with (Z.shiftr A 3 + 2147450880) in RDb by lia.
  (* [comment removed for export] *)
  Ltac ckcut L A bb CKb :=
    eapply evtF_cut;
    [ eapply L with (b := bb);
      [ lia
      | first [ exact CKb | lazymatch goal with |- _ \/ (_ /\ ?P mod 8 + _ - _ < _) => replace P with A by lia end; exact CKb ] ]
    | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO; subst ms' ].

  Ltac br K := if_cases K; try (zify_cond K; rewrite ?unsigned_lit in K by lia).
  (* [comment removed for export] *)
  Ltac fin NEXT FALSE INV1 :=
    first [ pc_is 0xb69e8; apply NEXT; lia
          | pc_is 0xb6cf0; apply FALSE
          | pc_is 0xb6cf4; apply vu_epi; [exact INV1| left; reflexivity]
          | pc_is 0xb69e4; zstep; apply NEXT; lia ].
  Lemma vu_loop : forall fuel pos m1 (x0 xa0 xa3 xa4 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : word),
    Z.of_nat fuel > n - pos -> 0 <= pos < n -> INV m1 ->
    evtF asegs RNG vu_post (GST 0xb69f0 m1 x0 (Z_to_bv 64 pos) xa0 xa3 xa4 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
  Proof.
    induction fuel as [|fuel IH]; intros pos m1 x0 xa0 xa3 xa4 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 FU PR INV1; [lia|].
    pose proof INV1 as (BA1 & UNP1 & FR & ST & MU & WM & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. unfold KEND in DE'.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    (* [comment removed for export] *)
    assert (NEXT : forall q (y1 ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word), pos < q <= n ->
              evtF asegs RNG vu_post (GST 0xb69e8 m1 (Z_to_bv 64 q) y1 ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)).
    { intros q y1 ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 Hq.
      zstep. zstep. if_cases Kq; zify_cond Kq; rewrite ?unsigned_lit in Kq by lia.
      - zstep. zstep. apply vu_epi; [exact INV1| right; reflexivity].
      - apply IH; [lia| lia| exact INV1]. }
    (* [comment removed for export] *)
    assert (FALSE : forall (y0 y1 ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word),
              evtF asegs RNG vu_post (GST 0xb6cf0 m1 y0 y1 ya0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)).
    { intros. zstep. apply vu_epi; [exact INV1| left; reflexivity]. }
    (* [comment removed for export] *)
    assert (SLOW1 : forall (y0 ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : word),
              evtF asegs RNG vu_post (GST 0xb6b0c m1 y0 (Z_to_bv 64 pos) (Z_to_bv 64 (D + pos)) ya3 ya4 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11)).
    { intros.
      destruct (payload_rdx m1 pos BA1 ltac:(lia)) as [c0 R0].
      ckrd UNP1 (D + pos) b RDb CKb. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b67bc (D + pos) b CKb. clear RDb CKb.
      zstep. zstep. br K; try fin NEXT FALSE INV1.          (* [comment removed for export] *)
      zstep. zstep. zstep. br K2; try fin NEXT FALSE INV1.    (* [comment removed for export] *)
      { (* [comment removed for export] *)
        zstep. zstep. br K3; try fin NEXT FALSE INV1.        (* [comment removed for export] *)
        { (* [comment removed for export] *)
          zstep. zstep. br K4; try fin NEXT FALSE INV1.      (* [comment removed for export] *)
          zstep. zstep. br Kb4; try fin NEXT FALSE INV1.      (* [comment removed for export] *)
          destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1]. destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
          destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
          zstep. ckrd UNP1 (D + pos + 1) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b68a0 (D + pos + 1) b1 CKb1. clear RDb1 CKb1.
          zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.   (* [comment removed for export] *)
          zstep. ckrd UNP1 (D + pos + 2) b2 RDb2 CKb2. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b68c0 (D + pos + 2) b2 CKb2. clear RDb2 CKb2.
          zstep. zstep. br Kc2; try fin NEXT FALSE INV1.          (* [comment removed for export] *)
          zstep. ckrd UNP1 (D + pos + 3) b3 RDb3 CKb3. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b68dc (D + pos + 3) b3 CKb3. clear RDb3 CKb3.
          zstep. zstep. br Kc3; try fin NEXT FALSE INV1.          (* [comment removed for export] *)
          do 6 zstep. zstep. br Kc4; try fin NEXT FALSE INV1.     (* [comment removed for export] *)
          zstep. fin NEXT FALSE INV1. }
        (* [comment removed for export] *)
        zstep. zstep. br Kb3; try fin NEXT FALSE INV1.        (* [comment removed for export] *)
        destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1]. destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2].
        zstep. ckrd UNP1 (D + pos + 1) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b6828 (D + pos + 1) b1 CKb1. clear RDb1 CKb1.
        zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.     (* [comment removed for export] *)
        zstep. ckrd UNP1 (D + pos + 2) b2 RDb2 CKb2. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b6848 (D + pos + 2) b2 CKb2. clear RDb2 CKb2.
        zstep. zstep. br Kc2; try fin NEXT FALSE INV1.            (* [comment removed for export] *)
        do 6 zstep. zstep. br Kc3; try fin NEXT FALSE INV1.       (* [comment removed for export] *)
        zstep. br Kc4; try fin NEXT FALSE INV1.                   (* [comment removed for export] *)
        zstep. zstep. br Kc5; try fin NEXT FALSE INV1.            (* [comment removed for export] *)
        zstep. fin NEXT FALSE INV1. }
      (* [comment removed for export] *)
      zstep. zstep. br Kb2; try fin NEXT FALSE INV1.          (* [comment removed for export] *)
      destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
      zstep. ckrd UNP1 (D + pos + 1) b1 RDb1 CKb1. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b67ec (D + pos + 1) b1 CKb1. clear RDb1 CKb1.
      zstep. zstep. zstep. br Kc1; try fin NEXT FALSE INV1.       (* [comment removed for export] *)
      zstep. zstep. br Kc2; try fin NEXT FALSE INV1.              (* [comment removed for export] *)
      zstep. fin NEXT FALSE INV1. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. br K16.                               (* [comment removed for export] *)
    all: try (pc_is 0xb6b0c; apply SLOW1).
    (* [comment removed for export] *)
    ckrd UNP1 (D + pos) b0 RDb0 CKb0. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b66ac (D + pos) b0 CKb0. clear RDb0 CKb0.
    zstep. ckrd UNP1 (D + pos + 7) b7 RDb7 CKb7. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b66c0 (D + pos + 7) b7 CKb7. clear RDb7 CKb7.
    destruct (payload_rdx m1 (pos + 0) BA1 ltac:(lia)) as [c0 R0]. destruct (payload_rdx m1 (pos + 1) BA1 ltac:(lia)) as [c1 R1].
    destruct (payload_rdx m1 (pos + 2) BA1 ltac:(lia)) as [c2 R2]. destruct (payload_rdx m1 (pos + 3) BA1 ltac:(lia)) as [c3 R3].
    zstep. zstep. zstep. zstep. clear R0 R1 R2 R3.
    destruct (payload_rdx m1 (pos + 4) BA1 ltac:(lia)) as [c4 R4]. destruct (payload_rdx m1 (pos + 5) BA1 ltac:(lia)) as [c5 R5].
    destruct (payload_rdx m1 (pos + 6) BA1 ltac:(lia)) as [c6 R6]. destruct (payload_rdx m1 (pos + 7) BA1 ltac:(lia)) as [c7 R7].
    zstep. ckrd UNP1 (D + pos + 8) b8 RDb8 CKb8. zstep. zstep. zstep. rewrite sxb_sval.
    zstep. zstep. zstep. zstep. clear R4 R5 R6 R7.
    ckcut ckb_b66f4 (D + pos + 8) b8 CKb8. clear RDb8 CKb8.
    zstep. ckrd UNP1 (D + pos + 15) b15 RDb15 CKb15. zstep. zstep. zstep. rewrite sxb_sval. ckcut ckb_b6708 (D + pos + 15) b15 CKb15. clear RDb15 CKb15.
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
    all: first [ pc_is 0xb69e8; apply NEXT; lia | pc_is 0xb6b0c; apply SLOW1 ].
  Qed.

  (* [comment removed for export] *)
  Lemma vu_body : stk asegs m lo SP -> mem_inv asegs m ->
    evtF asegs RNG vu_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVUTF8) fc None m (seg_rom asegs)).
  Proof.
    intros ST MI. unfold AVUTF8.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CLO as CLO'. unfold KHIGH in CLO'. pose proof DE as DE'. unfold KEND in DE'.
    assert (N0 : 0 <= n) by (unfold zlength; lia).
    assert (BL : D + Z.of_nat (length bs) <= lo) by (rewrite length_map; pose proof DLE as X; unfold zlength in X; lia).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
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
    - do 14 zstep.
      eapply (vu_loop (S (Z.to_nat n)) 0); [lia| lia| exact INV1].
  Qed.
End P.

(* [comment removed for export] *)
Definition validate_utf8_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (pl : list Z) (lo : Z),
    bytes_at asegs m D (map (Z_to_bv 8) pl) -> unpoisoned m D (D + zlength pl) ->
    D mod 8 = 0 -> 0 <= D -> D + zlength pl + 8 <= KEND -> zlength pl < 2 ^ 26 ->
    lo <= bv_unsigned sp - VUTF8_STACK -> KHIGH <= lo -> D + zlength pl <= lo ->
    rt_got m -> rt_shbase m ->
    rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG D (zlength pl) -> rng RNG (shad D) (nshad (zlength pl)) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength pl) ->
    evtF asegs RNG (vu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVUTF8) fc None m (seg_rom asegs)).

Theorem validate_utf8_proofA : validate_utf8_stmtA.
Proof.
  unfold validate_utf8_stmtA, VUTF8_STACK. intros until lo. intros BA UNP D8 D0 DE NLT LO CLO DLE GOT SHB RI RSTK RD RSH ST MI -> ->.
  eapply vu_body; eassumption.
Qed.
End CANSEC1.
Print Assumptions validate_utf8_proofA.
