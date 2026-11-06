(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_memcpy.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BP_policy BI_shadow BI_region_is_poisoned BI_memcpy_icp1 BI_memcpy_icp BI_memcpy_icp0 BP_mjx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition fwritex_entry := 0x98838%Z.

(* [comment removed for export] *)
Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
  [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

(* [comment removed for export] *)
Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
    (B : Z) (content junk : list byte) : Prop :=
  rw_cells bsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
                                          (B + Z.of_nat (length content)) j2 lbfw)
  /\ rw_cells bsegs m B [CB (length content) content; CB (length junk) junk]
  /\ Z.land (bv_unsigned fl0) 32 = 0%Z                       (* [comment removed for export] *)
  /\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z        (* [comment removed for export] *)
  /\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z   (* [comment removed for export] *)
  /\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

(* [comment removed for export] *)
Definition FWX_DEPTH : Z := 2304.
Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at bsegs m' S bs
    /\ mjx m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
  (9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64)%Z with 18446744073709551616%Z in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition in_stackw (A n : Z) : Prop := A_CEIL <= A /\ A + n < A_STK_HI.
Definition dst_loc (D n : Z) : Prop := in_stackw D n \/ (0x5d0810 <= D /\ D + n <= 0x603000).
Definition src_loc (S n : Z) : Prop := in_stackw S n \/ (0x10000 <= S /\ S + n <= 0x21000).

End RC__1.
Open Scope Z_scope.
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Pol.
Variable P : acc -> Prop.
Hypothesis PSTK : POL_STACK P.
Hypothesis PIMG : POL_IMG P.
Hypothesis PHSH : POL_HSH P.
Hypothesis PLSH : POL_LSH P.
Hypothesis PNUL : POL_NUL P.

(* [comment removed for export] *)
Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at bsegs m' (bv_unsigned a1) src
    /\ mjx m'.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte) (lo : Z),
  bytes_at bsegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells bsegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (0 < D)%Z -> (D + bv_unsigned a2 < 2^47)%Z -> (0 < bv_unsigned a1)%Z -> (bv_unsigned a1 + bv_unsigned a2 < 2^47)%Z -> (bv_unsigned a2 < 2^40)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (A_CEIL <= lo)%Z -> (lo <= bv_unsigned sp - 2240)%Z -> (bv_unsigned sp <= A_STK_HI)%Z ->
  mjx m ->
  dst_loc D (bv_unsigned a2) -> (bv_unsigned a2 = 0 \/ src_loc (bv_unsigned a1) (bv_unsigned a2))%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (D + bv_unsigned a2 <= lo \/ bv_unsigned sp <= D)%Z ->
  evtA bsegs P (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52b50) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros SRC LEN DST HD HDN HS HSN HN SEP MI SK LOC LO SPHI MJ DL LOCS HJS HJD.
  unfold A_CEIL, A_STK_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1. cbn in R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  set (S := bv_unsigned a1) in *. set (n := bv_unsigned a2) in *.
  assert (Ea1 : a1 = Z_to_bv 64 S) by (subst S; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Ea2 : a2 = Z_to_bv 64 n) by (subst n; rewrite Z_to_bv_bv_unsigned; reflexivity).
  stepA. (* [comment removed for export] *)
  destruct (Z.eq_dec n 0) as [N0 | N1].
  - (* [comment removed for export] *)
    rewrite N0 in *.
    assert (src = []) as -> by (destruct src; [reflexivity| cbn in LEN; lia]).
    assert (junk = []) as -> by (destruct DST as [[W _] _]; cbn in W; destruct junk; [reflexivity| cbn in W; lia]).
    eapply evtA_mono.
    { eapply (memcpy_icp_zero_spec) with (SB := 0x7fff8000%Z) (lo := lo) (S := S) (D := D); try reflexivity.
      - exact SK. - unfold alloc_ceiling, sp_window_lo, stack_max_size; lia. - exact LO. - exact MI. - exact Ea1. - exact Ea2. - lia. - lia.
      - exact (mjx_g m MJ).
      - intros a k H1 H2. apply PSTK; lia.
      - exact PIMG. - exact PNUL. }
    cbv beta. intros ms' PO. unfold memcpy_icp0_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & SK').
    unfold memcpy_postZ. fold S. fold n. rewrite !N0. do 15 eexists. split; [reflexivity|].
    assert (MU2 : munch [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + 0)] m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x [X _]. split; [exact X| exact I]. }
    split; [exact MU2|]. split; [exact WM|]. split; [exact MI'|]. split; [exact SK'|].
    split. { change (Z.to_nat 0) with 0%nat. apply rw_cells_CB0; lia. }
    split. { split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia. }
    eapply mjx_transport; [exact MJ| exact MU| exact WM|].
    apply Forall_cons; [| apply Forall_nil]. unfold mjx_ok_iv, A_CEIL, A_STK_HI; cbn [fst snd]. left. lia.
  - (* [comment removed for export] *)
    destruct LOCS as [N0 | SL]; [lia|]. unfold dst_loc, src_loc, in_stackw, A_CEIL, A_STK_HI in DL, SL.
    assert (WD : exists wsD, shadow_window bsegs m 0x7fff8000 D n wsD /\ range_clean 0x7fff8000 D n wsD /\ range_in_mem 0x7fff8000 D n
                 /\ (forall a k, shw_lo 0x7fff8000 D <= a -> a + Z.of_nat k <= shw_hi 0x7fff8000 D n -> P (Z_to_bv 64 a, k))).
    { destruct DL as [[D1 D2] | [D1 D2]].
      - pose proof (stack_window_span D n D1 ltac:(lia) ltac:(unfold A_STK_HI; lia)) as (W1 & W2 & W3).
        destruct (mjx_stack_window m D n MJ D1 ltac:(lia) ltac:(unfold A_STK_HI; lia)) as [X Y]. eexists. split; [exact X|]. split; [exact Y|].
        split. { right. unfold A_HIGHEND_VAL. lia. } intros a k H1 H2. apply PHSH; lia.
      - destruct (mjx_statics_window m D n MJ D1 ltac:(lia) D2) as (ws & X & Y). exists ws. split; [exact X|]. split; [exact Y|].
        pose proof (shw_geom 0x7fff8000 D n ltac:(lia) ltac:(lia) ltac:(lia)) as GE; cbv zeta in GE.
        assert (0x7fffa000 <= shw_lo 0x7fff8000 D /\ shw_hi 0x7fff8000 D n <= 0x800b8600).
        { unfold shw_lo, shw_hi, al8 in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. split; Z.div_mod_to_equations; lia. }
        split. { left. lia. } intros a k H1 H2. apply PLSH; lia. }
    assert (WS : exists wsS, shadow_window bsegs m 0x7fff8000 S n wsS /\ range_clean 0x7fff8000 S n wsS /\ range_in_mem 0x7fff8000 S n
                 /\ (forall a k, shw_lo 0x7fff8000 S <= a -> a + Z.of_nat k <= shw_hi 0x7fff8000 S n -> P (Z_to_bv 64 a, k))).
    { destruct SL as [[S1 S2] | [S1 S2]].
      - pose proof (stack_window_span S n S1 ltac:(lia) ltac:(unfold A_STK_HI; lia)) as (W1 & W2 & W3).
        destruct (mjx_stack_window m S n MJ S1 ltac:(lia) ltac:(unfold A_STK_HI; lia)) as [X Y]. eexists. split; [exact X|]. split; [exact Y|].
        split. { right. unfold A_HIGHEND_VAL. lia. } intros a k H1 H2. apply PHSH; lia.
      - destruct (mjx_rodata_window0 m S n MJ S1 ltac:(lia) S2) as [X Y]. eexists. split; [exact X|]. split; [exact Y|].
        pose proof (shw_geom 0x7fff8000 S n ltac:(lia) ltac:(lia) ltac:(lia)) as GE; cbv zeta in GE.
        assert (0x7fffa000 <= shw_lo 0x7fff8000 S /\ shw_hi 0x7fff8000 S n <= 0x800b8600).
        { unfold shw_lo, shw_hi, al8 in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. split; Z.div_mod_to_equations; lia. }
        split. { left. lia. } intros a k H1 H2. apply PLSH; lia. }
    destruct WD as (wsD & SWD & RCD & RID & PD). destruct WS as (wsS & SWS & RCS & RIS & PS).
    pose proof (shw_geom 0x7fff8000 D n ltac:(lia) ltac:(lia) ltac:(lia)) as GD; cbv zeta in GD.
    pose proof (shw_geom 0x7fff8000 S n ltac:(lia) ltac:(lia) ltac:(lia)) as GS; cbv zeta in GS.
    assert (SHB : shw_hi 0x7fff8000 S n < 2^45 /\ shw_hi 0x7fff8000 D n < 2^45).
    { unfold shw_hi, al8 in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. split; Z.div_mod_to_equations; lia. }
    eapply evtA_mono.
    { eapply (memcpy_icp_spec) with (SB := 0x7fff8000%Z) (lo := lo) (wsS := wsS) (wsD := wsD) (S := S) (D := D) (n := n); try reflexivity.
      - exact SK. - unfold alloc_ceiling, sp_window_lo, stack_max_size; lia. - exact LO. - exact MI. - exact Ea1. - exact Ea2. - lia.
      - exact RIS. - exact RID. - lia. - lia. - exact SEP. - exact HJS. - exact HJD.
      - destruct DL as [[D1 D2]|[D1 D2]]; lia.
      - exact DST. - exact SRC. - exact LEN.
      - exact (mjx_g m MJ).
      - exact SWS. - exact RCS. - destruct DL as [[D1 D2]|[D1 D2]]; lia.
      - exact SWD. - exact RCD. - destruct DL as [[D1 D2]|[D1 D2]]; lia.
      - intros a k H1 H2. apply PSTK; lia.
      - exact PIMG.
      - intros a k H1 H2. destruct SL as [[S1 S2]|[S1 S2]]; [apply PSTK; lia | apply PIMG; lia].
      - intros a k H1 H2. destruct DL as [[D1 D2]|[D1 D2]]; [apply PSTK; lia | apply PIMG; lia].
      - exact PS. - exact PD. }
    cbv beta. intros ms' PO. unfold memcpy_icp_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & SK' & DST' & SRC' & G' & _).
    unfold memcpy_postZ. fold S. fold n. do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact SK'|]. split; [exact DST'|]. split; [exact SRC'|].
    eapply mjx_transport; [exact MJ| exact MU| exact WM|].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold mjx_ok_iv, A_CEIL, A_STK_HI; cbn [fst snd].
    + left. lia.
    + destruct DL as [[D1 D2]|[D1 D2]]; [left; lia | right; right; lia].
Qed.

(* [comment removed for export] *)
Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at bsegs m' S bs
    /\ mjx m'.

(* [comment removed for export] *)

End Pol.
End RC__2.
