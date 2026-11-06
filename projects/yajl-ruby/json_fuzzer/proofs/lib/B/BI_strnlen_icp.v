(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2 BI_region_is_poisoned BM_strnlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition strnlen_icp_entry : Z := 0x432e4.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition strnlen_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A SB : Z) (str slack ws : list byte) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 4384, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ bytes_at bsegs m' A (str ++ Z_to_bv 8 0 :: slack)
    /\ icp_globals bsegs m' SB /\ icp_globals2 bsegs m'
    /\ shadow_window bsegs m' SB A (Z.of_nat (length str) + 1) ws.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (A cnt SB : Z) (str slack ws : list byte) (lo : Z).
Notation LEN := (Z.of_nat (length str)).
Notation n := (Z.of_nat (length str) + 1).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 4384.
Hypothesis HCNT : n <= cnt < 2^63.   (* [comment removed for export] *)
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis HN40 : n < 2^40.
Hypothesis RIM : range_in_mem SB A n.
Hypothesis HAN : A + n + Z.of_nat (length slack) < 2^47.
Hypothesis HDISJ : A + n + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= A.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB A n - shw_lo SB A.
Hypothesis RC : range_clean SB A n ws.
Hypothesis SBR : 2^24 <= SB < 2^32.
Hypothesis G20 : icp_globals2 bsegs m.
Hypothesis PSH : forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k).
Hypothesis PSTR : forall a k, A <= a -> a + Z.of_nat k <= A + n + Z.of_nat (length slack) -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 4384 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).

Notation POST := (strnlen_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A SB str slack ws m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2144)).
Notation g1 := (Z.shiftr A 3).
Notation g2 := (Z.shiftr (A + n + -1) 3).
Ltac hideD := hideH HDISJ; hideH RIM.
Ltac unhideD := unfold hidden in HDISJ, RIM.
Lemma BNDS : 0 < A /\ A + n < 2^47.
Proof. unfold range_in_mem in RIM. lia. Qed.

(* [comment removed for export] *)
Notation ST pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
          x18 (Z_to_bv 64 cnt) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

Definition MINV (m0 : mem) : Prop :=
  mem_inv bsegs m0 /\ munch [(bv_unsigned sp - 4384, bv_unsigned sp)] m m0 /\ wmono bsegs m m0 /\
  stk bsegs m0 lo (bv_unsigned sp + -64) /\
  rw_cells bsegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  bytes_at bsegs m0 A (str ++ Z_to_bv 8 0 :: slack) /\
  icp_globals bsegs m0 SB /\ bytes_at bsegs m0 (shw_lo SB A) ws.
Ltac open_minv H := destruct H as (MI & MU & WM & SK & FR & STR & G & SHB).

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= A < 8 * g1 + 8 /\ 8 * g2 <= A + n + -1 < 8 * g2 + 8 /\
  shw_lo SB A <= SB + g1 /\ SB + g1 < shw_lo SB A + 8 /\ shw_lo SB A mod 8 = 0 /\
  shw_hi SB A n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB A n /\ shw_hi SB A n mod 8 = 0 /\
  shw_lo SB A + 8 <= shw_hi SB A n.
Proof. pose proof BNDS. exact (shw_geom SB A n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma sni_tail : forall m0 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x433a8 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. open_minv IV. hideD.
  stepA. (* [comment removed for export] *) do 8 stepA. (* [comment removed for export] *) stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  unhideD. pose proof GEO as GE. pose proof BNDS as BN.
  pose proof G20 as G2. eapply (icp_globals2_transport bsegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ].
  apply evtA_done. unfold strnlen_icp_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  split; [exact SHB | exact SHL].
Qed.

(* [comment removed for export] *)
Lemma sni_loop : forall k (Q : machine_state -> Prop) m0 j x1 x5 x6 x7 x9 x10 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  Z.to_nat (g2 - j) = k -> g1 <= j < g2 ->
  bytes_at bsegs m0 (shw_lo SB A) ws ->
  evtA bsegs P Q (ST 0x4348c m0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31) ->
  evtA bsegs P Q (ST 0x4347c m0 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hj SHB CONT; pose proof GEO as GE; [lia|]. hideD.
  pose proof (range_clean_inner SB A n ws j RC ltac:(lia)) as Hb.
  pose proof (u8ro_read bsegs m0 (shw_lo SB A) ws (SB + j - shw_lo SB A) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + g2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma sni_join : forall m0 x1 x5 x6 x7 x9 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x4348c m0 x1 x5 x6 x7 x9 (Z_to_bv 64 LEN) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. hideD.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply sni_tail; exact IV.
Qed.

(* [comment removed for export] *)
Lemma sni_slow : forall m0 x1 x5 x6 x7 x9 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x43460 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 LEN) (Z_to_bv 64 (SB + g1)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (A + n + -1)) x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. hideD.
  destruct (RC g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read bsegs m0 (shw_lo SB A) ws (SB + g2 - shw_lo SB A) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?t) ?u)] =>
    change (Z.land (Z.b2z t) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (A + n + -1) 7)) end.
  rewrite (aip_last_clean k2 (A + n + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; lia]]).
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR STR G.
  if_cases KG; zify_cond KG.
  - replace (SB + g1) with (SB + g2) by lia. eapply sni_join; exact IV'.
  - eapply (sni_loop (Z.to_nat (g2 - g1)) _ m0 g1); [reflexivity | lia | exact SHB |].
    eapply sni_join; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma sni_small : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 -> n <= 64 ->
  evtA bsegs P POST (ST 0x4336c m0 x1 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn64. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. pose proof BNDS as BN. hideD.
  icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) replace (A + (LEN + 1)) with (A + n) by lia.
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + A ≫ 3)) with (shw_lo SB A).
  replace (al8 (SB + (A + n + -1) ≫ 3)) with (shw_hi SB A n - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read bsegs _ _ _ 0 8 SHB ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read bsegs _ _ _ (shw_hi SB A n - 8 - shw_lo SB A) 8 SHB ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB A + (shw_hi SB A n - 8 - shw_lo SB A)) with (shw_hi SB A n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR STR SHB GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply sni_slow; exact IV'.
  - eapply sni_tail; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma sni_big : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 -> 65 <= n ->
  evtA bsegs P POST (ST 0x43494 m0 x1 x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn65. open_minv IV.
  pose proof GEO as GE. pose proof BNDS as BN.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR. hideD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2144)) = bv_unsigned sp + -2144) by (apply unsigned_lit; lia).
  destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  pose proof G as Gc. icp_globals_open Gc.
  unhideH HDISJ.
  callA (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A n SB ws lo P).
  1:{ rewrite USP. exact SKlo. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ exact MI. }
  1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ lia. } 1:{ unhideD. exact RIM. } 1:{ exact G. }
  1:{ split; [exact SHB | exact SHL]. } 1:{ exact RC. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ exact PIMG. } 1:{ exact PSH. }
  ret_pc_lit. hideD.
  lazymatch goal with H : stk bsegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk bsegs ?mx _ (bv_unsigned sp + -64) |- _ =>
    pose proof (stk_merge bsegs _ _ _ _ SKlo2 H ltac:(lia)) as SK2; clear H SKlo2 end.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply sni_tail. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact SK2|].
  split; [eassumption|]. split; [eassumption|].
  split. { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
             A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
           repeat (split; [assumption|]). lia. }
  eassumption.
Qed.

(* [comment removed for export] *)
Lemma sni_check : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x43334 m0 x1 x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 A) x20 x21 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV. pose proof BNDS as BN. hideD.
  pose proof G20 as G2. unhideD.
  eapply (icp_globals2_transport bsegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ]. hideD.
  pose proof (ig2_cflags bsegs m0 G2) as GCF. pose proof (ig2_intercept_strlen bsegs m0 G2) as GIS.
  stepA. (* [comment removed for export] *) if_false.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) cbv beta.
  stepA. (* [comment removed for export] *) if_false.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K0; zify_cond K0.
  { (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) rewrite not64 by lia.
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. 2:{ exfalso. lia. }
    zstepA. zstepA. zstepA. (* [comment removed for export] *)
    clear MI MU WM SK FR STR G SHB GCF GIS.
    if_cases K2; zify_cond K2.
    - assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
      zstepA. (* [comment removed for export] *) if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
      eapply evtA_eq; [ | eapply sni_big; [exact IV' | lia] ]. cbv delta [mkR]. repeat first [ reflexivity | progress f_equal | lia ].
    - assert (n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
      eapply evtA_eq; [ | eapply sni_small; [exact IV' | lia] ]. cbv delta [mkR]. repeat first [ reflexivity | progress f_equal | lia ]. }
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR STR G SHB GCF GIS.
  if_cases K2; zify_cond K2.
  - assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
    zstepA. (* [comment removed for export] *) if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    eapply sni_big; [exact IV' | lia].
  - assert (n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
    eapply sni_small; [exact IV' | lia].
Qed.

Lemma strnlen_icp_body : forall x10 x11,
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  x10 = Z_to_bv 64 A -> x11 = Z_to_bv 64 cnt ->
  bytes_at bsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals bsegs m SB -> bytes_at bsegs m (shw_lo SB A) ws ->
  evtA bsegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strnlen_icp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros x10 x11 SK MI -> -> STR G SHB. unfold strnlen_icp_entry.
  pose proof GEO as GE. pose proof BNDS as BN. pose proof G20 as G2.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (MU : munch [(bv_unsigned sp - 4384, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  pose proof (conj STR SHB) as RO. clear STR SHB.
  hideD. carve_frame 64%nat SK.
  do 11 stepA.   (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport bsegs) in G; [ | exact MU | exact WM | cbn; lia ];
    eapply (icp_globals2_transport bsegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ]
  end.
  pose proof G as G'. icp_globals_open G. pose proof (ig2_strnlen bsegs _ G2) as GRS.
  (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  destruct (stk_split bsegs _ lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  carve_frame 16%nat SKlo.
  stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  cbv beta. stepA. (* [comment removed for export] *) if_false.
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -2160) _ |- _ => release_frame H SKlo (bv_unsigned sp + -2144) end.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2144)) = bv_unsigned sp + -2144) by (apply unsigned_lit; lia).
  unhideD. destruct RO as [STR SHB].
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (bytes_at_transport bsegs) in STR; [ | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia ];
    eapply (bytes_at_transport bsegs) in SHB; [ | exact MU | cbn; lia ] end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (G2c : icp_globals2 bsegs mx) by (eapply (icp_globals2_transport bsegs); [exact G20 | exact MU | exact WM | cbn; lia | cbn; lia ]) end.
  callA (strnlen_cstr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A cnt SB str slack ws lo P).
  1:{ rewrite USP. lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -2144) |- _ => exact H end. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ assumption. }
  1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ lia. } 1:{ exact RIM. } 1:{ lia. }
  1:{ rewrite USP. lia. }
  1:{ exact STR. }
  1:{ unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
        A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
      repeat (split; [assumption|]). lia. }
  1:{ exact G2c. }
  1:{ split; [exact SHB | exact SHL]. } 1:{ exact RC. }
  1:{ exact PSH. } 1:{ exact PSTR. } 1:{ exact PIMG. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  ret_pc_lit. hideD.
  lazymatch goal with H : stk bsegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk bsegs ?mx _ (bv_unsigned sp + -64) |- _ =>
    pose proof (stk_merge bsegs _ _ _ _ SKlo2 H ltac:(lia)) as SK; clear H SKlo2 end.
  eapply sni_check.
  split. 1: assumption. split. 1: assumption. split. 1: assumption. split. 1: exact SK.
  split. 1: eassumption. split. 1: assumption. split. 2: assumption.
  unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
    A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
  repeat (split; [assumption|]). lia.
Qed.
End Walk.

Lemma strnlen_icp_cstr_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A cnt SB : Z) (str slack ws : list byte) (lo : Z) (P : acc -> Prop),
  let n := Z.of_nat (length str) + 1 in
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4384 -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 cnt ->
  n <= cnt < 2^63 -> ~ In (Z_to_bv 8 0) str -> (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  n < 2^40 -> range_in_mem SB A n -> A + n + Z.of_nat (length slack) < 2^47 ->
  (A + n + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= A) ->
  bytes_at bsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals bsegs m SB -> icp_globals2 bsegs m ->
  shadow_window bsegs m SB A n ws -> range_clean SB A n ws ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, A <= a -> a + Z.of_nat k <= A + n + Z.of_nat (length slack) -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, bv_unsigned sp - 4384 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (strnlen_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A SB str slack ws m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strnlen_icp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until P. cbv zeta. intros SK LOC LO MI HA0 HA1 HCNT NONUL PAD HN40 RIM HAN HDISJ STR G G2 SHW RC PSH PSTR PIMG PSTK.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  destruct SHW as [SHB SHL].
  eapply strnlen_icp_body; eassumption.
Qed.
End RC__2.
