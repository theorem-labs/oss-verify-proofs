(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AI_globals2 AM_strlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition strlen_icp_entry : Z := 0x43244.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition strlen_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A SB : Z) (str slack ws : list byte) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' A (str ++ Z_to_bv 8 0 :: slack)
    /\ icp_globals asegs m' SB /\ icp_globals2 asegs m'
    /\ shadow_window asegs m' SB A (Z.of_nat (length str) + 1) ws.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (A SB : Z) (str slack ws : list byte) (lo : Z).
Notation LEN := (Z.of_nat (length str)).
Notation n := (Z.of_nat (length str) + 1).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2160.
Hypothesis HLEN : (length str <= 63)%nat.
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis HA : 0 < A.
Hypothesis HAN : A + n + Z.of_nat (length slack) < 2^47.
Hypothesis HDISJ : A + n + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= A.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB A n - shw_lo SB A.
Hypothesis RC : range_clean SB A n ws.
Hypothesis SBR : 2^24 <= SB < 2^32.
Hypothesis PSH : forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k).
Hypothesis PSTR : forall a k, A <= a -> a + Z.of_nat k <= A + n + Z.of_nat (length slack) -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 2160 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).

Notation POST := (strlen_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A SB str slack ws m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2144)).
Notation g1 := (Z.shiftr A 3).
Notation g2 := (Z.shiftr (A + n + -1) 3).
(* [comment removed for export] *)
Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp (Z_to_bv 64 (LEN + 1)) x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 A) (Z_to_bv 64 0x13f6a8) (Z_to_bv 64 (bv_unsigned sp + -2136)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Ltac hideD := hideH HDISJ.
Ltac unhideD := unfold hidden in HDISJ.

Definition MINV (m0 : mem) : Prop :=
  mem_inv asegs m0 /\ munch [(bv_unsigned sp - 2160, bv_unsigned sp)] m m0 /\ wmono asegs m m0 /\
  stk asegs m0 lo (bv_unsigned sp + -64) /\
  rw_cells asegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  bytes_at asegs m0 A (str ++ Z_to_bv 8 0 :: slack) /\
  icp_globals asegs m0 SB /\ icp_globals2 asegs m0 /\ bytes_at asegs m0 (shw_lo SB A) ws.
Ltac open_minv H := destruct H as (MI & MU & WM & SK & FR & STR & G & G2 & SHB).

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= A < 8 * g1 + 8 /\ 8 * g2 <= A + n + -1 < 8 * g2 + 8 /\
  shw_lo SB A <= SB + g1 /\ SB + g1 < shw_lo SB A + 8 /\ shw_lo SB A mod 8 = 0 /\
  shw_hi SB A n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB A n /\ shw_hi SB A n mod 8 = 0 /\
  shw_lo SB A + 8 <= shw_hi SB A n.
Proof. exact (shw_geom SB A n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma sli_tail : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  MINV m0 ->
  evtA asegs P POST (ST 0x432fc m0 x1 x5 x6 x7 (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. open_minv IV. hideD.
  stepA. (* [comment removed for export] *) do 8 stepA. (* [comment removed for export] *) stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  apply evtA_done. unfold strlen_icp_post.
  do 15 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  split; [exact SHB | exact SHL].
Qed.

(* [comment removed for export] *)
Lemma sli_loop : forall k (Q : machine_state -> Prop) m0 j x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  Z.to_nat (g2 - j) = k -> g1 <= j < g2 ->
  bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P Q (ST 0x43404 m0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 x21 x28 x29 x30 x31) ->
  evtA asegs P Q (ST 0x433f4 m0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + g2)) x13 x14 x15 x16 x17 x21 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hj SHB CONT; pose proof GEO as GE; [lia|]. hideD.
  pose proof (range_clean_inner SB A n ws j RC ltac:(lia)) as Hb.
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + j - shw_lo SB A) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + g2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma sli_join : forall m0 x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  MINV m0 ->
  evtA asegs P POST (ST 0x43404 m0 x1 x5 x6 x7 (Z_to_bv 64 0) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) x13 x14 x15 x16 x17 (Z_to_bv 64 LEN) x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. hideD.
  zstepA. zstepA. (* [comment removed for export] *) if_true.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply sli_tail; exact IV.
Qed.

(* [comment removed for export] *)
Lemma sli_slow : forall m0 x1 x5 x6 x7 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  MINV m0 ->
  evtA asegs P POST (ST 0x433d4 m0 x1 x5 x6 x7 (Z_to_bv 64 LEN) (Z_to_bv 64 (SB + g1)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (A + n + -1)) x14 x15 x16 x17 x21 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. hideD.
  destruct (RC g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + g2 - shw_lo SB A) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *)
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
  clear MI MU WM SK FR STR G G2.
  if_cases KG; zify_cond KG.
  - replace (SB + g1) with (SB + g2) by lia. eapply sli_join; exact IV'.
  - eapply (sli_loop (Z.to_nat (g2 - g1)) _ m0 g1); [reflexivity | lia | exact SHB |].
    eapply sli_join; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma sli_check : forall m0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  MINV m0 ->
  evtA asegs P POST
    (MS (mkR x1 SP' gp tp x5 x6 x7 sp (Z_to_bv 64 1) (Z_to_bv 64 LEN) x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 A) s3 s4 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x43294) fc None m0 (seg_rom asegs)).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEO as GE. hideD.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  icp_globals_open G. pose proof (ig2_cflags asegs m0 G2) as GCF. pose proof (ig2_intercept_strlen asegs m0 G2) as GIS.
  stepA. (* [comment removed for export] *) if_false.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) cbv beta.
  stepA. (* [comment removed for export] *) if_false.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. (* [comment removed for export] *) if_cases K2; zify_cond K2. { exfalso. lia. }
  stepA. stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) replace (LEN + A) with (A + n + -1) by lia.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + A ≫ 3)) with (shw_lo SB A).
  replace (al8 (SB + (A + n + -1) ≫ 3)) with (shw_hi SB A n - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read asegs _ _ _ 0 8 SHB ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read asegs _ _ _ (shw_hi SB A n - 8 - shw_lo SB A) 8 SHB ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB A + (shw_hi SB A n - 8 - shw_lo SB A)) with (shw_hi SB A n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR STR SHB GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI GCF GIS.
  if_cases KW.
  - eapply sli_slow; exact IV'.
  - eapply sli_tail; exact IV'.
Qed.

Lemma strlen_icp_body : forall x10,
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  x10 = Z_to_bv 64 A ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals asegs m SB -> icp_globals2 asegs m -> bytes_at asegs m (shw_lo SB A) ws ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strlen_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros x10 SK MI -> STR G G2 SHB. unfold strlen_icp_entry.
  pose proof GEO as GE.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (MU : munch [(bv_unsigned sp - 2160, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  pose proof (conj STR SHB) as RO. clear STR SHB. pose proof G2 as G2o.
  hideD. carve_frame 64%nat SK.
  do 11 stepA.   (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport asegs) in G; [ | exact MU | exact WM | cbn; lia ];
    eapply (icp_globals2_transport asegs) in G2; [ | exact MU | exact WM | cbn; lia | cbn; lia ]
  end.
  pose proof G as G'. icp_globals_open G. pose proof (ig2_strlen asegs _ G2) as GRS.
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) stepA. stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  cbv beta. zstepA. (* [comment removed for export] *) if_false.
  (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  destruct (stk_split asegs _ lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  carve_frame 16%nat SKlo.
  stepA. stepA. stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  cbv beta. stepA. (* [comment removed for export] *) if_false.
  stepA. stepA. stepA. stepA. (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2160) _ |- _ => release_frame H SKlo (bv_unsigned sp + -2144) end.
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -2144) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ H SKhi ltac:(lia)) as SK; clear H SKhi end.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  unhideD.
  destruct RO as [STR SHB].
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (bytes_at_transport asegs) in STR; [ | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia ];
    eapply (bytes_at_transport asegs) in SHB; [ | exact MU | cbn; lia ] end.
  callA strlen_spec.
  3:{ rewrite UA. exact STR. }
  1:{ intros a k H1 H2. rewrite ?UA in H1. rewrite ?UA in H2. apply PSTR; lia. }
  1:{ exact PIMG. }
  1:{ exact NONUL. }
  1:{ rewrite UA. exact PAD. }
  1:{ assumption. }
  ret_pc_lit. rewrite ?UA in *. hideD.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals2_transport asegs) in G2o; [ | exact MU | exact WM | cbn; lia | cbn; lia ] end.
  eapply sli_check.
  lazymatch goal with |- MINV ?mx =>
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact SK|];
    split; [assumption|]; split; [assumption|];
    split; [ unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
               A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL;
             repeat (split; [assumption|]); lia |];
    split; [assumption| assumption] end.
Qed.
End Walk.

Lemma strlen_icp_small_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A SB : Z) (str slack ws : list byte) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2160 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 A -> (length str <= 63)%nat -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < A -> A + (Z.of_nat (length str) + 1) + Z.of_nat (length slack) < 2^47 ->
  (A + (Z.of_nat (length str) + 1) + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= A) ->
  bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals asegs m SB -> icp_globals2 asegs m ->
  shadow_window asegs m SB A (Z.of_nat (length str) + 1) ws -> range_clean SB A (Z.of_nat (length str) + 1) ws ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A (Z.of_nat (length str) + 1) -> P (Z_to_bv 64 a, k)) ->
  (forall a k, A <= a -> a + Z.of_nat k <= A + (Z.of_nat (length str) + 1) + Z.of_nat (length slack) -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, bv_unsigned sp - 2160 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (strlen_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A SB str slack ws m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strlen_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros SK LOC LO MI HA0 HLEN NONUL PAD HA HAN HDISJ STR G G2 SHW RC PSH PSTR PIMG PSTK.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  destruct SHW as [SHB SHL].
  eapply strlen_icp_body; eassumption.
Qed.
End RC__2.
