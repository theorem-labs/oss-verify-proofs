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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AM_memset AI_region_is_poisoned.
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
Definition memset_icp_entry : Z := 0x53424.

End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memset_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c n SB : Z) (ws : list byte) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))]
    /\ icp_globals asegs m' SB
    /\ shadow_window asegs m' SB A n ws.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n SB : Z) (ws : list byte) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2224.
Hypothesis HC : bv_unsigned a1 mod 256 = c.
Hypothesis HN : 1 <= n < 2^40.
Hypothesis RIM : range_in_mem SB A n.
Hypothesis HA : 0 < A.
Hypothesis HAN : A + n < 2^47.
Hypothesis HDISJ : A + n <= lo \/ bv_unsigned sp <= A.
Hypothesis HGL : A + n <= 0xa4000 \/ 0xaee00 <= A.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB A n - shw_lo SB A.
Hypothesis RC : range_clean SB A n ws.
Hypothesis HSWD : shw_hi SB A n <= A \/ A + n <= shw_lo SB A.
Hypothesis SBR : 2^24 <= SB < 2^32.
Ltac hideD := hideH HDISJ; hideH HGL; hideH HSWD; hideH RIM.
Ltac unhideD := unfold hidden in HDISJ, HGL, HSWD, RIM.
Hypothesis PSTK : forall a k, bv_unsigned sp - 2224 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PDST : forall a k, A <= a -> a + Z.of_nat k <= A + n -> P (Z_to_bv 64 a, k).
Hypothesis PSH : forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k).

Notation POST := (memset_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n SB ws m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2144)).
Notation g1 := (Z.shiftr A 3).
Notation g2 := (Z.shiftr (A + n + -1) 3).
(* [comment removed for export] *)
Notation SP8 := (Z_to_bv 64 (bv_unsigned sp + -2136)).
Notation ST pc mm x13 x14 x15 x16 x17 :=
  (MS (mkR ra SP' gp tp t0 t1 t2 sp s1 (Z_to_bv 64 A) a1 (Z_to_bv 64 n) x13 x14 x15 x16 x17 s2 s3 s4 SP8 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
(* [comment removed for export] *)
Notation STG pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x22 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 (Z_to_bv 64 A) a1 (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 s4 SP8 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= A < 8 * g1 + 8 /\ 8 * g2 <= A + n + -1 < 8 * g2 + 8 /\
  shw_lo SB A <= SB + g1 /\ SB + g1 < shw_lo SB A + 8 /\ shw_lo SB A mod 8 = 0 /\
  shw_hi SB A n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB A n /\ shw_hi SB A n mod 8 = 0 /\
  shw_lo SB A + 8 <= shw_hi SB A n.
Proof. exact (shw_geom SB A n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma memset_icp_tail : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x22 x28 x29 x30 x31,
  mem_inv asegs m0 ->
  munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (exists junk, rw_cells asegs m0 A [CB (Z.to_nat n) junk]) ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST (STG 0x534b8 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x22 x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM ST FR [junk DST] G SHB.
  pose proof GEO as GE. pose proof RIM as RIM0. unfold range_in_mem in RIM0.
  icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  callA memset_spec.
  1:{ intros a k H1 H2. rewrite ?UA, ?UN in H1. rewrite ?UA, ?UN in H2. apply PDST; lia. }
  1:{ rewrite UA, UN. exact DST. }
  1:{ assumption. }
  ret_pc_lit. rewrite UA, UN in *.
  lazymatch goal with H : rw_cells asegs ?mx A _ |- _ => rename H into DST2 end.
  stepA. (* [comment removed for export] *)
  do 8 stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtA_done. unfold memset_icp_post.
  do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split. { rewrite <- HC. exact DST2. }
  split. { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
             A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
           repeat (split; [assumption|]). exact SBR. }
  split; [assumption| exact SHL].
Qed.

(* [comment removed for export] *)
Lemma memset_icp_loop : forall k (Q : machine_state -> Prop) m0 j x16 x17,
  Z.to_nat (g2 - j) = k -> g1 <= j < g2 ->
  bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P Q (ST 0x535fc m0 (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x17) ->
  evtA asegs P Q (ST 0x535ec m0 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x16 x17).
Proof.
  induction k as [|k IH]; intros Q m0 j x16 x17 Hk Hj SHB CONT; pose proof GEO as GE; [lia|].
  pose proof (range_clean_inner SB A n ws j RC ltac:(lia)) as Hb.
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + j - shw_lo SB A) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - (* [comment removed for export] *) replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - (* [comment removed for export] *) replace (SB + j + 1) with (SB + g2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma memset_icp_join : forall m0 x16 x17,
  mem_inv asegs m0 ->
  munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (exists junk, rw_cells asegs m0 A [CB (Z.to_nat n) junk]) ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST (ST 0x535fc m0 (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x16 x17).
Proof.
  intros m0 x16 x17 MI MU WM ST FR DST G SHB.
  zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
  eapply memset_icp_tail; eassumption.
Qed.

(* [comment removed for export] *)
Lemma memset_icp_slow : forall m0 x16 x17,
  mem_inv asegs m0 ->
  munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (exists junk, rw_cells asegs m0 A [CB (Z.to_nat n) junk]) ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  evtA asegs P POST (ST 0x535d0 m0 (Z_to_bv 64 (SB + g1)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (A + n + -1)) x16 x17).
Proof.
  intros m0 x16 x17 MI MU WM ST FR DST G SHB.
  pose proof GEO as GE.
  destruct (RC g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read asegs m0 (shw_lo SB A) ws (SB + g2 - shw_lo SB A) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?t) ?u)] =>
    change (Z.land (Z.b2z t) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (A + n + -1) 7)) end.
  rewrite (aip_last_clean k2 (A + n + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; exact K2]]).
  zstepA. (* [comment removed for export] *)
  if_cases KG; zify_cond KG.
  - (* [comment removed for export] *) replace (SB + g1) with (SB + g2) by lia. eapply memset_icp_join; eassumption.
  - eapply (memset_icp_loop (Z.to_nat (g2 - g1)) _ m0 g1); [reflexivity | lia | exact SHB |].
    eapply memset_icp_join; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memset_icp_big : forall m0 x13 x14 x15 x16 x17,
  mem_inv asegs m0 ->
  munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m0 -> wmono asegs m m0 ->
  stk asegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells asegs m0 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (exists junk, rw_cells asegs m0 A [CB (Z.to_nat n) junk]) ->
  icp_globals asegs m0 SB -> bytes_at asegs m0 (shw_lo SB A) ws ->
  65 <= n ->
  evtA asegs P POST (ST 0x53604 m0 x13 x14 x15 x16 x17).
Proof.
  intros m0 x13 x14 x15 x16 x17 MI MU WM SK FR [junk DST] G SHB Hn65.
  pose proof GEO as GE. unfold range_in_mem in RIM. pose proof RIM as RIM'. hideD.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2144)) = bv_unsigned sp + -2144) by (apply unsigned_lit; lia).
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
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
  lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk asegs ?mx _ (bv_unsigned sp + -64) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ SKlo2 H ltac:(lia)) as SK2; clear H SKlo2 end.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply memset_icp_tail; try eassumption.
  { eexists; eassumption. }
  { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
      A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
    repeat (split; [assumption|]). lia. }
Qed.

Lemma memset_icp_body : forall (t0' t1' t2' a0 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  a0 = Z_to_bv 64 A -> a2 = Z_to_bv 64 n ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  icp_globals asegs m SB -> shadow_window asegs m SB A n ws ->
  t0' = t0 -> t1' = t1 -> t2' = t2 ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memset_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST MI -> -> DST G SHW -> -> ->.
  unfold memset_icp_entry. pose proof RIM as RIM0. unfold range_in_mem in RIM0. hideD.
  assert (MU : munch [(bv_unsigned sp - 2224, bv_unsigned sp); (A, A + n)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  pose proof GEO as GE.
  assert (MU0 : munch [(bv_unsigned sp - 2224, bv_unsigned sp)] m m) by apply munch_refl.
  hideH DST.
  (* [comment removed for export] *)
  carve_frame 64%nat ST.
  do 11 stepA.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  unhideD. unhideH DST.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport asegs) in G; [ | exact MU | exact WM | cbn; lia ];
    eapply (rw_cells_transport asegs) in DST; [ | exact MU0 | exact WM | cbn; lia ]; clear MU0;
    destruct SHW as [SHB SHL'];
    eapply (bytes_at_transport asegs) in SHB; [ | exact MU | cbn; lia ]
  end.
  hideD. pose proof G as G'. icp_globals_open G.
  stepA. stepA. stepA. (* [comment removed for export] *)
  cbv beta. stepA. if_false.  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  { (* [comment removed for export] *)
    assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
    zstepA. (* [comment removed for export] *) if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
    eapply memset_icp_big; try eassumption. eexists; exact DST. }
  assert (Hn64 : n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
  clear K1 K2.
  stepA. stepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + A ≫ 3)) with (shw_lo SB A).
  replace (al8 (SB + (A + n + -1) ≫ 3)) with (shw_hi SB A n - 8) by (unfold shw_hi; lia).
  (* [comment removed for export] *)
  pose proof (bytes_at_read asegs _ _ _ 0 8 SHB ltac:(lia) ltac:(lia)) as RD1.
  rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read asegs _ _ _ (shw_hi SB A n - 8 - shw_lo SB A) 8 SHB ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB A + (shw_hi SB A n - 8 - shw_lo SB A)) with (shw_hi SB A n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply memset_icp_slow; try eassumption. eexists; exact DST.
  - eapply memset_icp_tail; try eassumption. eexists; exact DST.
Qed.
End Walk.

Lemma memset_icp_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (A c n SB : Z) (ws junk : list byte) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2224 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 A -> a2 = Z_to_bv 64 n -> bv_unsigned a1 mod 256 = c ->
  1 <= n < 2^40 -> range_in_mem SB A n -> 0 < A -> A + n < 2^47 -> (A + n <= lo \/ bv_unsigned sp <= A) -> (A + n <= 0xa4000 \/ 0xaee00 <= A) ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  icp_globals asegs m SB ->
  shadow_window asegs m SB A n ws -> range_clean SB A n ws -> (shw_hi SB A n <= A \/ A + n <= shw_lo SB A) ->
  (* [comment removed for export] *)
  (forall a k, bv_unsigned sp - 2224 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, A <= a -> a + Z.of_nat k <= A + n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A n -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (memset_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n SB ws m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memset_icp_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros ST LOC LO MI HA0 HA2 HC HN RIM HA HAN HDISJ HGL DST G SHW RC HSWD PSTK PIMG PDST PSH.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  eapply memset_icp_body; try eassumption; try reflexivity; try lia.
  destruct SHW as [_ SHL]. exact SHL.
Qed.
End RC__2.
