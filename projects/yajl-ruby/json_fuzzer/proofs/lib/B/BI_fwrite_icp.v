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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr ITree Nodes Decode SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ITreeA NodesA SysStepA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_monadx BI_shadow BI_globals2 BM_syscalls BM_stdio_lib BX_file BI_memtoshadow BI_region_is_poisoned BM_stdio_write BM_fwrite BI_gtrans.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition fwrite_icp_entry : Z := 0x44e98.
Definition FWRITE_ICP_DEPTH : Z := 2368.

End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma land_ones64 : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof.
  intros x. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.ltb_spec i 64).
  - rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. symmetry. apply Z.mod_pow2_bits_low. lia.
  - rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.

Section Walk.
Context {St : Type}.
Variable P : acc -> Prop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (S n SB : Z) (ws : list byte) (lo : Z) (canary : word).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - FWRITE_ICP_DEPTH.
Hypothesis SPTS : bv_unsigned sp < 0x800000000000.  (* [comment removed for export] *)
Hypothesis HN : 1 <= n < 2^31.
Hypothesis RIM : range_in_mem SB S n.
Hypothesis HS : 0x10000 <= S.
Hypothesis HSN : S + n <= 0x31000.
Hypothesis SHL : Z.of_nat (length ws) = shw_hi SB S n - shw_lo SB S.
Hypothesis RC : range_clean SB S n ws.
Hypothesis HSWD : shw_hi SB S n <= S \/ S + n <= shw_lo SB S.
Hypothesis SBR : 2^24 <= SB < 2^32.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSH : forall a k, shw_lo SB S <= a -> a + Z.of_nat k <= shw_hi SB S n -> P (Z_to_bv 64 a, k).
Hypothesis PNUL : forall a, P (Z_to_bv 64 a, 0%nat).

Definition fwrite_icp_post (st : St) : unit -> St -> machine_state -> Prop :=
  fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ stderr_wfile0 m' /\ ssp_cells m' canary
    /\ icp_globals bsegs m' SB /\ icp_globals2 bsegs m' /\ shadow_window bsegs m' SB S n ws
    /\ st' = st.

Notation g1 := (Z.shiftr S 3).
Notation g2 := (Z.shiftr (S + n + -1) 3).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2128)).
(* [comment removed for export] *)
Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp (Z_to_bv 64 n) x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 S) (Z_to_bv 64 0xa9c68) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

Lemma GEO :
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= S < 8 * g1 + 8 /\ 8 * g2 <= S + n + -1 < 8 * g2 + 8 /\
  shw_lo SB S <= SB + g1 /\ SB + g1 < shw_lo SB S + 8 /\ shw_lo SB S mod 8 = 0 /\
  shw_hi SB S n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB S n /\ shw_hi SB S n mod 8 = 0 /\
  shw_lo SB S + 8 <= shw_hi SB S n.
Proof. exact (shw_geom SB S n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Definition fwi_mem (st : St) (m1 : mem) : Prop :=
  mem_inv bsegs m1 /\ munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 /\ wmono bsegs m m1
  /\ stk bsegs m1 lo (bv_unsigned sp + -64)
  /\ rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 (@nil byte ++ repeat (Z_to_bv 8 0) 0) ; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ stderr_wfile0 m1 /\ ssp_cells m1 canary /\ icp_globals bsegs m1 SB /\ icp_globals2 bsegs m1 /\ bytes_at bsegs m1 (shw_lo SB S) ws.

(* [comment removed for export] *)
Lemma fwi_tail : forall st (Q : unit -> St -> machine_state -> Prop) m1 j8 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
  mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stderr_wfile0 m1 -> ssp_cells m1 canary -> icp_globals bsegs m1 SB -> icp_globals2 bsegs m1 -> bytes_at bsegs m1 (shw_lo SB S) ws ->
  (forall ms', fwrite_icp_post st tt st ms' -> Q tt st ms') ->
  evtA bsegs P (Q tt st) (ST 0x44f58 m1 x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM SK FR W0 SSP G G2 SHB HQ.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR. unfold FWRITE_ICP_DEPTH in LO.
  stepA. do 7 stepA. stepA. stepA.
  release_frame FR SK (bv_unsigned sp).
  apply evtA_done. apply HQ. unfold fwrite_icp_post.
  do 15 eexists. split; [reflexivity|].
  repeat (split; [assumption|]). split; [| reflexivity]. split; [exact SHB | exact SHL].
Qed.

(* [comment removed for export] *)
Lemma fwi_loop : forall k (Q : machine_state -> Prop) m1 j x1 x5 x6 x7 x10 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
  Z.to_nat (g2 - j) = k -> g1 <= j < g2 ->
  bytes_at bsegs m1 (shw_lo SB S) ws ->
  evtA bsegs P Q (ST 0x4502c m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x15 x16 x17 x20 x21 x28 x29 x30 x31) ->
  evtA bsegs P Q (ST 0x4501c m1 x1 x5 x6 x7 x10 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 x20 x21 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros Q m1 j x1 x5 x6 x7 x10 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 Hk Hj SHB CONT; pose proof GEO as GE; [lia|].
  pose proof (range_clean_inner SB S n ws j RC ltac:(lia)) as Hb.
  pose proof (u8ro_read bsegs m1 (shw_lo SB S) ws (SB + j - shw_lo SB S) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m1 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + g2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma fwi_join : forall st (Q : unit -> St -> machine_state -> Prop) m1 j8 x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
  mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stderr_wfile0 m1 -> ssp_cells m1 canary -> icp_globals bsegs m1 SB -> icp_globals2 bsegs m1 -> bytes_at bsegs m1 (shw_lo SB S) ws ->
  (forall ms', fwrite_icp_post st tt st ms' -> Q tt st ms') ->
  evtA bsegs P (Q tt st) (ST 0x4502c m1 x1 x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 0) x14 x15 x16 x17 x20 x21 x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM SK FR W0 SSP G G2 SHB HQ.
  zstepA. zstepA. eapply fwi_tail; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fwi_slow : forall st (Q : unit -> St -> machine_state -> Prop) m1 j8 x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
  mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stderr_wfile0 m1 -> ssp_cells m1 canary -> icp_globals bsegs m1 SB -> icp_globals2 bsegs m1 -> bytes_at bsegs m1 (shw_lo SB S) ws ->
  (forall ms', fwrite_icp_post st tt st ms' -> Q tt st ms') ->
  evtA bsegs P (Q tt st) (ST 0x45000 m1 x1 x5 x6 x7 (Z_to_bv 64 1) (Z_to_bv 64 (SB + g1)) (Z_to_bv 64 (SB + g2)) (Z_to_bv 64 (S + n + -1)) x14 x15 x16 x17 x20 x21 x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM SK FR W0 SSP G G2 SHB HQ.
  pose proof GEO as GE.
  destruct (RC g2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read bsegs m1 (shw_lo SB S) ws (SB + g2 - shw_lo SB S) _ (Z_to_bv 64 (SB + g2)) SHB Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?tt) ?u)] =>
    change (Z.land (Z.b2z tt) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (S + n + -1) 7)) end.
  rewrite (aip_last_clean k2 (S + n + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; exact K2]]).
  zstepA. (* [comment removed for export] *)
  if_cases KG; zify_cond KG.
  - replace (SB + g1) with (SB + g2) by lia. eapply fwi_join; eassumption.
  - eapply (fwi_loop (Z.to_nat (g2 - g1)) _ m1 g1); [reflexivity | lia | exact SHB |].
    eapply fwi_join; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fwi_big : forall st (Q : unit -> St -> machine_state -> Prop) m1 j8 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31,
  mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stderr_wfile0 m1 -> ssp_cells m1 canary -> icp_globals bsegs m1 SB -> icp_globals2 bsegs m1 -> bytes_at bsegs m1 (shw_lo SB S) ws ->
  65 <= n ->
  (forall ms', fwrite_icp_post st tt st ms' -> Q tt st ms') ->
  evtA bsegs P (Q tt st) (ST 0x45034 m1 x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 x20 (Z_to_bv 64 1) x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM SK FR W0 SSP G G2 SHB Hn65 HQ.
  pose proof GEO as GE. pose proof RIM as RIM'. unfold range_in_mem in RIM'. unfold FWRITE_ICP_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) = bv_unsigned sp + -2128) by (apply unsigned_lit; lia).
  destruct (stk_split bsegs m1 lo (bv_unsigned sp + -2128) (bv_unsigned sp + -64) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  pose proof G as Gc. icp_globals_open Gc.
  eapply evtA_cut.
  { eapply (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S n SB ws lo P).
    - rewrite USP. exact SKlo.
    - unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
    - rewrite USP. lia.
    - exact MI.
    - reflexivity. - reflexivity.
    - lia. - lia. - exact RIM. - exact G.
    - split; [exact SHB | exact SHL]. - exact RC.
    - intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia.
    - exact PIMG. - exact PSH. }
  cbv beta. intros ms2 PO. unfold region_is_poisoned_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MUc & WMc & MI2 & SKlo2).
  rewrite USP in MUc, SKlo2. ret_pc_lit.
  pose proof (stk_merge bsegs _ _ _ _ SKlo2 (stk_transport_disjoint _ _ _ _ _ _ SKhi MUc WMc ltac:(cbn; lia)) ltac:(lia)) as SK2.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MUc WMc ltac:(cbn; lia)) as FR2.
  assert (W2 : stderr_wfile0 m2).
  { destruct W0 as (fl & md & e & we & tl & FC & R). exists fl, md, e, we, tl. split; [| exact R].
    eapply rw_cells_transport; [exact FC | exact MUc | exact WMc | cbn; lia]. }
  assert (SSP2 : ssp_cells m2 canary).
  { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *.
    split; (eapply rw_cells_transport; [eassumption | exact MUc | exact WMc | cbn; lia]). }
  pose proof (icp_globals_transport bsegs _ _ _ _ G MUc WMc ltac:(cbn; lia)) as Gx.
  pose proof (icp_globals2_transport bsegs _ _ _ G2 MUc WMc ltac:(cbn; lia) ltac:(cbn; lia)) as G2x.
  pose proof (bytes_at_transport bsegs _ _ _ _ _ SHB MUc ltac:(cbn; lia)) as SHB2.
  assert (MU2 : munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp; cbn [outside]; intros; lia. }
  pose proof (wmono_trans _ _ _ _ WM WMc) as WM2.
  clear MUc WMc SKlo2 SKhi FR W0 SSP G2 SHB MU WM MI.
  zstepA. (* [comment removed for export] *) if_true.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply fwi_tail; try eassumption.
Qed.

(* [comment removed for export] *)
Lemma fwi_check : forall st (Q : unit -> St -> machine_state -> Prop) m1 j8 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1 -> wmono bsegs m m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stderr_wfile0 m1 -> ssp_cells m1 canary -> icp_globals bsegs m1 SB -> icp_globals2 bsegs m1 -> bytes_at bsegs m1 (shw_lo SB S) ws ->
  (forall ms', fwrite_icp_post st tt st ms' -> Q tt st ms') ->
  evtA bsegs P (Q tt st) (ST 0x44ef4 m1 x1 x5 x6 x7 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 1) x28 x29 x30 x31).
Proof.
  intros until x31. intros MI MU WM SK FR W0 SSP G G2 SHB HQ.
  pose proof GEO as GE. pose proof RIM as RIM'. unfold range_in_mem in RIM'.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR. unfold FWRITE_ICP_DEPTH in LO.
  pose proof G as G'. icp_globals_open G'.
  stepA. if_false. stepA. if_false. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) rewrite Z.mul_1_l.
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  { (* [comment removed for export] *)
    assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite ?land_ones64. change (2^64) with 18446744073709551616. rewrite mod64_neg_small by lia. lia. }
    zstepA. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
    eapply fwi_big; eassumption. }
  assert (Hn64 : n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite ?land_ones64. change (2^64) with 18446744073709551616. rewrite Z.mod_small by lia. lia. }
  clear K1 K2.
  stepA. stepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + S ≫ 3)) with (shw_lo SB S).
  replace (al8 (SB + (S + n + -1) ≫ 3)) with (shw_hi SB S n - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read bsegs _ _ _ 0 8 SHB ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read bsegs _ _ _ (shw_hi SB S n - 8 - shw_lo SB S) 8 SHB ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB S + (shw_hi SB S n - 8 - shw_lo SB S)) with (shw_hi SB S n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply fwi_slow; eassumption.
  - eapply fwi_tail; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fwrite_icp_body : forall (st : St) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (zs : list Z),
  stk bsegs m lo (bv_unsigned sp) -> mem_inv bsegs m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 0xa9c68 ->
  bytes_at bsegs m S (zb zs) -> Forall (fun c => 0 <= c < 256) zs -> zlength zs = n ->
  stderr_wfile0 m -> ssp_cells m canary ->
  icp_globals bsegs m SB -> icp_globals2 bsegs m -> shadow_window bsegs m SB S n ws ->
  implMA bsegs P (stderr_fwrite zs : M St unit) st (fwrite_icp_post st)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 fwrite_icp_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until zs. intros SK MI -> -> -> -> SRC HF LEN W0 SSP G G2 [SHB SHL'].
  pose proof GEO as GE. pose proof RIM as RIM'. unfold range_in_mem in RIM'. unfold FWRITE_ICP_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold fwrite_icp_entry. apply implMA_from_evtA. hideH SRC.
  pose proof G as G'. icp_globals_open G'. pose proof (ig2_fwrite bsegs _ G2) as GRF.
  carve_frame 64%nat SK.
  do 10 stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  stepA.
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -64) |- _ =>
    destruct (stk_split bsegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -64) H ltac:(lia)) as [SKlo SKhi]; clear H end.
  carve_frame 16%nat SKlo.
  stepA. stepA. stepA. stepA. stepA. stepA. zstepA. stepA. cbv beta. stepA. if_false.
  stepA. stepA. stepA. stepA.
  lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -2144) _ |- _ => release_frame H SKlo (bv_unsigned sp + -2128) end.
  (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MUx : munch [(lo, bv_unsigned sp)] m mx, WMx : wmono bsegs m mx |- _ =>
      assert (W0x : stderr_wfile0 mx) by
        (destruct W0 as (fl & md & e & we & tl & FC & R); exists fl, md, e, we, tl; split; [| exact R];
         eapply rw_cells_transport; [exact FC | exact MUx | exact WMx | cbn; lia]);
      assert (SSPx : ssp_cells mx canary) by
        (destruct SSP as [Q1 Q2]; unfold ssp_cells, got_ssp, ssp_guard in *;
         split; (eapply rw_cells_transport; [eassumption | exact MUx | exact WMx | cbn; lia]));
      pose proof (icp_globals_transport bsegs _ _ _ _ G MUx WMx ltac:(cbn; lia)) as Gx;
      pose proof (icp_globals2_transport bsegs _ _ _ G2 MUx WMx ltac:(cbn; lia) ltac:(cbn; lia)) as G2x;
      rename SHB into SHBx; unhideH SRC;
      pose proof (bytes_at_transport bsegs _ _ _ _ _ SRC MUx ltac:(cbn; rewrite zb_length'; unfold zlength in LEN; lia)) as SRCx
    end end.
  apply evtA_done. name_sp sp (-2128).
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned sp + -2128), E : bv_unsigned _ = bv_unsigned sp + -2128 |- _ => rewrite <- E in H end.
  eapply implMA_post_evt''.
  { eapply (fwrite_diag_proof (St:=St)) with (lo := lo) (P := P) (s := zs) (canary := canary);
      [ intros a k H1 H2; apply PSTK; lia | exact PIMG
      | intros a k H1 H2; rewrite unsigned_lit in H1, H2 by lia; apply PIMG; lia
      | exact PNUL | exact towrite_proof | exact W0x
      | rewrite unsigned_lit by lia; exact SRCx | exact HF | rewrite LEN; lia
      | rewrite LEN; reflexivity | reflexivity | reflexivity
      | eassumption | unfold FWRITE_DEPTH; lia | lia | lia
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | exact SSPx | eassumption ]. }
  cbv beta. intros [] st' ms' PO. unfold fwrite_diag_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MUc & WMc & MI1 & SK2 & W1 & SSP1 & ->).
  unname_sp. ret_pc_lit.
  (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells bsegs ?mx (bv_unsigned sp + -64) _, MUx : munch [(lo, bv_unsigned sp)] m ?mx2, WMx : wmono bsegs m ?mx3 |- _ =>
    pose proof (rw_cells_transport bsegs _ _ _ _ _ FRx MUc WMc ltac:(cbn; lia)) as FR1;
    pose proof (stk_transport_disjoint bsegs _ _ _ _ _ SKhi MUc WMc ltac:(cbn; lia)) as SKhi1;
    pose proof (icp_globals_transport_cells _ _ _ _ Gx MUc WMc ltac:(unfold icp_globals_cells; cells_disjoint)) as G1;
    pose proof (icp_globals2_transport_cells _ _ _ G2x MUc WMc ltac:(unfold icp_globals2_cells; cells_disjoint)) as G21;
    pose proof (bytes_at_transport bsegs _ _ _ _ _ SHBx MUc ltac:(cbn; lia)) as SHB1;
    assert (MU1 : munch [(lo, bv_unsigned sp); (0xa9c68, 0xa9c68 + 232)] m m1) by
      (eapply munch_trans; [| eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia];
       eapply munch_weaken; [| exact MUx]; unfold sub_fp; cbn [outside]; intros; lia);
    pose proof (wmono_trans _ _ _ _ WMx WMc) as WM1
  end.
  pose proof (stk_merge bsegs _ _ _ _ SK2 SKhi1 ltac:(lia)) as SKtop.
  eapply (fwi_check st (fwrite_icp_post st) m1); try eassumption. intros ms' H; exact H.
Qed.
End Walk.
End RC__2.
