(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux W_ge3a6 W_al5bs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8 RF_egfy.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_al5bs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_epilogue_post (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR RA (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc RA) fc None m (seg_rom rsegs).

Lemma realloc_epilogue_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (RA S0 S1 S2 S3 S4 S5 S6 : word),
  bv_unsigned sp + 64 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
  evt rsegs (realloc_epilogue_post sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24fec) fc None m (seg_rom rsegs)).
Proof.
  intros until S6. intros SPHI FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  apply evt_done. unfold realloc_epilogue_post. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_fb_malloc_pre (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR (wz 0x24f6c) sp gp tp t0 t1 t2 a1 a0 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz malloc_entry) fc None m (seg_rom rsegs).

Lemma realloc_fb_call_malloc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (realloc_fb_malloc_pre sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24f5c) fc None m (seg_rom rsegs)).
Proof.
  intros. step. step. step. step. apply evt_done. unfold realloc_fb_malloc_pre, malloc_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition realloc_fb_memcpy_pre (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pw : word) (NW P n osz : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR (wz 0x24f8c) sp gp tp t0 t1 t2 (wz NW) pw (wz NW) pw (wz (Z.min n osz)) a3 a4 a5 a6 a7 (wz (P + osz)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x2aff4) (* [comment removed for export] *) fc None m (seg_rom rsegs).

Lemma realloc_fb_after_malloc_copy : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (NW P n osz : Z),
  bv_unsigned a0 = NW -> NW <> 0 -> bv_unsigned s1 = P -> bv_unsigned s0 = n -> 0 <= osz -> P + osz < 2^64 ->
  evt rsegs (realloc_fb_memcpy_pre sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 NW P n osz F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz (P + osz)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24f6c) fc None m (seg_rom rsegs)).
Proof.
  intros until osz. intros HA0 NZ HS1 HS0 OS POS.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  pose proof (bv_unsigned_in_range _ s0) as S0R. change (bv_modulus 64) with (2^64) in S0R.
  pose proof (bv_unsigned_in_range _ s1) as S1R. change (bv_modulus 64) with (2^64) in S1R.
  assert (EA0 : a0 = wz NW) by (rewrite <- HA0; symmetry; apply Z_to_bv_bv_unsigned).
  assert (ES0 : s0 = wz n) by (rewrite <- HS0; symmetry; apply Z_to_bv_bv_unsigned).
  cbv delta [wz].
  step. if_cases K; zify_cond K. { exfalso. lia. }
  (* [comment removed for export] *)
  step. rewrite ?HS1. replace (P + osz + - P) with osz by lia. step.
  step. if_cases K2; zify_cond K2; rewrite ?HS0, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *) step. step. step. rewrite EA0, ES0.
    apply evt_done. unfold realloc_fb_memcpy_pre. rewrite Z.min_l by lia. reflexivity.
  - (* [comment removed for export] *) step. step. step. step. rewrite EA0.
    apply evt_done. unfold realloc_fb_memcpy_pre. rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition realloc_fb_free_pre (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR (wz 0x24f94) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz free_entry) fc None m (seg_rom rsegs).

Lemma realloc_fb_after_memcpy : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (realloc_fb_free_pre sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24f8c) fc None m (seg_rom rsegs)).
Proof. intros. step. step. apply evt_done. unfold realloc_fb_free_pre, free_entry. reflexivity. Qed.

(* [comment removed for export] *)
Lemma realloc_fb_after_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (RA S0 S1 S2 S3 S4 S5 S6 : word),
  bv_unsigned sp + 64 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
  evt rsegs (realloc_epilogue_post sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24f94) fc None m (seg_rom rsegs)).
Proof.
  intros until S6. intros SPHI FR. step. step. apply realloc_epilogue_walk; assumption.
Qed.


(* [comment removed for export] *)
Ltac sokW W off len addr := lazymatch type of W with wr_at rsegs ?mc ?A _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (A + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition needed_of (n base : Z) : Z := (n + base + 4115) - (n + base + 4115) mod 4096.

Lemma needed_of_props n base : 0 <= n -> 0 <= base ->
  n + base + 20 <= needed_of n base < n + base + 20 + 4096 /\ needed_of n base mod 4096 = 0.
Proof. intros. unfold needed_of. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Definition realloc_mremap_skip_post (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (n base maplen : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a3 a5,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (needed_of n base)) s1 a0 a1 a2 a3 (wz (4096 * maplen)) a5 a6 a7
                  s2 (wz base) (wz 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x24ec4) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
Definition realloc_mremap_call_post (sp gp tp t0 t1 t2 s1 a0 a1 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (B n base maplen : Z)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a5,
    ms' = MS (mkR (wz 0x24eb8) sp gp tp t0 t1 t2 (wz (needed_of n base)) s1 (wz B) (wz (4096 * maplen)) (wz (needed_of n base)) (wz 1) a4 a5 a6 a7
                  s2 (wz base) (wz 4095) a0 a1 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz mremap_entry) fc None m (seg_rom rsegs).

Lemma realloc_mremap_setup : forall (ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (P n S B last_idx freeable sc maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= S <= P -> n + (P - S) + 4115 < 2^64 -> 0 <= B < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  evt rsegs (fun ms' =>
        (4096 * maplen = needed_of n (P - S)
         /\ realloc_mremap_skip_post ra sp gp tp t0 (wz S) t2 s1 a0 a1 (wz B) a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n (P - S) maplen F fc m ms')
     \/ (4096 * maplen <> needed_of n (P - S)
         /\ realloc_mremap_call_post sp gp tp t0 (wz S) t2 s1 a0 a1 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 B n (P - S) maplen F fc m ms'))
      (MS (mkR ra sp gp tp t0 (wz S) t2 s0 s1 a0 a1 (wz B) a3 (wz mword) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24e74) fc None m (seg_rom rsegs)).
Proof.
  intros until maplen. intros mword HP HN SP XR BR LI FB SC ML.
  pose proof (bv_unsigned_in_range _ a0) as A0R. change (bv_modulus 64) with (2^64) in A0R.
  pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64) in A1R.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MWM : mword - mword mod 4096 = 4096 * maplen) by (subst mword; apply mword_maplen; lia).
  assert (PR : 0 <= P < 2^64) by lia. assert (SR : 0 <= S < 2^64) by lia.
  set (base := P - S) in *.
  pose proof (needed_of_props n base ltac:(lia) ltac:(lia)) as [ND1 ND2].
  cbv delta [wz].
  (* [comment removed for export] *)
  step. step. rewrite ?HP, ?(unsigned_lit S) by lia. fold base. step. step. step. rewrite ?HN, ?(unsigned_lit base) by lia. step. step.
  rewrite ?(unsigned_lit base), ?(unsigned_lit (n + 4095)), ?(unsigned_lit (n + 4095 + base)) by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (n + 4095 + base + 20)) by lia. rewrite land_pgmask by lia.
  replace (n + 4095 + base + 20 - (n + 4095 + base + 20) mod 4096) with (needed_of n base) by (unfold needed_of; lia).
  step. rewrite ?(unsigned_lit mword) by lia. rewrite land_pgmask by lia. rewrite MWM.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit, ?Z.mod_small in K by lia.
  - apply evt_done. left. split; [lia|]. unfold realloc_mremap_skip_post. do 2 eexists. reflexivity.
  - step. step. step. step. step. step. step. rewrite ?HP, ?HN.
    apply evt_done. right. split; [lia|]. unfold realloc_mremap_call_post, mremap_entry. do 2 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma realloc_after_mremap : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s5 s6 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x24ec4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24eb8) fc None m (seg_rom rsegs)).
Proof. intros. step. step. step. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_mod_pg a nd : 0 <= a < 4096 -> 0 <= nd -> nd mod 4096 = 0 -> Z.lor a nd = a + nd.
Proof.
  intros Ha Hn Hm.
  assert (D : Z.land a nd = 0).
  { replace a with (a + 2^12 * 0) by lia. replace nd with (0 + 2^12 * (nd / 4096)) by (Z.div_mod_to_equations; lia).
    rewrite land_split_k by lia. rewrite Z.land_0_r, Z.land_0_l. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). reflexivity.
Qed.

Definition remap_mem (m : mem) (G NB ND base n mword b3 : Z) : mem :=
  let P' := NB + base + 16 in
  let E' := NB + ND - 4 in
  let m1 := write_to_mem m (wa (G + 16)) (le8 (wz NB)) in
  let m2 := write_to_mem m1 (wa (G + 32)) (le8 (wz (mword mod 4096 + ND))) in
  let m3 := write_to_mem m2 (wa E') [b8 0] in
  set_size_mem m3 P' E' n b3.

(* [comment removed for export] *)
Lemma realloc_remap_fail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  bv_unsigned a2 = 2^64 - 1 ->
  evt rsegs (realloc_fallback_pre ra sp gp tp t0 s0 s1 a0 a1 (wz (-1)) a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24ec4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros HA2.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit_wrap in K. apply K. rewrite HA2. reflexivity. }
  apply evt_done. unfold realloc_fallback_pre. do 7 eexists. reflexivity.
Qed.

Definition realloc_remap_post (sp gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 : word)
   (G NB ND base n mword b3 : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR RA (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 S0 S1 (wz (NB + base + 16)) a1 a2 a3 a4 a5 a6 a7
                  S2 S3 S4 S5 S6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc RA) fc None m' (seg_rom rsegs)
    /\ m' = remap_mem m G NB ND base n mword b3 /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA].

Lemma realloc_remap_walk : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
   (RA S0 S1 S2 S3 S4 S5 S6 : word) (G NB ND base n mword b3 : Z),
  let P' := NB + base + 16 in
  let E' := NB + ND - 4 in
  bv_unsigned a1 = n -> bv_unsigned a2 = NB -> NB <> 2^64 - 1 -> bv_unsigned s1 = G ->
  0 <= n -> 0 <= base -> P' + n <= E' -> E' - P' - n < 2^31 -> 0 <= NB -> NB + ND < 2^64 -> ND mod 4096 = 0 ->
  0 <= G -> G + 40 <= 2^64 -> 0 <= mword < 2^64 -> 0 <= b3 < 256 ->
  (G + 40 <= NB \/ NB + ND <= G + 16) ->
  NB + ND <= bv_unsigned sp -> G + 40 <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  mem_inv rsegs m ->
  ov_read_bytes rsegs m (wa (G + 32)) 8 = Some (le8 (wz mword)) ->
  wr_at rsegs m (G + 16) 24 -> wr_at rsegs m NB ND ->
  bytes_at rsegs m (P' - 3) [b8 b3] ->
  rw_cells rsegs m (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
  evt rsegs (realloc_remap_post sp gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 G NB ND base n mword b3 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz ND) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz base) (wz 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24ec4) fc None m (seg_rom rsegs)).
Proof.
  intros until b3. intros P' E' HN HNB NF HG N0 B0 PNE RS NB0 NDHI NDM G0 G40 MWR B3 DISJ NDSP GSP SPHI MI RMW WG WN BK FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  assert (ND20 : 20 <= ND) by lia.
  set (r := E' - P' - n).
  assert (K31 : 0 <= Z.land b3 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  cbv delta [wz].
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit_wrap, HNB in K. cbn in K. lia. }
  assert (ES1 : s1 = Z_to_bv 64 G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EA2 : a2 = Z_to_bv 64 NB) by (rewrite <- HNB; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EA1 : a1 = Z_to_bv 64 n) by (rewrite <- HN; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ES1, EA2, EA1. clear K.
  pose proof (Z.mod_pos_bound mword 4096 ltac:(lia)) as MM12.
  (* [comment removed for export] *)
  assert (TAIL : forall (t0' a2' a3' a4' a5' a6' : word) (r' : Z) (mc : mem),
    0 <= r' < 8 -> mem_inv rsegs mc -> wr_at rsegs mc NB ND -> bytes_at rsegs mc (P' - 3) [b8 b3] ->
    rw_cells rsegs mc (bv_unsigned sp) [C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA] ->
    (forall mf, mf = write_to_mem mc (wa (P' - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)] -> mf = remap_mem m G NB ND base n mword b3) ->
    evt rsegs (realloc_remap_post sp gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 RA S0 S1 S2 S3 S4 S5 S6 G NB ND base n mword b3 F fc m)
      (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 ND) (Z_to_bv 64 G) (Z_to_bv 64 P') (Z_to_bv 64 r') a2' a3' a4' a5' a6' a7
               s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24fd8) fc None mc (seg_rom rsegs))).
  { intros t0' a2' a3' a4' a5' a6' r' mc R8 MIc WNc BKc FRc HF.
    pose proof (bytes_at_read rsegs mc (P' - 3) [b8 b3] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK.
    cbv [take drop Z.to_nat] in RK. replace (P' - 3 + 0) with (P' + -3) in RK by lia. change (wa (P' + -3)) with (Z_to_bv 64 (P' + -3)) in RK.
    (* [comment removed for export] *)
    step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned b3) by lia.
    step. rewrite ?(unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
    step. rewrite ?(unsigned_lit (r' * 2 ^ 5)), ?(unsigned_lit (Z.land b3 31)) by lia.
    rewrite (lor_shl5 r' (Z.land b3 31)) by lia.
    replace (Z.land (Z.land b3 31) 31) with (Z.land b3 31) by (rewrite <- Z.land_assoc; reflexivity).
    sokW WNc (base + 13) 1%nat (P' + -3).
    step. rewrite (le1_wz (Z.land b3 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    apply evt_done. unfold realloc_remap_post. do 11 eexists. split; [reflexivity|].
    split; [apply HF; assumption|]. split; assumption. }
  (* [comment removed for export] *)
  step. step. step. step. fold P'.
  step. rewrite ?(wz_unsigned mword), ?(unsigned_lit mword) by lia. change 4095 with (2^12 - 1) at 1. rewrite zb_land_mask by lia. change (2^12) with 4096.
  step. replace (NB + ND + -4) with E' by (unfold E'; lia).
  step. step. rewrite ?(unsigned_lit (mword mod 4096)), ?(unsigned_lit ND) by lia. rewrite lor_mod_pg by lia.
  step. rewrite ?(unsigned_lit E'), ?(unsigned_lit (n + P')) by (unfold E', P'; lia). rewrite (swrap32_small (E' - (n + P'))) by (unfold E', P' in *; lia).
  replace (E' - (n + P')) with r by lia.
  (* [comment removed for export] *)
  sokW WG 0 8%nat (G + 16). step. sdk.
  sokW WG 16 8%nat (G + 32). step. sdk.
  sokW WN (ND - 4) 1%nat (NB + ND + -4). step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
 
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by (unfold r, E', P' in *; lia).
  - (* [comment removed for export] *)
    step. step.
    apply (TAIL _ _ _ _ _ _ 0); [lia| assumption| assumption| assumption| assumption|].
    intros mf ->. unfold remap_mem, set_size_mem. cbv zeta.
    replace (NB + ND - 4 - (NB + base + 16) - n) with r by (unfold r, E', P'; lia). rewrite KR. cbv beta iota.
    repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
    unfold E', P'. repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit E'), ?(unsigned_lit (n + P')) by (unfold E', P'; lia). rewrite (swrap32_small (E' - (n + P'))) by (unfold E', P' in *; lia).
    replace (E' - (n + P')) with r by lia.
    step. rewrite ?(unsigned_lit r), (swrap32_small (0 - r)) by (unfold r, E', P' in *; lia).
    step. replace (E' + (0 - r)) with (E' - r + 0) by lia.
    step.
    sokW WN (ND - 4 - r) 1%nat (E' - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by (unfold r, E', P' in *; lia).
    + (* [comment removed for export] *)
      step.
      eapply (TAIL _ _ _ _ _ _ r); [unfold r, E', P' in *; lia| assumption| assumption| assumption| assumption|].
      intros mf ->. unfold remap_mem, set_size_mem. cbv zeta.
      replace (NB + ND - 4 - (NB + base + 16) - n) with r by (unfold r, E', P'; lia).
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      unfold E', P'. repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sokW WN (ND - 9) 1%nat (NB + ND + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sokW WN (ND - 8) 4%nat (NB + ND + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply (TAIL _ _ _ _ _ _ 5); [lia| assumption| assumption| assumption| assumption|].
      intros mf ->. unfold remap_mem, set_size_mem. cbv zeta.
      replace (NB + ND - 4 - (NB + base + 16) - n) with r by (unfold r, E', P'; lia).
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      unfold E', P'. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
