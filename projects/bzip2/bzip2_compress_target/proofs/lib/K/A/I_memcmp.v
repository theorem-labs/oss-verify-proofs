(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow IcptSpec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small R_m2s R_thread I_consts I_qck D_kit I_ikit F_memcmp I_memcmpw.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow IcptSpec2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_ikit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memcmp.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_memcmpw.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma cmp_musl : cmp_stmt 0xc6134 80.
Proof.
  unfold cmp_stmt. intros until b2. intros (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & _) ST LO LOLO SPH MI.
  eapply evt_mono.
  { apply (memcmp_spec b1 b2 p1 p2); try assumption; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  unfold frame_post. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI | exact ST].
Qed.

(* [comment removed for export] *)
Section Wrap_bcmp.
Variable D : Z.
Hypothesis HD : 80 <= D.
Hypothesis CMN : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0xc6134) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ff0) fc None m (seg_rom bsegs)).

Theorem wrap_bcmp : cmp_stmt 0x44884 (48 + (2192 + D)).
Proof using HD CMN.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (48 + (2192 + D)), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 3 lstep. lstep.
  call try_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -48) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -48) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof CMN as CM.
  call CM; [rewrite EU48; exact CA3| rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.
End Wrap_bcmp.

(* [comment removed for export] *)
Section Wrap_memcmp.
Variable D : Z.
Hypothesis HD : 80 <= D.
Hypothesis CMN : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0xc6064) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ff0) fc None m (seg_rom bsegs)).

Theorem wrap_memcmp : cmp_stmt 0x44940 (48 + (2192 + D)).
Proof using HD CMN.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (48 + (2192 + D)), usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 3 lstep. lstep.
  call try_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -48) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -48) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof CMN as CM.
  call CM; [rewrite EU48; exact CA3| rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.
End Wrap_memcmp.

Notation IMEMCMP_DEPTH := 4560%Z (only parsing).

Section Chain.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma cmp_ibcmp : cmp_stmt 0x44884 2320.
Proof using RIP.
  change 2320 with (48 + (2192 + 80)). apply (wrap_bcmp 80 ltac:(lia)).
  intros. apply (common_spec 0xc6134 80 ltac:(split; [lia | reflexivity]) ltac:(lia) cmp_musl RIP); assumption.
Qed.

(* [comment removed for export] *)
Lemma cmp_bcmp_stub : cmp_stmt 0xc6064 2320.
Proof using RIP.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lstep. lstep.
  apply cmp_ibcmp; assumption.
Qed.

(* [comment removed for export] *)
Theorem imemcmp_spec : cmp_stmt 0x44940 IMEMCMP_DEPTH.
Proof using RIP.
  change 4560 with (48 + (2192 + 2320)). apply (wrap_memcmp 2320 ltac:(lia)).
  intros. apply (common_spec 0xc6064 2320 ltac:(split; [lia | reflexivity]) ltac:(lia) cmp_bcmp_stub RIP); assumption.
Qed.

End Chain.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread I_consts I_qck D_kit I_ikit IcptSpec2 F_memcmp I_memcmpw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma cmp_musl : cmp_stmt 0xb8d54 80.
Proof.
  unfold cmp_stmt. intros until b2. intros (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & _) ST LO LOLO SPH MI.
  eapply evt_mono.
  { apply (memcmp_spec b1 b2 p1 p2); try assumption; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  unfold frame_post. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI | exact ST].
Qed.

(* [comment removed for export] *)
Section Wrap_bcmp.
Variable D : Z.
Hypothesis HD : 80 <= D.
Hypothesis CMN : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0xb8d54) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44108) fc None m (seg_rom asegs)).

Theorem wrap_bcmp : cmp_stmt 0x4499c (48 + (2192 + D)).
Proof using HD CMN.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (48 + (2192 + D)), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 3 lstep. lstep.
  call try_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -48) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -48) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof CMN as CM.
  call CM; [rewrite EU48; exact CA3| rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.
End Wrap_bcmp.

(* [comment removed for export] *)
Section Wrap_memcmp.
Variable D : Z.
Hypothesis HD : 80 <= D.
Hypothesis CMN : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 lo : Z) (b1 b2 : list byte),
  cmp_args m (bv_unsigned sp) lo p1 p2 b1 b2 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - (2192 + D) -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (memcmp_res b1 b2) [(bv_unsigned sp - (2192 + D), bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0xb8c84) (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.of_nat (length b1))) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44108) fc None m (seg_rom asegs)).

Theorem wrap_memcmp : cmp_stmt 0x44a58 (48 + (2192 + D)).
Proof using HD CMN.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof CA as (HL & HN & P1 & P1h & P2 & P2h & B1 & B2 & SEP1 & SEP2 & CS1 & CS2 & M2S & IC).
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - (48 + (2192 + D)), usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & RL & SHC & AI & FLG).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  do 9 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. do 3 lstep. lstep.
  call try_init_spec; [exact AI| rewrite EU48; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST2 end.
  do 2 lstep. lstep. if_false.
  do 5 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CA3 : cmp_args mm (usp + -48) lo p1 p2 b1 b2)
      by (apply (cmp_args_stack m mm _ usp (usp + -48) lo p1 p2 b1 b2 CA MU WM); [cbn [outside]; intros yy Hyy; lia | unfold kHighShadowEnd; lia | lia | lia]) end.
  pose proof CMN as CM.
  call CM; [rewrite EU48; exact CA3| rewrite EU48; exact ST2| rewrite EU48; lia| unfold kHighShadowEnd; lia| rewrite EU48; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST3 end.
  do 5 lstep.
  release_frame FR ST3 usp.
  lstep.
  unfold frame_post. sys_finish.
  all: rewrite ?EU; first [assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia].
Qed.
End Wrap_memcmp.

Notation IMEMCMP_DEPTH := 4560%Z (only parsing).

Section Chain.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma cmp_ibcmp : cmp_stmt 0x4499c 2320.
Proof using RIP.
  change 2320 with (48 + (2192 + 80)). apply (wrap_bcmp 80 ltac:(lia)).
  intros. apply (common_spec 0xb8d54 80 ltac:(split; [lia | reflexivity]) ltac:(lia) cmp_musl RIP); assumption.
Qed.

(* [comment removed for export] *)
Lemma cmp_bcmp_stub : cmp_stmt 0xb8c84 2320.
Proof using RIP.
  unfold cmp_stmt. intros until b2. intros CA ST LO LOLO SPH MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lstep. lstep.
  apply cmp_ibcmp; assumption.
Qed.

(* [comment removed for export] *)
Theorem imemcmp_spec : cmp_stmt 0x44a58 IMEMCMP_DEPTH.
Proof using RIP.
  change 4560 with (48 + (2192 + 2320)). apply (wrap_memcmp 2320 ltac:(lia)).
  intros. apply (common_spec 0xb8c84 2320 ltac:(split; [lia | reflexivity]) ltac:(lia) cmp_bcmp_stub RIP); assumption.
Qed.

End Chain.
