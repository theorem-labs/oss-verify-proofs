(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_setshadow R_thread R_cache_defs R_prim_defs R_asan_defs R_poison R_prim_kit R_qput.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma qput_A_spec_L : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (c cache stack M n b1 lo : Z) (ctx : word) (shj : list byte),
  (0xbcb000 <= M /\ M + 16 + ru8' n <= kLowMemEnd + 1)%Z -> (M mod 16 = 0)%Z -> (M + 16 + ru8' n <= kHighMemEnd + 1)%Z -> (M + 16 + ru8' n <= lo)%Z ->
  (1 <= n <= 2^28)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells ctasegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells ctasegs m (shad (M + 16)) [CB (Z.to_nat (ru8' n / 8)) shj] ->
  rw_cells ctasegs m q_max [C8 (Z_to_bv 64 0x10000000)] -> rw_cells ctasegs m q_cmax [C8 (Z_to_bv 64 0x100000)] ->
  rw_cells ctasegs m g_GOT_asan_flags [C8 (Z_to_bv 64 g_asan_flags)] -> rw_cells ctasegs m (g_asan_flags + 48) [C4 (Z_to_bv 64 0)] ->
  ps_cells m ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (qput_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c cache stack M n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 c) (Z_to_bv 64 cache) (Z_to_bv 64 stack) (Z_to_bv 64 M)
             (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qput_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until shj. intros HM HM16 HMe HMl Hn Hb1 HD SH QM QC GAF FF PS ST HLO HLOH MI.
  destruct HM as [HM HMlow].
  pose proof (ru8'_range n ltac:(lia)) as RU.
  assert (PA : ps_args_ok (M + 16) (ru8' n)).
  { unfold ps_args_ok. split; [split; [Z.div_mod_to_equations; lia| lia]| left; lia]. }
  pose proof (ps_shad_range _ _ PA) as (SR1 & SR2 & SR3 & SR4).
  unfold qput_entry, kHighShadowEnd, kHighMemEnd, kLowMemEnd, g_GOT_asan_flags, g_asan_flags in *.
  change (6748216 + 48)%Z with 6748264%Z in FF.
  move GAF at bottom. move QM at bottom. move QC at bottom. move FF at bottom.
  pose proof (munch_refl [(shad (M + 16), shad (M + 16) + ru8' n / 8); (bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MUp.
  pose proof (wmono_refl ctasegs m) as WM.
  apply box in PS.
  carve_frame 64%nat ST. carve_frame 16%nat ST.
  do 9 zstep.
  do 5 zstep. zstep. ifF.
  zstep. zstep. ifT.
  do 6 zstep. zstep. ifT.
  do 9 zstep.
  rewrite (Z.mod_small n 4294967296) by lia. rewrite roundup8_machine by lia.
  zstep.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ (unbox _ PS) MUp WM ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PSm.
  clear MUp PS.
  sp_facts.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (M + 16)%Z (ru8' n) 253 lo shj).
  all: rewrite ?Esp in *; try lia; try eassumption.
  do 6 zstep.
  apply evt_done. unfold qput_A_post.
  do 11 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| qexact_addr].
  unfold qput_frame. apply (proj2 (rwc_app ctasegs _ _ [C8 (Z_to_bv 64 cache); C8 (Z_to_bv 64 stack)]
                                  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
  split; [qexact_addr|]. cbn [cells_size csize Nat.add]. qexact_addr.
Qed.
