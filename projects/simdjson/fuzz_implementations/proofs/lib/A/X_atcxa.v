(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS NodesA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_libiface Sj_acps R_thread X_aexdefs X_ixdefs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Local Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sxb (Z_to_bv 8 z))) in
        replace (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word) by (vm_compute; reflexivity)
  | |- context [(fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 ?z)] => is_Zlit z;
        change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 z)) with (Z_to_bv 64 z : word)
  end.
Local Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Local Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition e_icxa : Z := 0x6fd24.
Definition e_asan_inited : Z := 0x8d678.
Definition e_lsan_disable : Z := 0xb3db4.
Definition e_lsan_enable : Z := 0xb3dd0.

Definition e_stop_ioc : Z := 0x6c2b8.

Definition AEX_W : list (Z * Z) := [(AEX, AEX + 80); (AEX_A0, AEX_A0 + 48)].

Definition cxa_atexitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (tbl args : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX, AEX + 80); (AEX_A0, AEX_A0 + 48)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AEX tbl /\ rw_cells asegs m' AEX_A0 args.

Definition cxa_atexitA_stmt (pc : Z) (pre_tbl pre_args : word -> word -> list cell) (post_tbl post_args : word -> word -> list cell) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (fo ao : word),
  stk asegs m lo (bv_unsigned sp) ->
  ro_cells asegs m LIBC_NL [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AEX (pre_tbl fo ao) -> rw_cells asegs m AEX_A0 (pre_args fo ao) ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 48) -> (SEGTOP_A <= lo) ->
  evt asegs (cxa_atexitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (post_tbl a0 a1) (post_args a0 a1) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Lemma cxa_atexitA_spec4 : forall (p1 p2 : list byte) (f5 a3v a5v : word),
  cxa_atexitA_stmt e_musl_cxa_atexit
    (fun fo ao => aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) fo f5) (fun fo ao => aex_args a3v ao a5v)
    (fun fn ob => aex_tbl 5 p1 p2 (Z_to_bv 64 X_CALL) fn f5) (fun fn ob => aex_args a3v ob a5v).
Proof.
  intros p1 p2 f5 a3v a5v. unfold cxa_atexitA_stmt, e_musl_cxa_atexit.
  intros until ao; intros ST NL TBL TA MI LO LOLO; aex_lits; unfold SEGTOP_A, LIBC_NL in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d0178, 0x6d0178 + 80); (0x6d0298, 0x6d0298 + 48)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x152948%Z.
  xsteps_to 0x152964%Z.
  xsteps_to 0x152970%Z.
  xsteps_to 0x15298c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  apply evt_done. unfold cxa_atexitA_post. aex_lits. sys_finish.
Qed.

Lemma cxa_atexitA_spec5 : forall (p1 p2 : list byte) (f4 a3v a4v : word),
  cxa_atexitA_stmt e_musl_cxa_atexit
    (fun fo ao => aex_tbl 5 p1 p2 (Z_to_bv 64 X_CALL) f4 fo) (fun fo ao => aex_args a3v a4v ao)
    (fun fn ob => aex_tbl 6 p1 p2 (Z_to_bv 64 X_CALL) f4 fn) (fun fn ob => aex_args a3v a4v ob).
Proof.
  intros p1 p2 f4 a3v a4v. unfold cxa_atexitA_stmt, e_musl_cxa_atexit.
  intros until ao; intros ST NL TBL TA MI LO LOLO; aex_lits; unfold SEGTOP_A, LIBC_NL in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d0178, 0x6d0178 + 80); (0x6d0298, 0x6d0298 + 48)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x152948%Z.
  xsteps_to 0x152964%Z.
  xsteps_to 0x152970%Z.
  xsteps_to 0x15298c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  apply evt_done. unfold cxa_atexitA_post. aex_lits. sys_finish.
Qed.

Lemma asan_inited2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m 0x17c398 [C1 (Z_to_bv 8 1)] ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x6d2000 <= lo ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [(bv_unsigned sp - 16, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_asan_inited) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AI ST LO LOLO MI. unfold e_asan_inited.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  xsteps_to 0x8d698%Z. xstep.
  xsteps_to 0x8d6a8%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold frame_post. sys_finish.
Qed.

Definition lsan_enable_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (LSAN_CTR, LSAN_CTR + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' LSAN_CTR [C4 (Z_to_bv 64 0)].

Lemma lsan_enable_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m 0x172da8 [C8 (Z_to_bv 64 16)] ->
  rw_cells asegs m LSAN_CTR [C4 (Z_to_bv 64 1)] ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x6d2000 <= lo ->
  mem_inv asegs m ->
  evt asegs (lsan_enable_post ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_lsan_enable) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros G88 CTR ST LO LOLO MI. unfold e_lsan_enable, LSAN_CTR, TP_A in *.
  match type of CTR with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in CTR end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x6b0138, 0x6b0138 + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  xsteps_to 0xb3dec%Z. xstep.
  xsteps_to 0xb3e04%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold lsan_enable_post, LSAN_CTR. sys_finish.
Qed.

Definition icxa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (a3v : word) (fn obj : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (AEX, AEX + 80); (AEX_A0, AEX_A0 + 48); (LSAN_CTR, LSAN_CTR + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' AEX (aex_tbl 6 p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 fn) (Z_to_bv 64 X_ATCXA))
    /\ rw_cells asegs m' AEX_A0 (aex_args a3v (Z_to_bv 64 obj) (Z_to_bv 64 0))
    /\ rw_cells asegs m' LSAN_CTR [C4 (Z_to_bv 64 0)].

Lemma icxa_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo fn obj : Z) (p1 p2 : list byte) (f4 f5 a3v a4v a5v : word),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96) -> (SEGTOP_A <= lo) ->
  rw_cells asegs m 0x17c398 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x172da8 [C8 (Z_to_bv 64 16)] ->
  rw_cells asegs m LSAN_CTR [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m g_REAL_cxa_atexit [C8 (Z_to_bv 64 e_musl_cxa_atexit)] ->
  ro_cells asegs m LIBC_NL [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AEX (aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) f4 f5) ->
  rw_cells asegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 fn -> a1 = Z_to_bv 64 obj -> (0 <= fn < 2^64) -> (0 <= obj < 2^64) ->
  evt asegs (icxa_post ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 a3v fn obj m)
      (MS (mkR ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_icxa) fc None m (seg_rom asegs)).
Proof.
  intros until a5v. intros ST LO LOLO AI G88 CTR RX NL TBL TA MI -> -> Hfn Hobj.
  pose proof (cxa_atexitA_spec4 p1 p2 f5 a3v a5v) as CX4. pose proof (cxa_atexitA_spec5 p1 p2 (Z_to_bv 64 fn) a3v (Z_to_bv 64 obj)) as CX5.
  pose proof lsan_enable_spec as LSE.
  unfold cxa_atexitA_stmt, cxa_atexitA_post in CX4, CX5. cbv beta in CX4, CX5. unfold lsan_enable_post in LSE.
  aex_lits. unfold e_icxa, LSAN_CTR, TP_A, g_REAL_cxa_atexit, e_musl_cxa_atexit, SEGTOP_A, LIBC_NL in *.
  match type of CTR with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in CTR end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0x6d0178, 0x6d0178 + 80); (0x6d0298, 0x6d0298 + 48); (0x6b0138, 0x6b0138 + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST.
  xstep.
  xsteps_to 0x7a314%Z.

  xstep. call_sp asan_inited2_spec; [exact AI| exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST1 end.

  xstep. xsteps_to 0x7a31c%Z.

  xsteps_to 0x7a330%Z. xstep.
  try replace (ret_pc (Z_to_bv 64 0x1528c8)) with (Z_to_bv 64 0x1528c8 : word) by (apply bv_eq; vm_compute; reflexivity).
  call_sp CX4; [exact ST1| exact NL| exact TBL| exact TA| assumption| lia| lia|]. clear CX4.
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST2 end.

  xsteps_to 0x7a34c%Z. xstep.
  try replace (ret_pc (Z_to_bv 64 0x1528c8)) with (Z_to_bv 64 0x1528c8 : word) by (apply bv_eq; vm_compute; reflexivity).
  call_sp CX5; [exact ST2| | | | assumption| lia| lia|].
  { lazymatch goal with H : ro_cells asegs _ 0x6d03bb _ |- _ => exact H end. }
  { lazymatch goal with H : rw_cells asegs _ 0x6d0178 _ |- _ => exact H end. }
  { lazymatch goal with H : rw_cells asegs _ 0x6d0298 _ |- _ => exact H end. }
  clear CX5.
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.

  xstep.
  call_sp LSE; [ | | exact ST3| lia| lia| assumption|]. clear LSE.
  { lazymatch goal with H : rw_cells asegs _ 0x172da8 _ |- _ => exact H end. }
  { unfold LSAN_CTR, TP_A. lazymatch goal with H : rw_cells asegs _ 0x6b0138 _ |- _ => exact H end. }
  lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST4 end.

  xsteps_to 0x7a370%Z.
  release_frame FR ST4 (bv_unsigned sp).
  xstep.
  apply evt_done. unfold icxa_post, LSAN_CTR, TP_A. aex_lits. sys_finish.
Qed.

Lemma atcxa_handler_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  rw_cells asegs m g_GOT_flags [C8 (Z_to_bv 64 0x178eb8)] ->
  rw_cells asegs m g_flags_cio [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> SEGTOP_A <= lo ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 X_ATCXA) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros GF CIO ST LO LOLO MI. unfold g_GOT_flags, g_flags_cio, X_ATCXA, SEGTOP_A in *.
  match type of CIO with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in CIO end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 96%nat ST.
  xstep.
  xsteps_to 0x6c2f4%Z. xstep.
  xsteps_to 0x6c520%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  sys_finish.
Qed.

Definition aex4 (m : mem) : Prop :=
  (exists (p1 p2 : list byte) (f4 f5 : word), rw_cells asegs m AEX (aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) f4 f5))
  /\ (exists a4 a5 : word, rw_cells asegs m AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) a4 a5)).

Section Contract.
Variable RT : rt_sig.

Definition atcxa_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fn obj dso : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 fn -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 dso -> tp = Z_to_bv 64 TP_A ->
  0 <= fn < 2^64 -> 0 <= obj < 2^64 ->
  aex4 m -> libc_nl m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_icxa m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) AEX_W m m'
         /\ (exists p1 p2, rw_cells asegs m' AEX (aex_tbl 6 p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 fn) (Z_to_bv 64 X_ATCXA)))
         /\ rw_cells asegs m' AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 obj) (Z_to_bv 64 0))) c).

Hypothesis AF : art_facts RT.
Hypothesis AF_IXIT : forall Σ m, ART RT Σ m -> ixit_rt (rt_sp0 RT Σ) m.
Hypothesis AF_CTR : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
  (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> ~ (LSAN_CTR <= bv_unsigned a < LSAN_CTR + 4) -> m' a = m a) ->
  rw_cells asegs m' LSAN_CTR [C4 (Z_to_bv 64 0)] -> wmono asegs m m' -> ART RT Σ m'.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem atcxa_ok : atcxa_icontract.
Proof using AF AF_IXIT AF_CTR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fn obj dso lo
    FDO MST -> -> -> -> Hfn Hobj ((p1 & p2 & f4 & f5 & TBL) & (a4v & a5v & TA)) NL ART0 MI0 CALL.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_IXIT Σ m ART0) as (AI & G88 & CTR & _ & RX & _).
  assert (W1 : evt asegs (icxa_post ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 (Z_to_bv 64 X_AEXGUARD) fn obj m)
                 (entry_st ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 fn) (Z_to_bv 64 obj) (Z_to_bv 64 dso) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_icxa m)).
  { unfold entry_st. rewrite ESP.
    apply (icxa_spec ra (Z_to_bv 64 usp) gp t0 t1 t2 s0 s1 _ _ (Z_to_bv 64 dso) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo fn obj p1 p2 f4 f5 (Z_to_bv 64 X_AEXGUARD) a4v a5v); try reflexivity; rewrite ?(unsigned_lit usp) by ul;
      first [assumption | exact NL | ul]. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  eapply ASTA_conseq; [exact Hc1|]. intros ms PO. unfold icxa_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & ST' & TBL' & TA' & CTR').
  rewrite (unsigned_lit usp) in MU, ST' by ul.

  assert (PRES : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp AEX_W m m').
  { intros a Ha Hout. apply MU. unfold AEX_W in Hout. unfold LSAN_CTR. cbn [outside fst snd] in Hout |- *.
    destruct (aclient_split_c RT AF Σ m usp _ ART0 Ha) as [Hs|Hs]; [split; [ul|]| split; [ul|]]; (split; [lia| split; [lia|]]).
    - split; [| exact I]. ul.
    - split; [| exact I].

      destruct Ha as [H|[H|[H|[H|H]]]]; [ul| | | |].
      + destruct H as [(l & h & Hin & Hx) Hn]. intros [H1 H2]. apply Hn. exists 0x6b0120, 0x6b0140.
        split; [unfold RT_STATIC; solve [repeat (first [left; reflexivity | right])] | lia].
      + destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). ul.
      + destruct H as (f & k & Hin & Hf). pose proof (af_frames_align RT AF Σ m f k ART0 Hin) as [_ Hf0]. ul.
      + destruct H as (f & k & Hin & Hf). pose proof (af_frames_align RT AF Σ m f k ART0 Hin) as [_ Hf0].
        assert (SEGTOP_A / 8 <= f / 8) by (apply Z.div_le_mono; lia). unfold shad, SHB in *. ul. }
  exists m'. split; [rewrite ESP; do 15 eexists; reflexivity|].
  split.
  { split; [| split; [exact MI| split; [exact WM| exact ST']]].
    apply (AF_CTR Σ m m' lo ART0 LOW); [| exact CTR'| exact WM].
    intros a Hna Hnc. apply MU. cbn [outside fst snd]. aex_lits. unfold LSAN_CTR in *.
    split; [| split; [| split; [| split; [lia| exact I]]]].
    -   destruct (Z_lt_le_dec (bv_unsigned a) lo); [ul|].
      destruct (Z_lt_le_dec (bv_unsigned a) USTACK_TOP); [| ul]. exfalso. apply Hna. left. ul.
    - destruct (Z_lt_le_dec (bv_unsigned a) 0x6d0178); [lia|]. destruct (Z_lt_le_dec (bv_unsigned a) (0x6d0178 + 80)); [| lia].
      exfalso. apply Hna. right; left. split; [exists 0x6add10, 0x6d1b18; split; [unfold CLIENT_STATIC; solve [repeat (first [left; reflexivity | right])]| lia]|].
      intros (lq & hq & Hin & Hx). unfold RT_STATIC in Hin. cbn in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - destruct (Z_lt_le_dec (bv_unsigned a) 0x6d0298); [lia|]. destruct (Z_lt_le_dec (bv_unsigned a) (0x6d0298 + 48)); [| lia].
      exfalso. apply Hna. right; left. split; [exists 0x6add10, 0x6d1b18; split; [unfold CLIENT_STATIC; solve [repeat (first [left; reflexivity | right])]| lia]|].
      intros (lq & hq & Hin & Hx). unfold RT_STATIC in Hin. cbn in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
  split; [exact PRES|].
  split; [exists p1, p2; exact TBL'| exact TA'].
Qed.
End Contract.
