(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_defsA Atp_h_defsA Pj_lftoi1A Pj_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition pw_st (usp sp' f : Z) (pc : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma pw_walk0 : forall (usp sp' f A fdv : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s10 s11 t3 t4 t5 t6 : word) (LC1 : list cell) (c13 : list cell) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> SEGTOP_A <= sp' -> sp' + 152 < 2^63 -> 0 < A -> A + 32 < 2^63 -> A mod 8 = 0 -> 0 <= fdv < 2^64 ->
  cells_size LC1 = 128%nat -> rw_cells asegs m sp' (LC1 ++ C8 (Z_to_bv 64 fdv) :: c13) -> shz m A 16 -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (fdv = 0 /\ exists a0' a1', ms = pw_st usp sp' f EL_EXIT2_A ra gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6 F fc m)
      \/ (fdv <> 0 /\ exists a1', ms = pw_st usp sp' f 0xb1918 ra gp t0 t1 t2 (Z_to_bv 64 (A + 8)) a1' a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f EL_VEC2_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH GLO SPH A0 AH A8 FDV SZ FRl SHZ MI.
  unfold pw_st, EL_VEC2_A, EL_EXIT2_A, SEGTOP_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [_ FRl]. rewrite SZ in FRl. change (Z.of_nat 128) with 128 in FRl.
  change (C8 (Z_to_bv 64 fdv) :: c13) with ([C8 (Z_to_bv 64 fdv)] ++ c13) in FRl. apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [FD _].

  chk0 SHZ A. step. if_false.

  zstep. chk0 SHZ (A + 8). step. if_false.

  zstep. step. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia|]. do 2 eexists. atp_st_eq_goal.
  - apply evt_done. right. split; [lia|]. eexists. atp_st_eq_goal.
Qed.

Lemma pw_walk1 : forall (usp sp' f A p0 l0 : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s8 s10 s11 t3 t4 t5 t6 : word) (vrest : list cell)
    (q0 q1 q8 q16 q17 q20 q24 q48 q56 q57 q64 t : list byte) (j0 j1 j2 : list byte) (post : list cell) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 <= sp' -> (f + 1024 <= shad f \/ shad f + 128 <= f) -> f + 1024 <= sp' ->
  SEGTOP_A <= sp' -> sp' + 152 < 2^63 -> 0 < A -> A + 32 < 2^63 -> (A + 32 <= f \/ f + 1024 <= A) -> (A + 32 <= shad f \/ shad f + 128 <= A) -> A + 32 <= sp' ->
  0 <= p0 < 2^64 -> 0 <= l0 < 2^64 ->
  rw_cells asegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: vrest) ->
  rw_cells asegs m sp' (CB 24 j0 :: CB 8 j1 :: CB 8 j2 :: post) ->
  rw_cells asegs m (f + 96) (fz_parser (CB 1 q0) q1 (CB 8 q8) (CB 1 q16) q17 (CB 4 q20) (CB 24 q24) (CB 8 q48) (CB 1 q56) q57 (CB 16 q64)) ->
  rw_cells asegs m (shad f) (el_shadowA 0 (-8) (-8) (-8) t) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pw_st usp sp' f e_asan_memset (Z_to_bv 64 0xb1978) gp t0 t1 t2 (Z_to_bv 64 (f + 120)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
             s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m1
      /\ munch [(sp' + 24, sp' + 40); (f + 96, f + 120); (shad f + 12, shad f + 22)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' (CB 24 j0 :: C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: post)
      /\ rw_cells asegs m1 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) q1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) q17 (C4 (Z_to_bv 64 12)) (CB 24 q24) (CB 8 q48) (CB 1 q56) q57 (CB 16 q64))
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 0 (-8) (-8) t))
    (pw_st usp sp' f 0xb1918 ra gp t0 t1 t2 (Z_to_bv 64 (A + 8)) a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHS SEP FSP GLO SPH A0 AH AF1 AS1 ASP P0 L0 VA FRl FP FS MI.
  unfold pw_st, e_asan_memset, fz_parser, el_shadowA, el_shbytesA, shad, SHB, SEGTOP_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 24, sp' + 40); (f + 96, f + 120); (f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  change (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: vrest) with ([C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 l0)] ++ vrest) in VA.
  apply Sj_stage1_kit.rw_cells_app in VA. destruct VA as [VA _].
  change (CB 24 j0 :: CB 8 j1 :: CB 8 j2 :: post) with ([CB 24 j0] ++ [CB 8 j1; CB 8 j2] ++ post) in FRl.
  apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [FR0 FRl]. apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [FRl FRp].
  cbn [cells_size csize Nat.add] in FRl, FRp. replace (sp' + Z.of_nat 24) with (sp' + 24) in FRl, FRp by lia.

  zstep. ls. zstep. ls.

  do 10 ls.

  zstep. ls. ls. ls. ls. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split.
  { change (CB 24 j0 :: C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: post) with ([CB 24 j0] ++ [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 l0)] ++ post).
    apply Sj_stage1_kit.rw_cells_app. split; [eassumption|]. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 24) with (sp' + 24) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [eassumption| cbn [cells_size csize Nat.add]; eassumption]. }
  split; eassumption.
Qed.

Lemma pw_walk2 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (q1 q17 q24 q48 q56 q57 q64 : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 ->
  rw_cells asegs m (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) q1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) q17 (C4 (Z_to_bv 64 12)) (CB 24 q24) (CB 8 q48) (CB 1 q56) q57 (CB 16 q64)) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pw_st usp sp' f e_asan_memset (Z_to_bv 64 0xb1998) gp t0 t1 t2 (Z_to_bv 64 (f + 160)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 144, f + 153)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) q1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) q17 (C4 (Z_to_bv 64 12)) (CB 24 q24)
                                             (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) q57 (CB 16 q64)))
    (pw_st usp sp' f 0xb1978 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FP MI.
  unfold pw_st, e_asan_memset, fz_parser in *.
  pose proof (munch_refl [(f + 144, f + 153)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. zstep.
  ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma pw_walk3 : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 < 2^63 ->
  rw_cells asegs m (shad f) (el_shadowA 0 0 (-8) (-8) t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = pw_st usp sp' f e_asan_memset (Z_to_bv 64 0xb19b0) gp t0 t1 t2 (Z_to_bv 64 (f + 208)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
             (Z_to_bv 64 (f + 208)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 26, shad f + 28)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (el_shadowA 0 0 0 (-8) t))
    (pw_st usp sp' f 0xb1998 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 208)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SH0 SHH FS MI.
  unfold pw_st, e_asan_memset, el_shadowA, el_shbytesA, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 26, f / 8 + 2147450880 + 28)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma pw_walk7 : forall (usp sp' f buf len : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= sp' -> sp' + 152 < 2^63 -> mem_inv asegs m ->
  evt asegs (eq (pw_st usp sp' f e_pid (Z_to_bv 64 EL_PIDRET_A) gp t0 t1 t2 (Z_to_bv 64 (sp' + 96)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf) (Z_to_bv 64 len) (Z_to_bv 64 0) a6 a7
                 s6 s7 s8 (Z_to_bv 64 buf) (Z_to_bv 64 len) (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb1a34 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 (Z_to_bv 64 buf) (Z_to_bv 64 len) (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH MI. unfold pw_st, e_pid, EL_PIDRET_A.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. atp_st_eq_goal.
Qed.

Lemma pw_walk4 : forall (usp sp' f A p0 l0 p1 l1 : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s10 s11 t3 t4 t5 t6 : word) (vrest : list cell) F fc (m : mem),
  0 < A -> A + 32 < 2^63 -> A mod 8 = 0 -> 0 <= p1 < 2^64 -> 0 <= l1 < 2^64 ->
  rw_cells asegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: C8 (Z_to_bv 64 p1) :: C8 (Z_to_bv 64 l1) :: vrest) ->
  shz m (A + 16) 16 -> cli_got_nothrow m -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (l1 > 1048512 /\ exists a0' a1', ms = pw_st usp sp' f 0xb1a34 ra gp t0 t1 t2 a0' a1' a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 0) (Z_to_bv 64 0) s11 t3 t4 t5 t6 F fc m)
      \/ (l1 <= 1048512 /\ ms = pw_st usp sp' f e_newarr_nt (Z_to_bv 64 0xb19fc) gp t0 t1 t2 (Z_to_bv 64 (l1 + 64)) (Z_to_bv 64 0x2eae8) a2 a3 a4 a5 a6 a7
                                      s6 (Z_to_bv 64 p1) s8 (Z_to_bv 64 A) (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb19b0 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 SHB) s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros A0 AH A8 P1 L1 VA SHZ GOT MI.
  unfold pw_st, e_newarr_nt, cli_got_nothrow in *.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  change (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: C8 (Z_to_bv 64 p1) :: C8 (Z_to_bv 64 l1) :: vrest)
    with ([C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 l0)] ++ [C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 l1)] ++ vrest) in VA.
  apply Sj_stage1_kit.rw_cells_app in VA. destruct VA as [_ VA]. apply Sj_stage1_kit.rw_cells_app in VA. destruct VA as [VA _].
  cbn [cells_size csize Nat.add] in VA. replace (A + Z.of_nat 16) with (A + 16) in VA by lia.

  zstep. chk0 SHZ (A + 16). step. if_false.
  zstep. chk0 SHZ (A + 24). step. if_false.
  zstep. zstep. zstep. step. if_cases K; zify_cond K.
  - zstep. zstep. apply evt_done. left. split; [lia|]. do 2 eexists. atp_st_eq_goal.
  - zstep. zstep. zstep. zstep. zstep. apply evt_done. right. split; [lia|]. atp_st_eq_goal.
Qed.

Lemma pw_walk5 : forall (usp sp' f p l1 : Z) (ra gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < p -> p + l1 + 64 < 2^63 -> 0 <= l1 -> mem_inv asegs m ->
  evt asegs (eq (pw_st usp sp' f e_asan_memset (Z_to_bv 64 0xb1a14) gp t0 t1 t2 (Z_to_bv 64 (p + l1)) (Z_to_bv 64 0) (Z_to_bv 64 64) a3 a4 a5 a6 a7
                 s6 s7 s8 (Z_to_bv 64 p) (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb19fc ra gp t0 t1 t2 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros P0 PH L1 MI. unfold pw_st, e_asan_memset.
  step. if_cases K; zify_cond K; [exfalso; lia|].

  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. atp_st_eq_goal.
Qed.

Lemma pw_walk6 : forall (usp sp' f p p1 l1 : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= l1 < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (l1 = 0 /\ ms = pw_st usp sp' f 0xb1a34 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 p1) s8 (Z_to_bv 64 p) (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m)
      \/ (0 < l1 /\ ms = pw_st usp sp' f e_asan_memcpy (Z_to_bv 64 0xb1a28) gp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 p1) (Z_to_bv 64 l1) a3 a4 a5 a6 a7
                                 s6 (Z_to_bv 64 p1) s8 (Z_to_bv 64 p) (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb1a14 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 p1) s8 (Z_to_bv 64 p) (Z_to_bv 64 l1) s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros L1 MI. unfold pw_st, e_asan_memcpy.
  step. if_cases K; zify_cond K.
  - apply evt_done. left. split; [lia| atp_st_eq_goal].
  - zstep. zstep. zstep. zstep. apply evt_done. right. split; [lia| atp_st_eq_goal].
Qed.

Lemma pw_walk6b : forall (usp sp' f : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  mem_inv asegs m ->
  evt asegs (eq (pw_st usp sp' f 0xb1a34 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb1a28 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof. intros until m. intros MI. unfold pw_st. zstep. apply evt_done. reflexivity. Qed.

Lemma pw_walk8 : forall (usp sp' f rv buf : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 t3 t4 t5 t6 : word) (pre rest : list cell) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> SEGTOP_A <= sp' -> sp' + 152 < 2^63 -> 0 <= rv < 64 -> 0 <= buf < 2^64 ->
  cells_size pre = 112%nat -> rw_cells asegs m sp' (pre ++ C4 (Z_to_bv 64 rv) :: rest) -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (rv = 0 /\ ms = pw_st usp sp' f e_asan_memcpy (Z_to_bv 64 0xb1a68) gp t0 t1 t2 (Z_to_bv 64 (f + 208)) (Z_to_bv 64 (sp' + 96)) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                             (Z_to_bv 64 (f + 208)) (Z_to_bv 64 0) s8 (Z_to_bv 64 buf) s10 (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m)
      \/ (rv <> 0 /\ buf = 0 /\ ms = pw_st usp sp' f EL_EXIT_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 208)) (Z_to_bv 64 rv) s8 (Z_to_bv 64 buf) s10 (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m)
      \/ (rv <> 0 /\ buf <> 0 /\ ms = pw_st usp sp' f e_delarr (Z_to_bv 64 0xb1a74) gp t0 t1 t2 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
                                             (Z_to_bv 64 (f + 208)) (Z_to_bv 64 rv) s8 (Z_to_bv 64 buf) s10 (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f EL_PIDRET_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 208)) s7 s8 (Z_to_bv 64 buf) s10 (Z_to_bv 64 (f + 120)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH GLO SPH R64 BUF SZ FRl MI.
  unfold pw_st, e_asan_memcpy, e_delarr, EL_PIDRET_A, EL_EXIT_A, SEGTOP_A in *.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [_ FRl]. rewrite SZ in FRl. change (Z.of_nat 112) with 112 in FRl.
  change (C4 (Z_to_bv 64 rv) :: rest) with ([C4 (Z_to_bv 64 rv)] ++ rest) in FRl.
  apply Sj_stage1_kit.rw_cells_app in FRl. destruct FRl as [FR _].

  astep. step. if_cases K; zify_cond K.
  -
    step. if_cases K1; zify_cond K1.
    +
      step. if_cases K2; zify_cond K2; [exfalso; lia|]. apply evt_done. right; left. split; [lia|]. split; [lia|]. atp_st_eq_goal.
    +
      zstep. zstep. apply evt_done. right; right. split; [lia|]. split; [lia|]. atp_st_eq_goal.
  -
    zstep. zstep. zstep. zstep. apply evt_done. left. split; [lia|]. replace rv with 0 by lia. atp_st_eq_goal.
Qed.

Lemma pw_walk8b : forall (usp sp' f buf : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= buf < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms =>
      (buf = 0 /\ ms = pw_st usp sp' f EL_DISPATCH_A ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 0) s8 (Z_to_bv 64 buf) s10 s11 t3 t4 t5 t6 F fc m)
      \/ (buf <> 0 /\ ms = pw_st usp sp' f e_delarr (Z_to_bv 64 0xb1a74) gp t0 t1 t2 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 0) s8 (Z_to_bv 64 buf) s10 s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb1a68 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 0) s8 (Z_to_bv 64 buf) s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros BUF MI. unfold pw_st, e_delarr, EL_DISPATCH_A.
  step. if_cases K; zify_cond K.
  -
    step. if_cases K1; zify_cond K1; [|exfalso; lia]. apply evt_done. left. split; [lia| atp_st_eq_goal].
  - zstep. zstep. apply evt_done. right. split; [lia| atp_st_eq_goal].
Qed.

Lemma pw_walk9 : forall (usp sp' f rv : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= rv < 64 -> mem_inv asegs m ->
  evt asegs (eq (pw_st usp sp' f (el_gate_pcA (Z_to_bv 64 rv)) ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 rv) s8 s9 s10 s11 t3 t4 t5 t6 F fc m))
    (pw_st usp sp' f 0xb1a74 ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 (Z_to_bv 64 rv) s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros R64 MI. unfold pw_st, el_gate_pcA, EL_DISPATCH_A, EL_EXIT_A.
  step. if_cases K; zify_cond K.
  - replace (bv_eqb (Z_to_bv 64 rv) (Z_to_bv 64 0)) with true by (symmetry; apply bv_eqb_eq; f_equal; lia). apply evt_done. reflexivity.
  - replace (bv_eqb (Z_to_bv 64 rv) (Z_to_bv 64 0)) with false. 2: { symmetry. apply Bool.not_true_is_false. intros E. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    apply evt_done. reflexivity.
Qed.
