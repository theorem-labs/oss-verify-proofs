(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs R_small D_kit X_aexdefs X_atexit X_xdefs X_unreg X_fini X_ixdefs X_atcxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation mem := (word -> option byte).
Local Ltac norm_lits := repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (a + b) in change (a + b) with v end.

Local Ltac cutR L := eapply evt_cut; [eapply L | cbv beta; let ms := fresh "ms" in let PO := fresh "PO" in intros ms PO; destruct_exs PO; subst ms].
Local Ltac retpc_lit := repeat match goal with |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.

Definition XPRE_DEPTH : Z := 160.

Lemma exit_pre6 : forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo tid : Z) (p1 p2 : list byte),
  0 <= usp -> usp + 16 <= USTACK_TOP ->
  stk bsegs m lo usp -> lo <= usp - XPRE_DEPTH -> SEGTOP_A <= lo ->
  rw_cells bsegs m 0x6be340 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells bsegs m 0x6de658 [C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 6 p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA)) ->
  rw_cells bsegs m AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0)) ->
  rw_cells bsegs m g_GOT_flags [C8 (Z_to_bv 64 0x187178)] -> rw_cells bsegs m g_flags_cio [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_VEC_OBJ)
                    (Z_to_bv 64 AEX_VEC_OBJ) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 AEX) (Z_to_bv 64 X_VECDTOR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 X_VECDTOR) fc None m' (seg_rom bsegs)
      /\ munch [(usp - XPRE_DEPTH, usp); (AEX + 8, AEX + 12); (0x6de658, 0x6de65c)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (usp + -64)
      /\ rw_cells bsegs m' (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m' (usp + -64) (foe_frame j8 s3 s2 s1 a0 (Z_to_bv 64 X_EXIT_FOE_RET))
      /\ rw_cells bsegs m' 0x6de658 [C4 (Z_to_bv 64 tid)]
      /\ rw_cells bsegs m' AEX (aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA))
      /\ rw_cells bsegs m' AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0)))
    (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160758) fc None m (seg_rom bsegs)).
Proof.
  intros until p2. intros U0 UT ST LO LOLO TID HT EXL NL TBL TA GF CIO MI.
  pose proof foe_entry_6 as FE6. pose proof foe_call_5 as FC5. pose proof foe_ret_5 as FR5. pose proof foe_call_4 as FC4.
  pose proof atcxa_handler_spec as AH.
  aex_lits. unfold XPRE_DEPTH, SEGTOP_A, USTACK_TOP, LIBC_NLX, g_GOT_flags, g_flags_cio, TP_A, AEX_HRA, FOE_BODY, X_EXIT_FOE_RET, foe_frame, SEGTOP_A' in *.
  cbv beta in FE6, FC5, FR5, FC4, AH. norm_lits.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 160, usp); (0x6de438 + 8, 0x6de438 + 12); (0x6de658, 0x6de65c)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  Local Ltac side EU := rewrite ?EU; first [eassumption | reflexivity | unfold SEGTOP_A', XPRE_DEPTH in *; lia].
  assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; lia).
  assert (EU160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
  call (exit_entry_spec ra (Z_to_bv 64 usp)). all: try (side EU). rewrite ?EU in *.

  call FE6. all: try (rewrite ?EU16; side EU). rewrite ?EU16 in *. clear FE6.
  replace (usp + -16 + -48) with (usp + -64) in * by lia.

  cutR FC5. all: try (side EU). clear FC5. retpc_lit.
  call AH. all: try (rewrite ?EU64; side EU). rewrite ?EU64 in *.
  call FR5. all: try (side EU). clear FR5.

  cutR FC4. all: try (side EU). clear FC4. retpc_lit.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_c3 : forall (ra gp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f4 f5 a4v a5v : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 3 p1 p2 (Z_to_bv 64 X_CALL) f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) a4v a5v) ->
  rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a3' s3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1' a0' a1' (Z_to_bv 64 2) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 2 p1 p2 (Z_to_bv 64 X_CALL) f4 f5))
    (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 3) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros U NL TBL TA FL MI.
  pose proof foe_call_3 as FC3. pose proof foe_ret_3 as FR3. pose proof hcall_guard as HG.
  aex_lits. unfold LIBC_NLX, TP_A, AEX_HRA, FOE_BODY, SEGTOP_A' in *. cbv beta in FC3, FR3, HG. norm_lits.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac side3 EU := rewrite ?EU; first [eassumption | reflexivity | lia].
  cutR FC3. all: try (side3 EU). clear FC3.
  cutR HG. all: try (side3 EU). clear HG. retpc_lit.
  call FR3. all: try (side3 EU). clear FR3.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_c2 : forall (ra gp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  stk bsegs m lo usp -> lo <= usp - 96 -> SEGTOP_A <= lo ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 2 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  rw_cells bsegs m g_GOT_flags [C8 (Z_to_bv 64 0x187178)] -> rw_cells bsegs m g_flags_cio [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_IOS) (Z_to_bv 64 AEX_IOS) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) (Z_to_bv 64 X_IOSDTOR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 X_IOSDTOR) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 96, usp); (AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' AEX (aex_tbl 1 p1 p2 f3 f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args a3v a4v a5v))
    (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 2) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros U ST LO LOLO NL TBL TA GF CIO MI.
  pose proof foe_call_2 as FC2. pose proof foe_ret_2 as FR2. pose proof foe_call_1 as FC1. pose proof atcxa_handler_spec as AH.
  aex_lits. unfold LIBC_NLX, TP_A, AEX_HRA, FOE_BODY, SEGTOP_A', SEGTOP_A, g_GOT_flags, g_flags_cio in *. cbv beta in FC2, FR2, FC1, AH. norm_lits.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 96, usp); (0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac side2 EU := rewrite ?EU; first [eassumption | reflexivity | lia].
  cutR FC2. all: try (side2 EU). clear FC2. retpc_lit.
  call AH. all: try (side2 EU). rewrite ?EU in *. clear AH.
  call FR2. all: try (side2 EU). clear FR2.
  cutR FC1. all: try (side2 EU). clear FC1. retpc_lit.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_r4 : forall (gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 4 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 3) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 3 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 AEX_HRA)) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros U NL TBL MI. aex_lits. unfold LIBC_NLX, TP_A, AEX_HRA, FOE_BODY in *. norm_lits. retpc_lit.
  apply (foe_ret_4 gp (Z_to_bv 64 7070696) t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 usp F fc m p1 p2 f3 f4 f5 U NL TBL MI).
Qed.

Lemma exit_post : forall (gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word) (j8 : list byte) (xs3 xs2 xs1 xs0 : word)
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte) (flag dso : word),
  0 <= usp -> usp + 64 < 2^64 ->
  stk bsegs m lo usp -> lo <= usp - 304 -> 0x800d1c58 <= lo ->
  rw_cells bsegs m usp (foe_frame j8 xs3 xs2 xs1 xs0 (Z_to_bv 64 X_EXIT_FOE_RET)) ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 1 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  ro_cells bsegs m SANCOV_FLAG [C1 (Z_to_bv 8 0)] ->

  ro_cells bsegs m 0x1799e0 [C8 (Z_to_bv 64 0xbff10); C8 (Z_to_bv 64 0x5dcf4)] ->
  ro_cells bsegs m 0x180ce8 [C8 (Z_to_bv 64 0x1799f0); C8 (Z_to_bv 64 0x1799e0)] ->
  ro_cells bsegs m 0x17fe98 [C8 (Z_to_bv 64 0x160574); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x181d40 [C8 dso] ->
  ro_cells bsegs m 0x180bb0 [C8 (Z_to_bv 64 0x184df0); C8 (Z_to_bv 64 0x1862b0)] ->
  rw_cells bsegs m 0x186310 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x1862c0 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x187190 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x187230 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x189978 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x18a658 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x1891dc [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x21b520 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x181f40 [C8 (Z_to_bv 64 0x1721b4)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0x184df0 asan_gds ->
  rw_cells bsegs m 0x6bc240 [C1 o1] -> rw_cells bsegs m 0x6bc241 [C1 o2] -> rw_cells bsegs m 0x6bc242 [C1 o3] -> rw_cells bsegs m 0x6bc243 [C1 o4] ->
  rw_cells bsegs m 0x6bc244 [C1 o5] -> rw_cells bsegs m 0x6bc245 [C1 o6] -> rw_cells bsegs m 0x6bc246 [C1 o7] -> rw_cells bsegs m 0x6bc247 [C1 o8] ->
  rw_cells bsegs m 0x6bc248 [C1 o9] -> rw_cells bsegs m 0x6bc249 [C1 o10] -> rw_cells bsegs m 0x6bc24a [C1 o11] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 0x1607c4) (Z_to_bv 64 (usp + 48)) gp (Z_to_bv 64 TP_A) t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7'
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x168690) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 304, usp + 48); (AEX, AEX + 24); (0x186310, 0x186311); (0x1862c0, 0x1862c8); (0x187230, 0x187238);
                (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6bc240, 0x6bc241); (0x6bc241, 0x6bc24b)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (usp + 48))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 AEX_HRA)) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros U0 U1 ST LO LOLO FRX NL TBL TA CV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS
    O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof foe_ret_1 as FR1. pose proof foe_call_0 as FC0. pose proof hcall_covdump as HC. pose proof foe_last as FLT.
  aex_lits. unfold LIBC_NLX, TP_A, AEX_HRA, FOE_BODY, SEGTOP_A', SANCOV_FLAG, X_EXIT_FOE_RET, foe_frame in *. cbv beta in FR1, FC0, HC, FLT.
  cbn [skipn app] in FLT. norm_lits. retpc_lit.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + 48)) = usp + 48) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 304, usp + 48); (0x6de438, 0x6de438 + 24); (0x186310, 0x186311); (0x1862c0, 0x1862c8); (0x187230, 0x187238);
                (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6bc240, 0x6bc241); (0x6bc241, 0x6bc24b)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  Local Ltac sideP EU := rewrite ?EU; first [eassumption | reflexivity | (split; eassumption) | lia].
  call FR1. all: try (sideP EU). clear FR1.
  cutR FC0. all: try (sideP EU). clear FC0.
  cutR HC. all: try (sideP EU). clear HC. retpc_lit.
  call FLT. all: try (sideP EU). clear FLT. retpc_lit.

  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x184df0 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa; rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call fini_spec. all: try (rewrite ?EU48; sideP EU). rewrite ?EU48 in *.

  lstep.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_head4 : forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo tid : Z) (p1 p2 : list byte) (f4 f5 a4v a5v : word),
  0 <= usp -> usp + 16 <= USTACK_TOP ->
  stk bsegs m lo usp -> lo <= usp - XPRE_DEPTH -> SEGTOP_A <= lo ->
  rw_cells bsegs m 0x6be340 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells bsegs m 0x6de658 [C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 3) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 64, usp); (AEX + 8, AEX + 12); (0x6de658, 0x6de65c)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (usp + -64)
      /\ rw_cells bsegs m' (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m' (usp + -64) (foe_frame j8 s3 s2 s1 a0 (Z_to_bv 64 X_EXIT_FOE_RET))
      /\ rw_cells bsegs m' 0x6de658 [C4 (Z_to_bv 64 tid)]
      /\ rw_cells bsegs m' AEX (aex_tbl 3 p1 p2 (Z_to_bv 64 X_CALL) f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) a4v a5v))
    (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160758) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros U0 UT ST LO LOLO TID HT EXL NL TBL TA MI.
  pose proof foe_entry_4 as FE. aex_lits. unfold XPRE_DEPTH, SEGTOP_A, USTACK_TOP, LIBC_NLX, TP_A, FOE_BODY, X_EXIT_FOE_RET, foe_frame, SEGTOP_A' in *.
  cbv beta in FE. norm_lits.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 64, usp); (0x6de438 + 8, 0x6de438 + 12); (0x6de658, 0x6de65c)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac sideH4 EU := rewrite ?EU; first [eassumption | reflexivity | lia].
  call (exit_entry_spec ra (Z_to_bv 64 usp)). all: try (sideH4 EU). rewrite ?EU in *.
  call FE. all: try (rewrite ?EU16; sideH4 EU). rewrite ?EU16 in *. clear FE.
  replace (usp + -16 + -48) with (usp + -64) in * by lia.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_head3 : forall (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo tid : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp -> usp + 16 <= USTACK_TOP ->
  stk bsegs m lo usp -> lo <= usp - XPRE_DEPTH -> SEGTOP_A <= lo ->
  rw_cells bsegs m 0x6be340 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells bsegs m 0x6de658 [C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 3 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 2) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(usp - 64, usp); (AEX + 8, AEX + 12); (0x6de658, 0x6de65c)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (usp + -64)
      /\ rw_cells bsegs m' (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m' (usp + -64) (foe_frame j8 s3 s2 s1 a0 (Z_to_bv 64 X_EXIT_FOE_RET))
      /\ rw_cells bsegs m' 0x6de658 [C4 (Z_to_bv 64 tid)]
      /\ rw_cells bsegs m' AEX (aex_tbl 2 p1 p2 f3 f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args a3v a4v a5v))
    (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160758) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros U0 UT ST LO LOLO TID HT EXL NL TBL TA MI.
  pose proof foe_entry_3 as FE. aex_lits. unfold XPRE_DEPTH, SEGTOP_A, USTACK_TOP, LIBC_NLX, TP_A, FOE_BODY, X_EXIT_FOE_RET, foe_frame, SEGTOP_A' in *.
  cbv beta in FE. norm_lits.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU16 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(usp - 64, usp); (0x6de438 + 8, 0x6de438 + 12); (0x6de658, 0x6de65c)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac sideH3 EU := rewrite ?EU; first [eassumption | reflexivity | lia].
  call (exit_entry_spec ra (Z_to_bv 64 usp)). all: try (sideH3 EU). rewrite ?EU in *.
  call FE. all: try (rewrite ?EU16; sideH3 EU). rewrite ?EU16 in *. clear FE.
  replace (usp + -16 + -48) with (usp + -64) in * by lia.
  norm_lits. sys_finish. all: eassumption.
Qed.

Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x160468) (Z_to_bv 64 94) fc None m (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 0x1607c4) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1607c4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
