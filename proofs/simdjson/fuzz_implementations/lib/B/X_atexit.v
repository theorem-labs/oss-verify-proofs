(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import R_small X_aexdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Local Ltac fold_b :=
  repeat match goal with
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sxb (Z_to_bv 8 z))) in
        replace (sxb (Z_to_bv 8 z)) with (Z_to_bv 64 v : word) by (vm_compute; reflexivity)
  | |- context [(fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 ?z)] => is_Zlit z;
        change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 z)) with (Z_to_bv 64 z : word)
  end.

Local Ltac norm_lits := repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (a + b) in change (a + b) with v end.
Local Ltac ystep := lstep; fold_sx32; fold_b; fold_closed_in_goal; try (first [if_true | if_false]).
Local Ltac ysteps_to p := repeat (tryif at_pc p then fail else ystep).

Definition AEX_HRA : Z := 0x16052c.
Definition FOE_BODY : Z := 0x160508.
Definition X_EXIT_FOE_RET : Z := 0x1607bc.
Definition LIBC_NLX : Z := 0x6de67b.
Definition SANCOV_FLAG : Z := 0x21b820.

Definition foe_frame (j8 : list byte) (xs3 xs2 xs1 xs0 xra : word) : list cell := [CB 8 j8; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra].
Definition SEGTOP_A' : Z := 0x6e0000.

Lemma foe_entry_6 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A' <= lo ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 6 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 5) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (foe_frame j8 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m' AEX (aex_tbl 5 p1 p2 f3 f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args a3v a4v a5v))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 X_FUNCS_ON_EXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros ST LO LOLO NL TBL TA MI. aex_lits. unfold SEGTOP_A', LIBC_NLX, FOE_BODY, foe_frame in *. norm_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  ysteps_to 0x1604fc%Z.
  ysteps_to 0x160508%Z.
  sys_finish. all: first [eexact FR | idtac].
Qed.

Lemma foe_entry_4 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A' <= lo ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 4 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 3) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (foe_frame j8 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m' AEX (aex_tbl 3 p1 p2 f3 f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args a3v a4v a5v))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 X_FUNCS_ON_EXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros ST LO LOLO NL TBL TA MI. aex_lits. unfold SEGTOP_A', LIBC_NLX, FOE_BODY, foe_frame in *. norm_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  ysteps_to 0x1604fc%Z.
  ysteps_to 0x160508%Z.
  sys_finish. all: first [eexact FR | idtac].
Qed.

Lemma foe_entry_3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A' <= lo ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 3 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j8 : list byte) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 2) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (foe_frame j8 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m' AEX (aex_tbl 2 p1 p2 f3 f4 f5) /\ rw_cells bsegs m' AEX_A0 (aex_args a3v a4v a5v))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 X_FUNCS_ON_EXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros ST LO LOLO NL TBL TA MI. aex_lits. unfold SEGTOP_A', LIBC_NLX, FOE_BODY, foe_frame in *. norm_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  ysteps_to 0x1604fc%Z.
  ysteps_to 0x160508%Z.
  sys_finish. all: first [eexact FR | idtac].
Qed.

Lemma foe_call_5 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 5 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) a5v a5v a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) f5 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc f5) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 5) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_call_4 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 4 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) a4v a4v a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) f4 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc f4) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 4) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_call_3 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 3 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) a3v a3v a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) f3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc f3) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 3) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_call_2 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 2 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 0) (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) (Z_to_bv 64 X_ATCXA) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 X_ATCXA)) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 2) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_call_1 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 1 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_IOS) (Z_to_bv 64 AEX_IOS) a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) (Z_to_bv 64 X_IOSDTOR) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 X_IOSDTOR)) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 1) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_call_0 : forall (ra gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word),
  0 <= usp < 2^64 ->
  rw_cells bsegs m AEX (aex_tbl 0 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 X_COVDUMP) (Z_to_bv 64 X_COVDUMP) a1' a2' a3 a4 a5 a6 a7
                    (Z_to_bv 64 AEX) (Z_to_bv 64 X_CALL) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 X_CALL)) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until a5v. intros RSP TBL TA MI. aex_lits. unfold FOE_BODY, AEX_HRA in *.
  norm_lits.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160524%Z.
  ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma foe_ret_5 : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 5 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 4) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 4 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros RSP NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160540%Z. ystep.
  sys_finish.
Qed.

Lemma foe_ret_4 : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 4 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 3) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 3 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros RSP NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160540%Z. ystep.
  sys_finish.
Qed.

Lemma foe_ret_3 : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 3 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 2) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 2 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros RSP NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160540%Z. ystep.
  sys_finish.
Qed.

Lemma foe_ret_2 : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 2 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 1) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 1 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros RSP NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160540%Z. ystep.
  sys_finish.
Qed.

Lemma foe_ret_1 : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (p1 p2 : list byte) (f3 f4 f5 : word),
  0 <= usp < 2^64 ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 1 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' a0' a1' a3' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0' a1' (Z_to_bv 64 0) a3' a4 a5 a6 a7
                    (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FOE_BODY) fc None m' (seg_rom bsegs)
      /\ munch [(AEX + 8, AEX + 12)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' AEX (aex_tbl 0 p1 p2 f3 f4 f5))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until f5. intros RSP NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438 + 8, 0x6de438 + 12)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ysteps_to 0x160540%Z. ystep.
  sys_finish.
Qed.

Lemma foe_last : forall (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 : word) (j8 : list byte) (xs3 xs2 xs1 xs0 xra : word),
  0 <= usp -> usp + 48 < 2^64 ->
  stk bsegs m lo usp -> SEGTOP_A' <= lo -> lo <= usp ->
  rw_cells bsegs m usp (foe_frame j8 xs3 xs2 xs1 xs0 xra) ->
  ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AEX (aex_tbl 0 p1 p2 f3 f4 f5) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR xra (Z_to_bv 64 (usp + 48)) gp tp t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7'
                    xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(AEX, AEX + 1); (AEX + 8, AEX + 12); (AEX + 16, AEX + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (usp + 48)
      /\ rw_cells bsegs m' AEX ([C1 (Z_to_bv 8 1); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); CB 4 p2; C8 (Z_to_bv 64 0)]
                              ++ skipn 6 (aex_tbl 0 p1 p2 f3 f4 f5)))
    (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp tp t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AEX_HRA) fc None m (seg_rom bsegs)).
Proof.
  intros until xra. intros U0 U1 ST LOLO LOU FRX NL TBL MI. aex_lits. unfold FOE_BODY, AEX_HRA, LIBC_NLX, SEGTOP_A', foe_frame in *. cbn [skipn app] in *.
  norm_lits.
  pose proof (munch_refl [(0x6de438, 0x6de438 + 1); (0x6de438 + 8, 0x6de438 + 12); (0x6de438 + 16, 0x6de438 + 24)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  ysteps_to 0x160540%Z. ystep.
  ysteps_to 0x1604f8%Z. ystep.
  ysteps_to 0x160558%Z.
  ysteps_to 0x160570%Z.
  release_frame FRX ST (usp + 48).
  ystep. ysteps_to 0x172d18%Z. ystep.
  sys_finish.
Qed.

Lemma hcall_guard : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a0' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X_AEXGUARD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 X_CALL)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros FL MI. pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA. aex_lits.
  replace (ret_pc (Z_to_bv 64 1443588)) with (Z_to_bv 64 1443588 : word) by (apply bv_eq; vm_compute; reflexivity).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ystep.
  try replace (ret_pc (Z_to_bv 64 739776)) with (Z_to_bv 64 739776 : word) by (apply bv_eq; vm_compute; reflexivity).
  ystep. ystep. ystep. ystep.
  apply evt_done. eexists. reflexivity.
Qed.

Lemma hcall_covdump : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  ro_cells bsegs m SANCOV_FLAG [C1 (Z_to_bv 8 0)] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a0' a1' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X_COVDUMP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc (Z_to_bv 64 X_CALL)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros CV MI. pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA. aex_lits. unfold SANCOV_FLAG in *.
  replace (ret_pc (Z_to_bv 64 1443588)) with (Z_to_bv 64 1443588 : word) by (apply bv_eq; vm_compute; reflexivity).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  ystep.
  try replace (ret_pc (Z_to_bv 64 671736)) with (Z_to_bv 64 671736 : word) by (apply bv_eq; vm_compute; reflexivity).
  ystep. ystep. ystep. ystep. ystep.
  apply evt_done. eexists. eexists. reflexivity.
Qed.

Lemma exit_entry_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo tid : Z),
  tp = Z_to_bv 64 0x6be3e8 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> SEGTOP_A' <= lo ->
  rw_cells bsegs m 0x6be340 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells bsegs m 0x6de658 [C4 (Z_to_bv 64 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 X_EXIT_FOE_RET) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0' t1' t2' a0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 X_FUNCS_ON_EXIT) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (0x6de658, 0x6de65c)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -16)
      /\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m' 0x6de658 [C4 (Z_to_bv 64 tid)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x160758) fc None m (seg_rom bsegs)).
Proof.
  intros until tid. intros -> ST LO LOLO TID HT EXL MI. aex_lits. unfold SEGTOP_A', X_EXIT_FOE_RET in *. norm_lits.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x6de658, 0x6de65c)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
  carve_frame 16%nat ST.
  do 6 lstep.
  rewrite (sx32_small_A tid ltac:(lia)).
  lstep. lstep.

  amo_step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  astep. amo_step. astep.
  astep. fold_sx32. fold_closed_in_goal.
  astep. astep.
  astep.
  astep.
  sys_finish.
Qed.
