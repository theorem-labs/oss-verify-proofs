(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflRod6 InflCtx6.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition A6_ITABLE : Z := 0x1f188.
Definition ITFR6 : Z := 192.

Definition cty6 (ty : codetype) : Z := match ty with CODES => 0 | LENS => 1 | DISTS => 2 end.

Definition it_ret   (r : Z * arr * Z * Z * arr) : Z   := fst (fst (fst (fst r))).
Definition it_tbl   (r : Z * arr * Z * Z * arr) : arr := snd (fst (fst (fst r))).
Definition it_table (r : Z * arr * Z * Z * arr) : Z   := snd (fst (fst r)).
Definition it_bits  (r : Z * arr * Z * Z * arr) : Z   := snd (fst r).
Definition it_work  (r : Z * arr * Z * Z * arr) : arr := snd r.

Definition it_clob6 : list reg := (1 :: c_clob)%bv.

Definition itable_run6 : Prop :=
  forall (M : word -> option byte) (R : bvmap 5 word) (ty : codetype)
         (S lo codes nx bits pb usp : Z) (ra : word) (lens tbl work : arr),
    getr R 10 = zw (cty6 ty) -> getr R 11 = zw (S + 168 + 2 * lo) -> getr R 12 = zw codes ->
    getr R 13 = zw (S + 160) -> getr R 14 = zw pb -> getr R 15 = zw (S + 808) ->
    getr R 2 = zw usp -> getr R 1 = ra -> ret_ok ra ->
    (pb = S + 136 \/ pb = S + 140) ->
    0 < S -> S + 7176 < 2 ^ 63 -> S mod 16 = 0 -> offimg S 7176 ->
    IMG6_TOP + ITFR6 <= usp -> usp < 2 ^ 63 -> usp <= 2 ^ 47 -> usp mod 16 = 0 -> S + 7176 <= usp - ITFR6 ->
    mapped M (usp - ITFR6) ITFR6 -> mapped M S 7176 -> rod6_clear M ->
    arr_len lens = 320 -> arr_len tbl = 1444 -> arr_len work = 288 ->
    cells s6_segs M (S + 168) 2 2 320 (arr_get lens) ->
    cells s6_segs M (S + 1384) 4 4 1444 (arr_get tbl) ->
    cells s6_segs M (S + 808) 2 2 288 (arr_get work) ->
    cell s6_segs M (S + 160) 8 (S + 1384 + 4 * nx) -> cell s6_segs M pb 4 bits ->
    (forall i, 0 <= i < 320 -> 0 <= arr_get lens i < 65536) ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get tbl i < 2 ^ 32) ->
    (forall i, 0 <= i < 288 -> 0 <= arr_get work i < 65536) ->
    0 <= lo -> lo + codes <= 320 -> 0 <= codes <= 288 ->
    (forall s, 0 <= s < codes -> arr_get lens (lo + s) <= 15) ->
    (ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> arr_get lens (lo + s) <= 7)) ->
    (ty = DISTS -> codes <= 32) ->
    1 <= bits <= 15 -> 0 <= nx -> nx + it_room ty <= 1444 ->
    let r := inflate_table ty lens lo codes tbl nx bits work in
    exists R' M',
      msteps s6_segs (mkst R (zw A6_ITABLE) M s6_rom) (mkst R' ra M' s6_rom)
      /\ getr R' 10 = zw (it_ret r) /\ (it_ret r = 0 \/ it_ret r = 1 \/ it_ret r = -1)
      /\ getr R' 2 = zw usp
      /\ (forall rg : reg, reg_in rg it_clob6 = false -> getr R' rg = getr R rg)
      /\ cells s6_segs M' (S + 168) 2 2 320 (arr_get lens)
      /\ cells s6_segs M' (S + 1384) 4 4 1444 (arr_get (it_tbl r))
      /\ cells s6_segs M' (S + 808) 2 2 288 (arr_get (it_work r))
      /\ cell s6_segs M' (S + 160) 8 (S + 1384 + 4 * it_table r) /\ cell s6_segs M' pb 4 (it_bits r)
      /\ arr_len (it_tbl r) = 1444 /\ arr_len (it_work r) = 288
      /\ (forall i, 0 <= i < 1444 -> 0 <= arr_get (it_tbl r) i < 2 ^ 32)
      /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r) i < 65536)
      /\ (it_ret r = 0 -> 1 <= it_bits r <= 15 /\ nx + 2 <= it_table r <= nx + it_room ty)
      /\ (forall x : word, M x <> None -> M' x <> None)
      /\ (forall x : word,
            ~ (usp - ITFR6 <= bv_unsigned x < usp) -> ~ (S + 808 <= bv_unsigned x < S + 7160) ->
            ~ (S + 160 <= bv_unsigned x < S + 168) -> ~ (pb <= bv_unsigned x < pb + 4) ->
            M' x = M x).
End FXG.
