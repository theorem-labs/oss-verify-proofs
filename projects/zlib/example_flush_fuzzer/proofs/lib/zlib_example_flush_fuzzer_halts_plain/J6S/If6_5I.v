(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflRod6 InflCtx6 InffastModel InffastCtx InffastSafe IfSpec IfSpec6 If6_1.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition srcn_ok (WN fout : Z) (fr : fromptr) (n : Z) : Prop :=
  match fr with FWin i => 0 <= i /\ i + n <= WN | FOut i => 0 <= i < fout end.

Section Stmts.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Local Notation X := (ffx_of s c r).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation KR := (@KREGS6 sp ZP S I0 P0 WB X (is_lenbits s) (is_distbits s) LC DC).
Local Notation MEMI := (@MEMINV s6_segs mem sp (arr_len (ic_outbuf c)) ZP S P0).

Definition wleg_stmt (hd ex : word) : Prop :=
  forall SV m f (n : nat) wi regs,
    KR regs -> MEMI SV m (f_ob f) -> f_from f = FWin wi ->
    getr regs 1 = zw (WB + wi) -> getr regs 25 = zw (Z.of_nat n) -> getr regs 14 = zw (P0 + f_out f) ->
    (1 <= n)%nat -> Z.of_nat n < 2 ^ 17 -> 0 <= wi -> wi + Z.of_nat n <= WN -> x_beg X <= f_out f -> f_out f + Z.of_nat n <= ON ->
    let f' := cpn X n f in
    exists R m', msteps s6_segs (mkst regs hd m s6_rom) (mkst R ex m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f') /\ getr R 1 = zw (WB + wi + Z.of_nat n)
     /\ (forall k, reg_in k [1; 14; 21; 25]%bv = false -> getr R k = getr regs k).

Definition wleg2_stmt : Prop :=
  forall SV m f regs,
    KR regs -> MEMI SV m (f_ob f) -> f_from f = FWin 0 ->
    getr regs 7 = zw WB -> getr regs 14 = zw (P0 + f_out f) ->
    1 <= x_wnext X -> x_wnext X <= WN -> x_beg X <= f_out f -> f_out f + x_wnext X <= ON ->
    let f' := cpn X (Z.to_nat (x_wnext X)) f in
    exists R m', msteps s6_segs (mkst regs (0x1fbe0 : word) m s6_rom) (mkst R (0x1fbf8 : word) m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
     /\ (forall k, reg_in k [7; 14; 21; 25]%bv = false -> getr R k = getr regs k).

Definition w3_stmt : Prop :=
  forall SV m f regs,
    KR regs -> MEMI SV m (f_ob f) ->
    getr regs 1 = zw (faddr WB P0 (f_from f)) -> getr regs 14 = zw (P0 + f_out f) -> getr regs 26 = zw (f_len f) ->
    0 <= f_len f < 2 ^ 17 -> x_beg X <= f_out f -> f_out f + f_len f <= ON -> srcn_ok WN (f_out f) (f_from f) (f_len f) ->
    let f' := copy_tail X (copy_while3 X f) in
    exists R m', msteps s6_segs (mkst regs (0x1fcd8 : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
     /\ (forall k, reg_in k [1; 7; 14; 21; 25; 26]%bv = false -> getr R k = getr regs k)
     /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.

Definition w3c00_stmt : Prop :=
  forall SV m f regs,
    KR regs -> MEMI SV m (f_ob f) -> f_from f = FWin 0 ->
    getr regs 14 = zw (P0 + f_out f) -> getr regs 26 = zw (f_len f) ->
    0 <= f_len f < 2 ^ 17 -> x_beg X <= f_out f -> f_out f + f_len f <= ON -> srcn_ok WN (f_out f) (f_from f) (f_len f) ->
    let f' := copy_tail X (copy_while3 X f) in
    exists R m', msteps s6_segs (mkst regs (0x1fd38 : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
     /\ (forall k, reg_in k [1; 7; 14; 21; 25; 26]%bv = false -> getr R k = getr regs k)
     /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.

Definition do3_stmt : Prop :=
  forall SV m f regs,
    KR regs -> MEMI SV m (f_ob f) ->
    getr regs 14 = zw (P0 + f_out f + 2) -> getr regs 7 = zw (1 - f_dist f) -> getr regs 27 = zw (f_dist f) -> getr regs 26 = zw (f_len f) ->
    3 <= f_len f < 2 ^ 17 -> 1 <= f_dist f < 2 ^ 17 -> f_dist f <= f_out f -> x_beg X <= f_out f -> f_out f + f_len f <= ON ->
    let f' := copy_tail X (copy_do3 X (fset_from f (FOut (f_out f - f_dist f)))) in
    exists R m', msteps s6_segs (mkst regs (0x1fc0c : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
     /\ (forall k, reg_in k [7; 14; 21; 25; 26]%bv = false -> getr R k = getr regs k)
     /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.
End Stmts.
End FXG.
