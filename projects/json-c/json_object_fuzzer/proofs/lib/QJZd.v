(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QRjH QHnV QCcH QfLs Q0Ek QYIF Q7UD Qhd4 Qwm6 QsKa QlKV Q9O6 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QYIF.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QsKa.Mq5 QsKa.Mq4 QlKV.Mqa QlKV.Mq7.
Import QlKV.Mq2 Q9O6.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoFuzzStmts.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation joptA := (jopt asegs A4F).

Definition jo_post_frameWA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : word) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_chargeA (costB costD : Z) (B B' : bud) : Prop := bB B - costB <= bB B' /\ bD B - costD <= bD B'.

Definition arg_locA (FRS : list frame) (S n : Z) : Prop :=
exists Fr k, In (Fr, k) FRS /\ Fr <= S /\ S + n <= Fr + fr_size k - 8.
Definition cstring_argA (FRS : list frame) (m : word -> option byte) (S : Z) (sb slack : list byte) : Prop :=
bytes_at asegs m S (sb ++ Z_to_bv 8 0 :: slack) /\
Forall (fun b => bv_unsigned b <> 0) sb /\
(- (S + Z.of_nat (length sb) + 1)) mod 8 <= Z.of_nat (length slack) /\
arg_locA FRS S (Z.of_nat (length sb) + 1 + Z.of_nat (length slack)) /\
unpoisoned asegs m A_SB S (Z.of_nat (length sb) + 1).

Definition buffer_argA (FRS : list frame) (m : word -> option byte) (S : Z) (sb : list byte) : Prop :=
bytes_at asegs m S sb /\ arg_locA FRS S (Z.of_nat (length sb)) /\ (sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))).

Definition jo_get_num_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> joptA s m BS p ->
Z.of_nat (length FRS) + 2 < 4096 ->
bv_unsigned sp mod 32 = 0 ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' r (A' : ASA A4L HIx),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_get_double_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> joptA s m BS p ->
Z.of_nat (length FRS) + 1 < 4096 -> costB <= bB B -> costD <= bD B ->
bv_unsigned sp mod 32 = 0 ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
jo_chargeA costB costD B B' ->
joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B' m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_visit_A_stmt (entry uf stk0 stk1 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stk0 + stk1 * odepth s) errv -> joptA s m BS p ->
Z.of_nat (length FRS) + (1 + odepth s) < 4096 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 uf -> a3 = Z_to_bv 64 0 ->
(forall ms' md' m' r (A' : ASA A4L HIx),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
r = 0 -> joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_set_double_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
costB <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud) BS',
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jroot_repA (set_double_root (fn_dbl_to_json_string A4F) r) m' BS' p -> HEAPAx A' (BS' ++ LB) LM FRS B' m' md' ->
(match r with JRtree (Sdouble _) | JRdblx _ => True | _ => BS' = BS end) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition str_lenA (m : word -> option byte) (p n : Z) : Prop :=
exists len : Z, bytes_at asegs m (p + 40) (le8 (Z_to_bv 64 len)) /\ - 2^31 < len < 2^31 /\ Z.abs len <= n.

Definition set_string_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB BS LM : list blk) (FRS : list frame) (B : bud) (costB costD lo p n : Z) (r : jroot) (T : TSet) : Prop :=
forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud) BS',
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
jroot_repA (set_string_root r) m' BS' p -> HEAPAx A' (BS' ++ LB) LM FRS B' m' md' ->
(is_string_root r = true -> str_lenA m' p n) ->
(is_string_root r = false -> BS' = BS) ->
AJ5 A4L HIx A' T md' ms'.

Definition jo_set_string_A_stmt (entry stkb costD : Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p S : Z) (sb slack : list byte) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
cstring_argA FRS m S sb slack -> Z.of_nat (length sb) <= 63 ->
costB (Z.of_nat (length sb)) <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S ->
set_string_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B (costB (Z.of_nat (length sb))) costD lo p (Z.of_nat (length sb)) r T ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_set_string_len_A_stmt (entry stkb costD : Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p S : Z) (sb : list byte) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
buffer_argA FRS m S sb -> Z.of_nat (length sb) <= 63 ->
costB (Z.of_nat (length sb)) <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (Z.of_nat (length sb)) ->
set_string_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B (costB (Z.of_nat (length sb))) costD lo p (Z.of_nat (length sb)) r T ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition heap_presxDA (D : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addrx A4H (hl_volatile A4H) LB SP a -> ~ (D <= a < D + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Definition jo_post_frameDA (D : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_presxDA D (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition root_wA (r : jroot) (m : word -> option byte) (BS : list blk) (p w : Z) : Prop :=
match r with
| JRtree s => exists w0 Y R, jtx s (BS ++ Y) = Some (w0, R) /\ w0 <= w
| JRstrx   => exists L, str_lenA m p L /\ 6 * Z.max L 8 + 2 <= w
| JRdblx _ => 9 <= w
| JRnull   => 0 <= w
end.

Definition copy_ofA (r d : jroot) (CBS : list blk) (w : Z) : Prop :=
copy_of r d /\ match d with JRtree s' => exists w', jtx s' CBS = Some (w', []) /\ w' <= w | _ => True end.

Definition jo_deep_copy_A_stmt (entry scf stk0 stk1 : Z) (costB costD : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D w : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stk0 + stk1 * rdepth r) errv ->
bv_unsigned sp mod 32 = 0 ->
lh_globA m -> jroot_repA r m BS p ->
rw_cells asegs m D [C8 (Z_to_bv 64 0)] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
Z.of_nat (length FRS) + (1 + rdepth r) < 4096 ->
root_wA r m BS p w -> w < 2^28 ->
costB w <= bB B -> costD w <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 scf ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA (costB w) (costD w) B B' -> lh_globA m' -> jroot_repA r m' BS p ->
( (rv = 0 /\ exists (d : jroot) (q : Z) CBS REM,
copy_ofA r d CBS w /\ q <> 0 /\ rw_cells asegs m' D [C8 (Z_to_bv 64 q)] /\ jroot_repA d m' CBS q /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ exists REM, rw_cells asegs m' D [C8 (Z_to_bv 64 0)] /\ HEAPAx A' (BS ++ REM ++ LB) LM FRS B' m' md') ) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_put_xleaf_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
match r with JRdblx _ | JRstrx => True | _ => False end ->
costB <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
rv = 1 -> rw_cells asegs m' A_ERRNO [C4 errv] -> HEAPAx A' LB LM FRS B' m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jhex_A (m : word -> option byte) : Prop := bytes_at asegs m 0xea520 (le8 (Z_to_bv 64 0x23320)).

Definition utf8rep_A (m : word -> option byte) : Prop := bytes_at asegs m 0xea500 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].

Definition jo_get_string_A_stmt (entry : Z) (stkb : jshape -> Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (s : jshape) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stkb s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
costB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (costB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_get_string_null_A_stmt (entry stkb0 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
jo_preA HIx A LB LM FRS B m md sp tp ra lo stkb0 errv ->
(forall ms' md' m' (rv : word),
jo_post_frameWA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] -> HEAPAx A LB LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition tokparse_staticsA (m : word -> option byte) : Prop :=
rw_cells asegs m QlKV.Mq4.LOCCELL_A [C8 (Z_to_bv 64 QlKV.Mq4.GLOBLOC_A)] /\
rw_cells asegs m QlKV.Mq4.LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\
lh_globA m /\ utf8rep_A m.
Definition xlocA (a : Z) : Prop := a4_volatile a \/ (QlKV.Mq4.LOCCELL_A <= a < QlKV.Mq4.LOCCELL_A + 8).

Definition jo_tokparse_A_stmt (entry stkb ura : Z) (costB costD : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBc LM : list blk) (FRS : list frame) (B : bud) (sb lo : Z) (str0 slack : list byte) (errv : word) (u : uwd),
jo_preA HIx A LBc LM FRS B m md sp tp ra lo stkb errv ->
bv_unsigned sp mod 32 = 0 ->
Z.of_nat (length LM) < 8 ->
cstring_argA FRS m sb str0 slack -> Z.of_nat (length str0) < 2^25 ->
tokparse_staticsA m ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 ura) u ->
Z.of_nat (length FRS) + 2 < 4096 ->
costB (Z.of_nat (length str0)) <= bB B -> uw_cost u + costD (Z.of_nat (length str0)) <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 sb ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
tokparse_staticsA m' ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
jo_chargeA (costB (Z.of_nat (length str0))) (uw_cost u + costD (Z.of_nat (length str0))) B B' ->
HEAPAx A' (RBS ++ LK ++ LBc) LM FRS B' m' md' ->
((r = 0 /\ RBS = []) \/
(r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End AJoFuzzStmts.
End RC__1.

End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply Qsw7 QJjn QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewBoolT.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_boolean_A_entry : Z := 0x9bfd8.
Definition newbool_costB : Z := 16 * 48 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newbool_costB <= bB B' /\ bD B <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_boolean_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
bv_unsigned a0 <= 1 ->
newbool_costB <= bB B -> 0 <= bD B ->
(forall ms' md' A', new_obj_A_post Sbool ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA Hb01 BB BD K.
unfold_consts. unfold newbool_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_boolean_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 11 step.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre]; left; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newbool_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
stepz. step.
asan_chkA.
step. step. stepz.
do 6 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
lazymatch goal with SH : ro_cells asegs mc (r / 8 + 2147450880) ?cs |- _ =>
lazymatch cs with [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] => change cs with ([c1; c2] ++ ([c3; c4; c5] ++ [c6])) in SH end;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SH) as [SH01 SHrest]; clear SH; cbn [cells_size csize Nat.add] in SHrest;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SHrest) as [SH234 SH5]; clear SHrest; cbn [cells_size csize Nat.add] in SH5;
replace (r / 8 + 2147450880 + Z.of_nat 2) with ((r + 16) / 8 + A_SB) in SH234 by (unfold A_SB; rewrite (div8_add r 16) by lia; change (16 / 8) with 2; lia);
replace (r / 8 + 2147450880 + Z.of_nat 2 + Z.of_nat 3) with (r / 8 + 2147450885) in SH5 by lia
end;
assert (HPc : HEAPAx A2 ((r, 48) :: LB) LM FRS (charge B (16 * 48 + 512) (uw_cost UWptr)) mc md2) by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r 48 (r + 16) 0 24 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9c070)) with (Z_to_bv 64 0x9c070) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. step.
asan_chkA.
step.
do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST4 (bv_unsigned sp). exact ST4.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6434400 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newbool_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 48)]. split.
* cbn [jval]. exists 0, [], [(r, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists b junk, _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with TLc : rw_cells asegs mf (r + 40) [C4 ?bv; CB 4 ?jk] |- _ =>
exists (bv_unsigned bv), jk; split; [reflexivity|];
unfold jhdr_cells; rewrite Z_to_bv_bv_unsigned; cbn [fn_bool_to_json_string A4F app];
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
change [c1; c2; c3; c4; c5; c6; c7; c8] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7; c8])) end;
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf r _ |- _ => exact H end |];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
split; [| exact TLc];
match goal with H : rw_cells asegs mf (r + 16) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewBoolT.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewInt64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_int64_A_entry : Z := 0x9c330.
Definition newint_costB : Z := 16 * 56 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newint_costB <= bB B' /\ bD B - 1 <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_int64_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', new_obj_A_post Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_int64_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA BB BD K.
unfold_consts. unfold newint_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_int64_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 11 step.

alloc_callA (hiA_malloc A4L HIx) uw UWpaid A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 56 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 56 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 0 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 6 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 56); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
do 6 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
lazymatch goal with SH : ro_cells asegs mc (r / 8 + 2147450880) ?cs |- _ =>
lazymatch cs with [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] => change cs with ([c1; c2] ++ ([c3; c4; c5] ++ [c6; c7])) in SH end;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SH) as [SH01 SHrest]; clear SH; cbn [cells_size csize Nat.add] in SHrest;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SHrest) as [SH234 SH56]; clear SHrest; cbn [cells_size csize Nat.add] in SH56;
replace (r / 8 + 2147450880 + Z.of_nat 2 + Z.of_nat 3) with (r / 8 + 2147450885) in SH56 by lia
end;
assert (HPc : HEAPAx A2 ((r, 56) :: LB) LM FRS (charge B (16 * 56 + 512) (uw_cost UWpaid)) mc md2) by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r 56 (r + 16) 0 24 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9c3cc)) with (Z_to_bv 64 0x9c3cc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
asan_chkA.
step. step.
step.
asan_chkA.
stepz.
do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST4 (bv_unsigned sp). exact ST4.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6434400 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 56)]. split.
* cbn [jval]. exists 0, [], [(r, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists cty v junk, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with TLc : rw_cells asegs mf (r + 40) [C4 _; CB 4 ?jk; C8 ?vv] |- _ =>
exists 0, vv, jk; split; [reflexivity|]; split; [left; reflexivity|];
unfold jhdr_cells; cbn [fn_int_to_json_string A4F app];
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7; c8; c9])) end;
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf r _ |- _ => exact H end |];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
split; [| exact TLc];
match goal with H : rw_cells asegs mf (r + 16) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewInt64.
End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewUint64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_uint64_A_entry : Z := 0x9c9d4.
Definition newint_costB : Z := 16 * 56 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newint_costB <= bB B' /\ bD B - 1 <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_uint64_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', new_obj_A_post Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_uint64_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA BB BD K.
unfold_consts. unfold newint_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_uint64_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 11 step.

alloc_callA (hiA_malloc A4L HIx) uw UWpaid A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 56 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 56 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 0 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 6 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 56); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
do 6 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
lazymatch goal with SH : ro_cells asegs mc (r / 8 + 2147450880) ?cs |- _ =>
lazymatch cs with [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] => change cs with ([c1; c2] ++ ([c3; c4; c5] ++ [c6; c7])) in SH end;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SH) as [SH01 SHrest]; clear SH; cbn [cells_size csize Nat.add] in SHrest;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SHrest) as [SH234 SH56]; clear SHrest; cbn [cells_size csize Nat.add] in SH56;
replace (r / 8 + 2147450880 + Z.of_nat 2 + Z.of_nat 3) with (r / 8 + 2147450885) in SH56 by lia
end;
assert (HPc : HEAPAx A2 ((r, 56) :: LB) LM FRS (charge B (16 * 56 + 512) (uw_cost UWpaid)) mc md2) by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r 56 (r + 16) 0 24 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9ca70)) with (Z_to_bv 64 0x9ca70) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
asan_chkA.
step. step.
step.
asan_chkA.
step. stepz.
do 6 step.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST4 (bv_unsigned sp). exact ST4.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6434400 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 56)]. split.
* cbn [jval]. exists 0, [], [(r, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists cty v junk, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with TLc : rw_cells asegs mf (r + 40) [C4 _; CB 4 ?jk; C8 ?vv] |- _ =>
exists 1, vv, jk; split; [reflexivity|]; split; [right; reflexivity|];
unfold jhdr_cells; cbn [fn_int_to_json_string A4F app];
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
change [c1; c2; c3; c4; c5; c6; c7; c8; c9] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7; c8; c9])) end;
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf r _ |- _ => exact H end |];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
split; [| exact TLc];
match goal with H : rw_cells asegs mf (r + 16) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewUint64.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition printbuf_free_A_entry : Z := 0x9a6d0.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section APbFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_free_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM BS : list blk) (FRS : list frame) (B : bud) (lo p : Z) (errv : word) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - 512 * Z.of_nat (length BS) <= bB B' /\ bD B - (if p =? 0 then 0 else uw_cost u) <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma printbuf_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM BS : list blk) (FRS : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A (BS ++ LB) LM FRS B m md ->
(p <> 0 -> uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u) -> (p <> 0 -> uw_ok A4L (hl_free A4H) ra u) ->
((p = 0 /\ BS = []) \/ (p <> 0 /\ pbufw asegs m BS p)) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
512 * Z.of_nat (length BS) <= bB B -> (if p =? 0 then 0 else uw_cost u) <= bD B ->
(forall ms' md' A', printbuf_free_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM BS FRS B lo p errv u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_free_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK Hp ST LO LOS SPA HT ERR TP RA A0 BB BD K.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
subst a0 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold printbuf_free_A_entry, A_ERRNO in *. a4l.
destruct Hp as [(-> & ->) | (Hp & PB)].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. step. if_true. step. step. step. step.
evt_done5. apply K. unfold printbuf_free_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, (Z_to_bv 64 0), B end. cbn [app] in HP.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
split; [assumption|]. split; [cbn; lia|]. split; [cbn; lia|].
eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
destruct PB as (buf & bpos & size & content & -> & Hbp & Hsz & Hlen & PBS & PBUF).
specialize (UW Hp). specialize (UWK Hp).
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) in BD by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
cbn [app] in HP. cbn [length] in BB. assert (BB' : 1024 <= bB B) by lia. clear BB. rename BB' into BB.
blk_factsA A4L HIx HP p 16 Hal Hlo Hhi Himg_p.
blk_factsA A4L HIx HP buf size Hbal Hblo Hbhi Himg_buf.
shadow_nowA A4L HIx HP p 16 SHp.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p 16 0 p 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
a4l.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. step. if_falsex.
step. step. step.
asan_chk0.
step. step. step. step.

assert (Hne : p <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
alloc_callA (hiA_free A4L HIx) blk buf uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists size. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec buf 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if buf =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec buf 0); reflexivity).
assert (UW2 : uw_at (hiA_top A4L HIx) m2 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply uw_at_heap_pres; [| exact HPR2 | lia]. eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia].
apply Forall_cons; [cbn; lia | apply Forall_nil]. }
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST PBS PBUF SHp GOT CELL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 4 step.
release_frame FR ST2 (bv_unsigned sp).
step.
alloc_callA (hiA_free A4L HIx) blk p uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 16. left. reflexivity. }
all: try (eapply uw_at_pre0; [exact UW2 | lia]). all: try exact UWK.
all: try (intros _; split; [eapply uw_at_pre0; [exact UW2 | lia] | exact UWK]).
all: try (destruct (Z.eqb_spec p 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold printbuf_free_A_post.
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
exists m3, r3, (charge (charge B 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; eassumption|]. split; [exact ST3|]. split; [exact HPR|].
split; [exact ERR3|]. split; [cbn [bB charge length Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. split; [cbn [bD charge]; lia|]. exact HP3.
Qed.
End APbFree.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pbuf_fresh32 (m : word -> option byte) (BS : list blk) (pb : Z) : Prop :=
exists buf post, BS = [(pb, PB_SZ); (buf, 32)] /\ pbuf_core asegs m pb buf 0 32 ([] ++ [Z_to_bv 8 0] ++ post).
Lemma pbuf_fresh32_pbuf : forall m BS pb, pbuf_fresh32 m BS pb -> pbuf asegs m BS pb.
Proof. intros m BS pb (buf & post & E & C). exists buf, 0, 32, [], post. split; [exact E|]. split; [reflexivity | exact C]. Qed.

Section APbNewT.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_new_A_entry : Z := 0x99fb8.

Definition pbnew_costB : Z := 768 + 1024 + 512.

Definition printbuf_new_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - pbnew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, pbuf_fresh32 m' BS r /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

Lemma printbuf_new_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x99fe0) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
pbnew_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', printbuf_new_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_new_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD K.
unfold_consts. unfold pbnew_costB in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold printbuf_new_A_entry in *.
carve_frame 32%nat ST.
do 10 step.

alloc_callA (hiA_calloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 HPR2 ERR2 OUT. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 7 step.
evt_done5. apply K. unfold printbuf_new_A_post.
exists m2, 0, errv2, (charge B (16 * (1 * 16) + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold pbnew_costB; cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat (1 * 16)) with 16%nat in BLK. change (1 * 16) with 16 in HP2. cbn [repeat] in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 16 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 16 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step.
asan_chkA.
step. step. stepz.
asan_chkA.
stepz.
step. step.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms3 mq3 md3 A3 q errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity| lia | cbn; lia]]. a4l.
clear MU WM MI ST2 HPR2 SHr SEP0 SEP1.
replace (ret_pc (Z_to_bv 64 0x9a024)) with (Z_to_bv 64 0x9a024) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
destruct OUT3 as [(-> & _ & HP3) | (Hq & BLKQ & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 16 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
asan_chkA.
stepz. step. if_true. step. step.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 16. left. reflexivity. }
intros ms4 m5 md4 A4 rv4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST3 HPR3 BLK SHr SEP0 SEP1.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
reenterA asegs A4L HIx asegs_wx HP4.
do 7 step.
evt_done5. apply K. unfold printbuf_new_A_post.
exists m5, 0, errv3, (charge (charge (charge B (16 * (1 * 16) + 512) (uw_cost u)) (16 * 32 + 512) (uw_cost UWptr)) 512 (if Z.eqb r 0 then 0 else uw_cost UWptr)).
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR4 | split; [| split; [| left; auto]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM4]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
* unfold pbnew_costB; cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. destruct (Z.eqb r 0); lia.
+
change (Z.to_nat 32) with 32%nat in BLKQ. destruct BLKQ as [junkq BLKQ].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q 32 Hqal Hqlo Hqhi Himg_q.
assert (Hqr0 : q <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 16 HP3 ltac:(apply in_or_app; left; left; reflexivity))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 32 r 16 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hqr0) as Hqr.
shadow_nowA A4L HIx HP3 r 16 SHr. shadow_nowA A4L HIx HP3 q 32 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPr0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPr1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 q 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPrq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 q 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPrq1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 0 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 3 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPq3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 0 q 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPqq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 3 q 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPqq3.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16); (q, q + 32)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
asan_chkA.
step. step. if_falsex.
asan_chkA.
stepz. step. do 6 step.
evt_done5. apply K. unfold printbuf_new_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] =>
exists mf, r, errv3, (charge (charge B (16 * (1 * 16) + 512) (uw_cost u)) (16 * 32 + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [exact ERR3 | split; [| split; [| right]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP3].
* unfold pbnew_costB; cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* split; [exact Hr|]. exists [(r, 16); (q, 32)]. split.
-- unfold pbuf_fresh32. exists q, (skipn 1 junkq).
split; [reflexivity|]. unfold pbuf_core.
split; [lia|]. split; [lia|].
split. { destruct BLKQ as [[Hwf0 _] _]. cbn in Hwf0. destruct Hwf0 as [_ [Hwf0 _]]. rewrite !length_app. cbn [length]. lia. }
split.
++ eapply rw_cells_recast; [exact BLK | cbn; repeat split; reflexivity | cbn; reflexivity | reflexivity].
++ destruct BLKQ as [[Hwf HBq] HWq]. cbn in Hwf. destruct Hwf as [_ [Hwf _]].
split; [split|]; [ | exact HBq | exact HWq ].
cbn. split; [|exact I]. rewrite Hwf. reflexivity.
-- pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3 (perm_swap (r, 16) (q, 32) LB) (Permutation_refl LM) (Permutation_refl FRS)) as HP3'.
eapply (heapA_client_frame A4L HIx);
[ exact HP3'
| eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU); solve_frameW_withA HP3'
| exact WM
| match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end ].
Qed.
End APbNewT.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.Mq0 QlKV.Mqa Qw5U.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition DBUF_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 243; 243; 243; 243].

Lemma dbuf_sh_zero : forall m sh i, bytes_at asegs m sh DBUF_SHW -> 4 <= i < 20 -> bytes_at asegs m (sh + i) [Z_to_bv 8 0].
Proof.
intros m sh i B Hi. pose proof (bytes_at_subG asegs m sh DBUF_SHW (Z.to_nat i) 1 B ltac:(cbn [DBUF_SHW map length]; lia)) as X.
rewrite Z2Nat.id in X by lia.
replace (firstn 1 (skipn (Z.to_nat i) DBUF_SHW)) with [Z_to_bv 8 0] in X; [exact X|].
assert (C : exists k, Z.to_nat i = (4 + k)%nat /\ (k < 16)%nat) by (exists (Z.to_nat i - 4)%nat; lia). destruct C as (k & -> & Hk).
do 16 (destruct k as [|k]; [reflexivity|]). lia.
Qed.
Lemma dbuf_sh_word : forall m sh j, bytes_at asegs m sh DBUF_SHW -> (j = 0 \/ j = 8 \/ j = 16) -> exists bs, length bs = 8%nat /\ bytes_at asegs m (sh + j) bs.
Proof.
intros m sh j B Hj. pose proof (bytes_at_subG asegs m sh DBUF_SHW (Z.to_nat j) 8 B ltac:(cbn [DBUF_SHW map length]; lia)) as X.
rewrite Z2Nat.id in X by lia. eexists. split; [| exact X].
destruct Hj as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma unpoisoned_dbuf : forall m Fr n, Fr mod 256 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) DBUF_SHW -> 0 < n <= 128 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
assert (E4 : (Fr + 32) / 8 = Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (EL : Fr / 8 + 4 <= (Fr + 32 + n - 1) / 8 <= Fr / 8 + 19) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [| split].
- intros g Hg. replace (g + 2147450880) with (Fr / 8 + 2147450880 + (g - Fr / 8)) by lia. apply dbuf_sh_zero; [exact B | lia].
- exists 0. split; [| left; reflexivity].
replace ((Fr + 32 + n - 1) / 8 + 2147450880) with (Fr / 8 + 2147450880 + ((Fr + 32 + n - 1) / 8 - Fr / 8)) by lia. apply dbuf_sh_zero; [exact B | lia].
- intros w Hw.
assert (C : w * 8 = Fr / 8 + 2147450880 + 0 \/ w * 8 = Fr / 8 + 2147450880 + 8 \/ w * 8 = Fr / 8 + 2147450880 + 16) by (Z.div_mod_to_equations; lia).
destruct C as [E | [E | E]]; rewrite E; apply dbuf_sh_word; [exact B | tauto | exact B | tauto | exact B | tauto].
Qed.

Lemma abs63z : forall x : word, Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1 = bv_unsigned x mod 2^63.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
rewrite Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations; lia.
Qed.
Lemma abs63z_ltu : forall (x : word) k, 0 <= k < 2^64 ->
bv_ltu (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1)) (Z_to_bv 64 k) = (bv_unsigned x mod 2^63 <? k).
Proof.
intros x k Hk. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
unfold bv_ltu. rewrite abs63z. rewrite !Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite (Z.mod_small (bv_unsigned x mod 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small k) by lia. reflexivity.
Qed.
Lemma abs63z_lit : forall (x : word) k, bv_unsigned x mod 2^63 = k ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1) = Z_to_bv 64 k.
Proof. intros x k H. rewrite abs63z, H. reflexivity. Qed.

Lemma inf_bits : forall x : word, bv_unsigned x mod 2^63 = 0x7FF0000000000000 ->
x = Z_to_bv 64 0x7FF0000000000000 \/ x = Z_to_bv 64 0xFFF0000000000000.
Proof.
intros x H. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
assert (D : bv_unsigned x / 2^63 = 0 \/ bv_unsigned x / 2^63 = 1) by (Z.div_mod_to_equations; lia).
destruct D as [D|D]; [left|right]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; replace (bv_modulus 64) with (2^64) by reflexivity;
rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia.
Qed.

Lemma fsaved_set_tmp : forall F F' (k : bv 5) v,
fsaved F F' -> ~ In (bv_unsigned k) FSAVED -> fsaved F (bvmap_set k v F').
Proof.
intros F F' k v H Hk j Hj. rewrite QEpW.reg_get_set_other; [apply H; exact Hj|].
intros E. apply Hk. rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 5) with 32 by reflexivity. cbn in Hj.
repeat (destruct Hj as [<-|Hj]; [cbn; tauto|]). destruct Hj.
Qed.
Ltac fsaved_tmp := repeat (apply fsaved_set_tmp; [| vm_compute; intuition discriminate]); first [apply fsaved_refl | assumption].
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MuslAMemcpy.
Hypothesis OBL_REAL_MEMCPY : real_memcpy_specZ_stmt.

Lemma real_memcpy_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= S < 2^64 -> S + n <= 2^64 -> 0 <= n < 2^63 ->
bytes_at asegs m S src -> length src = Z.to_nat n ->
rw_cells asegs m D [CB (Z.to_nat n) junk] -> (S + n <= D \/ D + n <= S) -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn HS HSn Hn SRC SRCL DST DISJ MI.
pose proof (OBL_REAL_MEMCPY ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as X.
rewrite (unsigned_lit D), (unsigned_lit S), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. cbn beta in P. rewrite ?(unsigned_lit D), ?(unsigned_lit S), ?(unsigned_lit n) in P by lia. exact P.
Qed.

Lemma amemcpy_sound_U : amemcpy_spec_U.
Proof.
unfold amemcpy_spec_U.
intros until Q. intros UPd0 UPs0 RT Hd0 Hd47 Hs0 Hs47 Hdlo Hslo Ha0 Ha1 Ha2 Hn Hsz Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC]. apply Forall_cons_iff in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [REALM RTC]. cbn [fst snd] in GOTF, FLAG, REALM.
do 56 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in REALM. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf07d9 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.

stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMCPY_U. carve_frame 72%nat ST.
do 12 step.

unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.

assert (TAIL2G : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 w7 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -72) ->
rw_cells asegs mz (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] -> bytes_at asegs mz s src ->
ro_cells asegs mz 0xe7da8 [C8 (Z_to_bv 64 0xdb34c)] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2144)) w5 w6 w7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x61834) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 w7 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz SRCz REALMz.
clear GOTF REALM GOT CELL FLAGc MU WM MU0 ST FR DST SRC1 MI.
step. step. step.
(call real_memcpy_specZ); [ lia | lia | lia | lia | lia | exact SRCz | exact SRCL | exact DSTz | lia | assumption | ].
do 12 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ src] |- _ => exact H end
| match goal with H : bytes_at _ ?mf s src |- _ => exact H end
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
clear UPd0 UPs0.
do 4 step. if_false.
step. step.
step. step.
subst n. rewrite !Z.add_0_r in *.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD0 : evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 0)
(zxb (Z_to_bv 8 1)) a4 a5 a6 a7 s2 (Z_to_bv 64 d) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 s) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x617a0) fc None mc (seg_rom asegs)))
end.
{ step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step. change (0 + -65) with (-65). if_true.
step. if_false. step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_true.
step. if_false. step.
eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1 | exact REALM]. }
step.
destruct (Z.eq_dec d s) as [Heq | Hne].
- if_truex. exact AD0.
- if_falsex. step.
destruct (Z.lt_ge_cases s d) as [Hlt | Hge].
+ if_falsex. step. if_falsex. exact AD0.
+ if_truex. exact AD0. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RT1 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]])
end.
destruct Hsz as [Hsz | [AMd AMs]]; [lia|].
do 4 step. if_false.
step. step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ADB : evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(zxb (Z_to_bv 8 1)) a4 a5 a6 a7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x617a0) fc None mc (seg_rom asegs)))
end.
{ step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step. if_truex.
step. if_truex.
do 5 step.
step.
stash SRC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := s) (n := n) (lo := lo);
[ exact UPs1 | exact RT1 | exact AMs | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (SRC2 : bytes_at asegs m2 s src)
by (unstash SRC1; eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC1.
assert (UPd2 : unpoisoned asegs m2 A_SB d n).
{ eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia].
eapply munch_trans; [exact MU0 | eapply munch_weaken; [| exact MU2]]. unfold sub_fp; cbn [outside]; intros; lia. }
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x61ae8)) with (Z_to_bv 64 0x61ae8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_truex.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ exact UPd2 | exact RT2 | exact AMd | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
assert (SRC3 : bytes_at asegs m3 s src)
by (unstash SRC2; eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC2.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x61b88)) with (Z_to_bv 64 0x61b88) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL2G; [exact MU | exact WM | exact MI3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR | exact DST | exact SRC3 | exact REALM]. }
clear UPs1 RT1.
step. if_falsex.
step.
destruct Hdisj as [Hsd|Hds].
- if_falsex. step. if_falsex. exact ADB.
- if_truex. exact ADB. }

assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPd1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |]
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.
do 4 step. if_false.
step. step.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL2 : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61834) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1 | exact REALM])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7 s2 (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61b5c) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOT CELL Hh HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply TAIL2
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x617ec) fc None mc (seg_rom asegs)))
end.
{ intros x3 x4 x5 x6 x7;
clear V1c V2c GS0 GOTF FLAGc Hh REALM HRLs;
step; step; rewrite (unsigned_lit d) by lia; rewrite (lxor_ones64 d) by lia; if_falsex;
step; step; rewrite (size_test_n n) by lia; cbv iota;
do 3 step;
step; replace (d + n + -1) with (d + n - 1) by lia;
do 2 step; do 2 step; do 2 step;
sh_norm;
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia;
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLd as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (d + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply TAIL2
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ])
|  apply TAIL2 ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61ab8) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOT CELL Hg REALM TAIL2 LOOP2 HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD : forall x3 : word, evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 a4 a5 a6 a7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x617a0) fc None mc (seg_rom asegs)))
end.
{ intros x3;
clear W1c W2c GR0 GOTF FLAGc Hg REALM TAIL2 LOOP2 HRLd;
step; step; rewrite (unsigned_lit s) by lia; rewrite (lxor_ones64 s) by lia; if_falsex;
step; step; step; rewrite (size_test_n n) by lia; cbv iota;
do 3 step;
step; replace (s + n + -1) with (s + n - 1) by lia;
do 2 step; do 2 step; do 2 step;
sh_norm;
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia;
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((s + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLs as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (s + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((s + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply MID
| if_falsex; replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia;
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia ])
|  apply MID ]. }

clear W1c W2c V1c V2c GR0 GS0 GOTF FLAGc GOT CELL Hg Hh REALM TAIL2 LOOP2 MID LOOP1 HRLd HRLs.
step. if_falsex.
step.
destruct Hdisj as [Hsd|Hds].
- if_falsex. step. if_falsex. apply AD.
- if_truex. apply AD.
Qed.
End MuslAMemcpy.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 Qw5U.Mq4 QXUB.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma asan_inited_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x69bd0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG K.
do 5 step.
match goal with |- context [v_sltiu ?x 1] => replace (v_sltiu x 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity) end.
step. exact K.
Qed.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf07d9 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aae0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma strlen_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (str slack : list byte),
0 <= A < 2^64 ->
bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ bytes_at asegs m' A (str ++ Z_to_bv 8 0 :: slack))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb9b0) fc None m (seg_rom asegs)).
Proof.
intros until slack. intros HA STR NONUL PAD MI.
pose proof (strlen_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack) as X.
rewrite (unsigned_lit A) in X by lia.
eapply evt_mono; [eapply X; [exact STR | exact NONUL | exact PAD | exact MI] |].
intros ms' P. unfold strlen_post in P. rewrite ?(unsigned_lit A) in P by lia. exact P.
Qed.

Section MuslAStrlen.

Lemma astrlen_sound_U : astrlen_spec_U.
Proof.
unfold astrlen_spec_U.
intros until Q. intros UP RT Hs0 Hs47 Hslo Ha0 NONUL Hlen40 Hlen STR PAD ST LO LOS SPA MI RA K.
subst a0. unfold_consts. word_range sp SPR.
remember (Z.of_nat (length str)) as len eqn:Elen.
pose proof (bytes_at_bound _ _ _ _ STR) as ABs. rewrite length_app in ABs. cbn [length] in ABs.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [INITED RTC].
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [GOTFL RTC].
apply Forall_cons_iff in RTC as [REALS RTC]. apply Forall_cons_iff in RTC as [RSTR RTC]. cbn [fst snd] in INITED, REALS, GOTFL, RSTR.
do 53 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in REALS. apply ro_C8_of_bytes_at in GOTFL. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
assert (RSTRc : ro_cells asegs m 0x181723 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact RSTR]). clear RSTR.
stash STR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_STRLEN_STUB_U. carve_frame 64%nat ST.
step.
do 12 step.
step.
apply asan_inited_spec; [exact MI | assumption |].
replace (ret_pc (Z_to_bv 64 0x4fa40)) with (Z_to_bv 64 0x4fa40) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (bv_unsigned sp - 2144 - 16) with (bv_unsigned sp - 2160) in * by lia.
replace (ret_pc (Z_to_bv 64 0x4fa48)) with (Z_to_bv 64 0x4fa48) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 5 step.

unstash STR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STR1 : bytes_at asegs mc s (str ++ Z_to_bv 8 0 :: slack))
by (eapply bytes_at_transport; [exact STR | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
clear STR.
call strlen_specZ; [lia | exact STR1 | exact NONUL | rewrite <- Elen; exact PAD | assumption |].
rewrite <- ?Elen.
step. if_false.
do 4 step. if_false.
step.
step. step. step.
step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step.

assert (TAILG : forall (xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 z5 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp q0 q1 q2 sp w1 (Z_to_bv 64 len) y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2136)) z5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x4fac4) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 z5 q3 q4 q5 q6 mz MUz WMz MIz STRz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
try match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
do 11 step.
eapply K; [exact MUz | exact WMz | exact MIz | exact STRz | release_frame FRz STz (bv_unsigned sp); exact STz]. }
step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
destruct Hlen as [Hlen | AM]; [lia|].
clear GOT CELL.
step.
step. if_truex.
step. step. step.
match goal with H : bytes_at _ _ s (str ++ _) |- _ => rename H into STRc; stash STRc end.
try match goal with H : bytes_at _ _ s (str ++ _) |- _ => clear H end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc |- _ =>
eapply region_is_poisoned_sound_U with (s := s) (n := len + 1) (lo := lo);
[ eapply unpoisoned_transport; [exact UP | exact MUc | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s (len + 1)); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MUc | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]
| exact AM | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| assumption
| rewrite unsigned_lit by lia; reflexivity | ]
end end.
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
assert (STR3 : bytes_at asegs m3 s (str ++ Z_to_bv 8 0 :: slack))
by (unstash STRc; eapply bytes_at_transport; [exact STRc | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
clear STRc.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x4fbe0)) with (Z_to_bv 64 0x4fbe0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
step. step.
lazymatch goal with MUc : munch _ m m3 |- _ => lazymatch goal with WMc : wmono _ m m3 |- _ =>
eapply TAILG; [exact MUc | exact WMc | exact MI3 | exact STR3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR]
end end. }

if_falsex.
assert (Hh : s / 8 <= (s + len) / 8 <= s / 8 + 8) by (Z.div_mod_to_equations; lia).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB s (len + 1))
by (eapply unpoisoned_transport; [exact UP | match goal with H : munch _ m mc |- _ => exact H end
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB s (len + 1)); try eassumption; unfold A_SB; lia])
end.
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + len) / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + len) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP1); lia |];
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + len) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv); replace (s + (len + 1) - 1) with (s + len) in Hro, Hv by lia;
exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UP UP1.
do 3 step.
step. replace (len + s) with (s + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
replace (2147450880 + (s + len) / 8) with ((s + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((s + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall (p0 p1 p2 y1 y2 y3 y4 y5 y6 y7 z5 p3 p4 p5 p6 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x4fa5c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp p0 p1 p2 sp (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 s) (Z_to_bv 64 0x181628) (Z_to_bv 64 (bv_unsigned sp + -2136)) z5 s6 s7 s8 s9 s10 s11 p3 p4 p5 p6)
F (Z_to_bv 64 0x4fac4) fc None mc (seg_rom asegs)))
by (intros p0 p1 p2 y1 y2 y3 y4 y5 y6 y7 z5 p3 p4 p5 p6;
lazymatch goal with MUc : munch _ m mc |- _ => lazymatch goal with WMc : wmono _ m mc |- _ =>
eapply TAILG; [exact MUc | exact WMc | assumption | match goal with H : bytes_at _ mc s (str ++ _) |- _ => exact H end
| eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR ] end end)
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP : forall (Kn : nat) (i : Z) (x0 x1 x2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
Z.to_nat ((s + len) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + len) / 8 ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x4fa5c) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp (Z_to_bv 64 (len + 1)) (Z_to_bv 64 0) (Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + len) / 8 + 2147450880)) y3 y4 y5 y6 y7
(Z_to_bv 64 s) (Z_to_bv 64 0x181628) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 len) s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
F (Z_to_bv 64 0x4fbbc) fc None mc (seg_rom asegs)))
end.
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i p0 p1 p2 q3 q4 q5 q6 q7 r3 r4 r5 r6 HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (s / 8 + i + 1) ((s + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. step. step. apply TAIL.
- if_truex. replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }

destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step.
step. rewrite (sxb_small v) by lia. clear HR.
step. rewrite (unsigned_lit (s + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (s / 8) ((s + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. step. step. apply TAIL.
+ if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((s + len) / 8 - s / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((s + len) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (s / 8) ((s + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. step. step. apply TAIL.
+ if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((s + len) / 8 - s / 8 - 0)) 0); lia.
Qed.
End MuslAStrlen.
End RC__1.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import QYIF.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QsKa.Mqe QsKa.Mqd QlKV.Mqj QlKV.Mqh.
Import QlKV.Mq2 Q9O6.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoFuzzStmts.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation joptA := (jopt asegs A4F).

Definition jo_post_frameWA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : word) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_chargeA (costB costD : Z) (B B' : bud) : Prop := bB B - costB <= bB B' /\ bD B - costD <= bD B'.

Definition arg_locA (FRS : list frame) (S n : Z) : Prop :=
exists Fr k, In (Fr, k) FRS /\ Fr <= S /\ S + n <= Fr + fr_size k - 8.
Definition cstring_argA (FRS : list frame) (m : word -> option byte) (S : Z) (sb slack : list byte) : Prop :=
bytes_at asegs m S (sb ++ Z_to_bv 8 0 :: slack) /\
Forall (fun b => bv_unsigned b <> 0) sb /\
(- (S + Z.of_nat (length sb) + 1)) mod 8 <= Z.of_nat (length slack) /\
arg_locA FRS S (Z.of_nat (length sb) + 1 + Z.of_nat (length slack)) /\
unpoisoned asegs m A_SB S (Z.of_nat (length sb) + 1).

Definition buffer_argA (FRS : list frame) (m : word -> option byte) (S : Z) (sb : list byte) : Prop :=
bytes_at asegs m S sb /\ arg_locA FRS S (Z.of_nat (length sb)) /\ (sb <> [] -> unpoisoned asegs m A_SB S (Z.of_nat (length sb))).

Definition jo_get_num_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> joptA s m BS p ->
Z.of_nat (length FRS) + 2 < 4096 ->
bv_unsigned sp mod 32 = 0 ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' r (A' : ASA A4L HIx),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_get_double_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> joptA s m BS p ->
Z.of_nat (length FRS) + 1 < 4096 -> costB <= bB B -> costD <= bD B ->
bv_unsigned sp mod 32 = 0 ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
jo_chargeA costB costD B B' ->
joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B' m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_visit_A_stmt (entry uf stk0 stk1 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (s : option jshape) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stk0 + stk1 * odepth s) errv -> joptA s m BS p ->
Z.of_nat (length FRS) + (1 + odepth s) < 4096 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 uf -> a3 = Z_to_bv 64 0 ->
(forall ms' md' m' r (A' : ASA A4L HIx),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
r = 0 -> joptA s m' BS p -> HEAPAx A' (BS ++ LB) LM FRS B m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_set_double_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
costB <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud) BS',
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
rw_cells asegs m' A_ERRNO [C4 errv] ->
jroot_repA (set_double_root (fn_dbl_to_json_string A4F) r) m' BS' p -> HEAPAx A' (BS' ++ LB) LM FRS B' m' md' ->
(match r with JRtree (Sdouble _) | JRdblx _ => True | _ => BS' = BS end) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition str_lenA (m : word -> option byte) (p n : Z) : Prop :=
exists len : Z, bytes_at asegs m (p + 40) (le8 (Z_to_bv 64 len)) /\ - 2^31 < len < 2^31 /\ Z.abs len <= n.

Definition set_string_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB BS LM : list blk) (FRS : list frame) (B : bud) (costB costD lo p n : Z) (r : jroot) (T : TSet) : Prop :=
forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud) BS',
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
jroot_repA (set_string_root r) m' BS' p -> HEAPAx A' (BS' ++ LB) LM FRS B' m' md' ->
(is_string_root r = true -> str_lenA m' p n) ->
(is_string_root r = false -> BS' = BS) ->
AJ5 A4L HIx A' T md' ms'.

Definition jo_set_string_A_stmt (entry stkb costD : Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p S : Z) (sb slack : list byte) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
cstring_argA FRS m S sb slack -> Z.of_nat (length sb) <= 63 ->
costB (Z.of_nat (length sb)) <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S ->
set_string_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B (costB (Z.of_nat (length sb))) costD lo p (Z.of_nat (length sb)) r T ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_set_string_len_A_stmt (entry stkb costD : Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p S : Z) (sb : list byte) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
buffer_argA FRS m S sb -> Z.of_nat (length sb) <= 63 ->
costB (Z.of_nat (length sb)) <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (Z.of_nat (length sb)) ->
set_string_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB BS LM FRS B (costB (Z.of_nat (length sb))) costD lo p (Z.of_nat (length sb)) r T ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition heap_presxDA (D : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addrx A4H (hl_volatile A4H) LB SP a -> ~ (D <= a < D + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Definition jo_post_frameDA (D : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_presxDA D (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition root_wA (r : jroot) (m : word -> option byte) (BS : list blk) (p w : Z) : Prop :=
match r with
| JRtree s => exists w0 Y R, jtx s (BS ++ Y) = Some (w0, R) /\ w0 <= w
| JRstrx   => exists L, str_lenA m p L /\ 6 * Z.max L 8 + 2 <= w
| JRdblx _ => 9 <= w
| JRnull   => 0 <= w
end.

Definition copy_ofA (r d : jroot) (CBS : list blk) (w : Z) : Prop :=
copy_of r d /\ match d with JRtree s' => exists w', jtx s' CBS = Some (w', []) /\ w' <= w | _ => True end.

Definition jo_deep_copy_A_stmt (entry scf stk0 stk1 : Z) (costB costD : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D w : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stk0 + stk1 * rdepth r) errv ->
bv_unsigned sp mod 32 = 0 ->
lh_globA m -> jroot_repA r m BS p ->
rw_cells asegs m D [C8 (Z_to_bv 64 0)] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
Z.of_nat (length FRS) + (1 + rdepth r) < 4096 ->
root_wA r m BS p w -> w < 2^28 ->
costB w <= bB B -> costD w <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 scf ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA (costB w) (costD w) B B' -> lh_globA m' -> jroot_repA r m' BS p ->
( (rv = 0 /\ exists (d : jroot) (q : Z) CBS REM,
copy_ofA r d CBS w /\ q <> 0 /\ rw_cells asegs m' D [C8 (Z_to_bv 64 q)] /\ jroot_repA d m' CBS q /\
HEAPAx A' (BS ++ CBS ++ REM ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ exists REM, rw_cells asegs m' D [C8 (Z_to_bv 64 0)] /\ HEAPAx A' (BS ++ REM ++ LB) LM FRS B' m' md') ) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_put_xleaf_A_stmt (entry stkb costB costD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (r : jroot) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo stkb errv -> jroot_repA r m BS p ->
match r with JRdblx _ | JRstrx => True | _ => False end ->
costB <= bB B -> costD <= bD B ->
a0 = Z_to_bv 64 p ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
jo_chargeA costB costD B B' ->
rv = 1 -> rw_cells asegs m' A_ERRNO [C4 errv] -> HEAPAx A' LB LM FRS B' m' md' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jhex_A (m : word -> option byte) : Prop := bytes_at asegs m 0xec940 (le8 (Z_to_bv 64 0x23380)).

Definition utf8rep_A (m : word -> option byte) : Prop := bytes_at asegs m 0xec920 [Z_to_bv 8 239; Z_to_bv 8 191; Z_to_bv 8 189].

Definition jo_get_string_A_stmt (entry : Z) (stkb : jshape -> Z) (costB : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (s : jshape) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (stkb s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
costB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (costB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_get_string_null_A_stmt (entry stkb0 : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
jo_preA HIx A LB LM FRS B m md sp tp ra lo stkb0 errv ->
(forall ms' md' m' (rv : word),
jo_post_frameWA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
rw_cells asegs m' A_ERRNO [C4 errv] -> HEAPAx A LB LM FRS B m' md' ->
AJ5 A4L HIx A T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition tokparse_staticsA (m : word -> option byte) : Prop :=
rw_cells asegs m QlKV.Mqe.LOCCELL_A [C8 (Z_to_bv 64 QlKV.Mqe.GLOBLOC_A)] /\
rw_cells asegs m QlKV.Mqe.LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] /\
lh_globA m /\ utf8rep_A m.
Definition xlocA (a : Z) : Prop := a4_volatile a \/ (QlKV.Mqe.LOCCELL_A <= a < QlKV.Mqe.LOCCELL_A + 8).

Definition jo_tokparse_A_stmt (entry stkb ura : Z) (costB costD : Z -> Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LBc LM : list blk) (FRS : list frame) (B : bud) (sb lo : Z) (str0 slack : list byte) (errv : word) (u : uwd),
jo_preA HIx A LBc LM FRS B m md sp tp ra lo stkb errv ->
bv_unsigned sp mod 32 = 0 ->
Z.of_nat (length LM) < 8 ->
cstring_argA FRS m sb str0 slack -> Z.of_nat (length str0) < 2^25 ->
tokparse_staticsA m ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 ura) u ->
Z.of_nat (length FRS) + 3 < 4096 ->
costB (Z.of_nat (length str0)) <= bB B -> uw_cost u + costD (Z.of_nat (length str0)) <= bD B ->
frm0 fc -> a0 = Z_to_bv 64 sb ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (gp' : word) (r : Z) (errv' : word) (RBS LK : list blk),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
tokparse_staticsA m' ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
jo_chargeA (costB (Z.of_nat (length str0))) (uw_cost u + costD (Z.of_nat (length str0))) B B' ->
HEAPAx A' (RBS ++ LK ++ LBc) LM FRS B' m' md' ->
((r = 0 /\ RBS = []) \/
(r <> 0 /\ exists s, jval asegs A4F s m' RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * (Z.of_nat (length str0) + 1) + 64)) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End AJoFuzzStmts.
End RC__1.

End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewBoolT.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_boolean_A_entry : Z := 0x9d828.
Definition newbool_costB : Z := 16 * 48 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newbool_costB <= bB B' /\ bD B <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_boolean_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
bv_unsigned a0 <= 1 ->
newbool_costB <= bB B -> 0 <= bD B ->
(forall ms' md' A', new_obj_A_post Sbool ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_boolean_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA Hb01 BB BD K. pose proof OBL_AMEMSET as OBL_unused_on_B.
unfold_consts. unfold newbool_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_boolean_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 10 bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre]; left; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newbool_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstepz. bstep.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstep.
do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newbool_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 48)]. split.
* cbn [jval]. exists 0, [], [(r, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists b junk, _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with BLKc : rw_cells asegs mf r [_; _; _; _; _; _; C4 ?bv; CB 4 ?jk] |- _ =>
exists (bv_unsigned bv), jk; split; [reflexivity|];
unfold jhdr_cells; rewrite Z_to_bv_bv_unsigned; cbn [fn_bool_to_json_string A4F app]; exact BLKc
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewBoolT.
End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewInt64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_int64_A_entry : Z := 0x9dbdc.
Definition newint_costB : Z := 16 * 56 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newint_costB <= bB B' /\ bD B - 1 <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_int64_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', new_obj_A_post Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_int64_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA BB BD K. pose proof OBL_AMEMSET as OBL_unused_on_B.
unfold_consts. unfold newint_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_int64_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 10 bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWpaid A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 56 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 56 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 0 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 6 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 56); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstep.
bstep. asan_chkA. bstepz.
do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 56)]. split.
* cbn [jval]. exists 0, [], [(r, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].

lazymatch goal with |- exists cty v junk, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with BLKc : rw_cells asegs mf r [_; _; _; _; _; _; C4 _; CB 4 ?jk; C8 ?vv] |- _ =>
exists 0, vv, jk; split; [reflexivity|]; split; [left; reflexivity|];
unfold jhdr_cells; cbn [fn_int_to_json_string A4F app]; exact BLKc
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewInt64.
End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewUint64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Definition json_object_new_uint64_A_entry : Z := 0x9e328.
Definition newint_costB : Z := 16 * 56 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newint_costB <= bB B' /\ bD B - 1 <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_uint64_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newint_costB <= bB B -> 1 <= bD B ->
(forall ms' md' A', new_obj_A_post Sint ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_uint64_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA BB BD K. pose proof OBL_AMEMSET as OBL_unused_on_B.
unfold_consts. unfold newint_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_uint64_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 10 bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWpaid A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 56 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 56 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 0 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 56 6 r 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 56); (lo, bv_unsigned sp - 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstep.
bstep. asan_chkA. bstep. bstepz.
do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 56 + 512) (uw_cost UWpaid)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newint_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 56)]. split.
* cbn [jval]. exists 0, [], [(r, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists cty v junk, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with BLKc : rw_cells asegs mf r [_; _; _; _; _; _; C4 _; CB 4 ?jk; C8 ?vv] |- _ =>
exists 1, vv, jk; split; [reflexivity|]; split; [right; reflexivity|];
unfold jhdr_cells; cbn [fn_int_to_json_string A4F app]; exact BLKc
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewUint64.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition printbuf_free_A_entry : Z := 0x9bcec.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section APbFree.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_free_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM BS : list blk) (FRS : list frame) (B : bud) (lo p : Z) (errv : word) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
bB B - 512 * Z.of_nat (length BS) <= bB B' /\ bD B - (if p =? 0 then 0 else uw_cost u) <= bD B' /\
HEAPAx A' LB LM FRS B' m' md'.

Lemma printbuf_free_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM BS : list blk) (FRS : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A (BS ++ LB) LM FRS B m md ->
(p <> 0 -> uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u) -> (p <> 0 -> uw_ok A4L (hl_free A4H) ra u) ->
((p = 0 /\ BS = []) \/ (p <> 0 /\ pbufw asegs m BS p)) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p ->
512 * Z.of_nat (length BS) <= bB B -> (if p =? 0 then 0 else uw_cost u) <= bD B ->
(forall ms' md' A', printbuf_free_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM BS FRS B lo p errv u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_free_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK Hp ST LO LOS SPA HT ERR TP RA A0 BB BD K.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
subst a0 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold printbuf_free_A_entry, A_ERRNO in *. a4l.
destruct Hp as [(-> & ->) | (Hp & PB)].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. bstep. if_true. bstep. bstep. bstep. bstep.
evt_done5. apply K. unfold printbuf_free_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, (Z_to_bv 64 0), B end. cbn [app] in HP.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia | solve_clientWA A4L HIx HP]. }
split; [assumption|]. split; [cbn; lia|]. split; [cbn; lia|].
eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
destruct PB as (buf & bpos & size & content & -> & Hbp & Hsz & Hlen & PBS & PBUF).
specialize (UW Hp). specialize (UWK Hp).
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) in BD by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
cbn [app] in HP. cbn [length] in BB. assert (BB' : 1024 <= bB B) by lia. clear BB. rename BB' into BB.
blk_factsA A4L HIx HP p 16 Hal Hlo Hhi Himg_p.
blk_factsA A4L HIx HP buf size Hbal Hblo Hbhi Himg_buf.
shadow_nowA A4L HIx HP p 16 SHp.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ p 16 0 p 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
a4l.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. bstep. bstep. bstep.

assert (Hne : p <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
alloc_callA (hiA_free A4L HIx) blk buf uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists size. right. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec buf 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms2 m2 md2 A2 r2 RS VM2 ST2 HPR2 ERR2 HP2. open_ret RS. a4l.
rewrite lb_remove_other in HPR2, HP2 by (cbn; lia). rewrite lb_remove_head in HPR2, HP2.
replace (if buf =? 0 then 0 else uw_cost UWptr) with 0 in HP2 by (destruct (Z.eqb_spec buf 0); reflexivity).
assert (UW2 : uw_at (hiA_top A4L HIx) m2 (bv_unsigned sp) (bv_unsigned s0) u).
{ eapply uw_at_heap_pres; [| exact HPR2 | lia]. eapply (uw_at_mono _ _ _ _ _ _ _ _ UW MU); [| lia].
apply Forall_cons; [cbn; lia | apply Forall_nil]. }
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST PBS PBUF SHp GOT CELL.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
do 4 bstep.
release_frame FR ST2 (bv_unsigned sp).
bstep.
alloc_callA (hiA_free A4L HIx) blk p uw u A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 16. left. reflexivity. }
all: try (eapply uw_at_pre0; [exact UW2 | lia]). all: try exact UWK.
all: try (intros _; split; [eapply uw_at_pre0; [exact UW2 | lia] | exact UWK]).
all: try (destruct (Z.eqb_spec p 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite lb_remove_head in HP3, HPR3.
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) in HP3 by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply K. unfold printbuf_free_A_post.
replace (if p =? 0 then 0 else uw_cost u) with (uw_cost u) by (destruct (Z.eqb_spec p 0); [lia | reflexivity]).
exists m3, r3, (charge (charge B 512 0) 512 (uw_cost u)).
split; [apply ret_statew_same|]. split; [eapply model_vm_only_trans; eassumption|]. split; [exact ST3|]. split; [exact HPR|].
split; [exact ERR3|]. split; [cbn [bB charge length Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. split; [cbn [bD charge]; lia|]. exact HP3.
Qed.
End APbFree.
End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pbuf_fresh32 (m : word -> option byte) (BS : list blk) (pb : Z) : Prop :=
exists buf post, BS = [(pb, PB_SZ); (buf, 32)] /\ pbuf_core asegs m pb buf 0 32 ([] ++ [Z_to_bv 8 0] ++ post).
Lemma pbuf_fresh32_pbuf : forall m BS pb, pbuf_fresh32 m BS pb -> pbuf asegs m BS pb.
Proof. intros m BS pb (buf & post & E & C). exists buf, 0, 32, [], post. split; [exact E|]. split; [reflexivity | exact C]. Qed.

Section APbNewT.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_new_A_entry : Z := 0x9b3fc.

Definition pbnew_costB : Z := 768 + 1024 + 512.

Definition printbuf_new_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - pbnew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, pbuf_fresh32 m' BS r /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

Lemma printbuf_new_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x9b424) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
pbnew_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', printbuf_new_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_new_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD K.
unfold_consts. unfold pbnew_costB in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold printbuf_new_A_entry in *.
carve_frame 32%nat ST.
do 10 bstep.

alloc_callA (hiA_calloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 HPR2 ERR2 OUT. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 7 bstep.
evt_done5. apply K. unfold printbuf_new_A_post.
exists m2, 0, errv2, (charge B (16 * (1 * 16) + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold pbnew_costB; cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat (1 * 16)) with 16%nat in BLK. change (1 * 16) with 16 in HP2. cbn [repeat] in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 16 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 16 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex. bstep. bstep.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstepz.
bstep. bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
intros ms3 mq3 md3 A3 q errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity| lia | cbn; lia]]. a4l.
clear MU WM MI ST2 HPR2 SHr SEP0 SEP1.
replace (ret_pc (Z_to_bv 64 0x9b470)) with (Z_to_bv 64 0x9b470) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
destruct OUT3 as [(-> & _ & HP3) | (Hq & BLKQ & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 16 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
asan_chkA.
bstepz. bstep. if_true. bstep. bstep.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 16. left. reflexivity. }
intros ms4 m5 md4 A4 rv4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST3 HPR3 BLK SHr SEP0 SEP1.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
reenterA asegs A4L HIx asegs_wx HP4.
do 7 bstep.
evt_done5. apply K. unfold printbuf_new_A_post.
exists m5, 0, errv3, (charge (charge (charge B (16 * (1 * 16) + 512) (uw_cost u)) (16 * 32 + 512) (uw_cost UWptr)) 512 (if Z.eqb r 0 then 0 else uw_cost UWptr)).
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR4 | split; [| split; [| left; auto]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM4]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST4 (bv_unsigned sp). exact ST4.
* unfold pbnew_costB; cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. destruct (Z.eqb r 0); lia.
+
change (Z.to_nat 32) with 32%nat in BLKQ. destruct BLKQ as [junkq BLKQ].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q 32 Hqal Hqlo Hqhi Himg_q.
assert (Hqr0 : q <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 16 HP3 ltac:(apply in_or_app; left; left; reflexivity))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 32 r 16 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hqr0) as Hqr.
shadow_nowA A4L HIx HP3 r 16 SHr. shadow_nowA A4L HIx HP3 q 32 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 r 16 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPr0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 r 16 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPr1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 0 q 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPrq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 16 1 q 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPrq1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 0 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 3 r 16 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPq3.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 0 q 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPqq0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 32 3 q 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPqq3.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 16); (q, q + 32)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
asan_chkA.
bstep. bstep. if_falsex.
asan_chkA.
bstepz. bstep. do 6 bstep.
evt_done5. apply K. unfold printbuf_new_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] =>
exists mf, r, errv3, (charge (charge B (16 * (1 * 16) + 512) (uw_cost u)) (16 * 32 + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [exact ERR3 | split; [| split; [| right]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP3].
* unfold pbnew_costB; cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* split; [exact Hr|]. exists [(r, 16); (q, 32)]. split.
-- unfold pbuf_fresh32. exists q, (skipn 1 junkq).
split; [reflexivity|]. unfold pbuf_core.
split; [lia|]. split; [lia|].
split. { destruct BLKQ as [[Hwf0 _] _]. cbn in Hwf0. destruct Hwf0 as [_ [Hwf0 _]]. rewrite !length_app. cbn [length]. lia. }
split.
++ eapply rw_cells_recast; [exact BLK | cbn; repeat split; reflexivity | cbn; reflexivity | reflexivity].
++ destruct BLKQ as [[Hwf HBq] HWq]. cbn in Hwf. destruct Hwf as [_ [Hwf _]].
split; [split|]; [ | exact HBq | exact HWq ].
cbn. split; [|exact I]. rewrite Hwf. reflexivity.
-- pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3 (perm_swap (r, 16) (q, 32) LB) (Permutation_refl LM) (Permutation_refl FRS)) as HP3'.
eapply (heapA_client_frame A4L HIx);
[ exact HP3'
| eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU); solve_frameW_withA HP3'
| exact WM
| match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end ].
Qed.
End APbNewT.
End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QbFI. Import Qhd4. Import Qwm6.Mq4 QlKV.Mqj Qw5U.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition DBUF_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 243; 243; 243; 243].

Lemma dbuf_sh_zero : forall m sh i, bytes_at asegs m sh DBUF_SHW -> 4 <= i < 20 -> bytes_at asegs m (sh + i) [Z_to_bv 8 0].
Proof.
intros m sh i B Hi. pose proof (bytes_at_subG asegs m sh DBUF_SHW (Z.to_nat i) 1 B ltac:(cbn [DBUF_SHW map length]; lia)) as X.
rewrite Z2Nat.id in X by lia.
replace (firstn 1 (skipn (Z.to_nat i) DBUF_SHW)) with [Z_to_bv 8 0] in X; [exact X|].
assert (C : exists k, Z.to_nat i = (4 + k)%nat /\ (k < 16)%nat) by (exists (Z.to_nat i - 4)%nat; lia). destruct C as (k & -> & Hk).
do 16 (destruct k as [|k]; [reflexivity|]). lia.
Qed.
Lemma dbuf_sh_word : forall m sh j, bytes_at asegs m sh DBUF_SHW -> (j = 0 \/ j = 8 \/ j = 16) -> exists bs, length bs = 8%nat /\ bytes_at asegs m (sh + j) bs.
Proof.
intros m sh j B Hj. pose proof (bytes_at_subG asegs m sh DBUF_SHW (Z.to_nat j) 8 B ltac:(cbn [DBUF_SHW map length]; lia)) as X.
rewrite Z2Nat.id in X by lia. eexists. split; [| exact X].
destruct Hj as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma unpoisoned_dbuf : forall m Fr n, Fr mod 256 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) DBUF_SHW -> 0 < n <= 128 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
assert (E4 : (Fr + 32) / 8 = Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (EL : Fr / 8 + 4 <= (Fr + 32 + n - 1) / 8 <= Fr / 8 + 19) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [| split].
- intros g Hg. replace (g + 2147450880) with (Fr / 8 + 2147450880 + (g - Fr / 8)) by lia. apply dbuf_sh_zero; [exact B | lia].
- exists 0. split; [| left; reflexivity].
replace ((Fr + 32 + n - 1) / 8 + 2147450880) with (Fr / 8 + 2147450880 + ((Fr + 32 + n - 1) / 8 - Fr / 8)) by lia. apply dbuf_sh_zero; [exact B | lia].
- intros w Hw.
assert (C : w * 8 = Fr / 8 + 2147450880 + 0 \/ w * 8 = Fr / 8 + 2147450880 + 8 \/ w * 8 = Fr / 8 + 2147450880 + 16) by (Z.div_mod_to_equations; lia).
destruct C as [E | [E | E]]; rewrite E; apply dbuf_sh_word; [exact B | tauto | exact B | tauto | exact B | tauto].
Qed.

Lemma abs63z : forall x : word, Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1 = bv_unsigned x mod 2^63.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
rewrite Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations; lia.
Qed.
Lemma abs63z_ltu : forall (x : word) k, 0 <= k < 2^64 ->
bv_ltu (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1)) (Z_to_bv 64 k) = (bv_unsigned x mod 2^63 <? k).
Proof.
intros x k Hk. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
unfold bv_ltu. rewrite abs63z. rewrite !Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity.
rewrite (Z.mod_small (bv_unsigned x mod 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small k) by lia. reflexivity.
Qed.
Lemma abs63z_lit : forall (x : word) k, bv_unsigned x mod 2^63 = k ->
Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned x) 1))) 1) = Z_to_bv 64 k.
Proof. intros x k H. rewrite abs63z, H. reflexivity. Qed.

Lemma inf_bits : forall x : word, bv_unsigned x mod 2^63 = 0x7FF0000000000000 ->
x = Z_to_bv 64 0x7FF0000000000000 \/ x = Z_to_bv 64 0xFFF0000000000000.
Proof.
intros x H. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
assert (D : bv_unsigned x / 2^63 = 0 \/ bv_unsigned x / 2^63 = 1) by (Z.div_mod_to_equations; lia).
destruct D as [D|D]; [left|right]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; replace (bv_modulus 64) with (2^64) by reflexivity;
rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia.
Qed.

Lemma fsaved_set_tmp : forall F F' (k : bv 5) v,
fsaved F F' -> ~ In (bv_unsigned k) FSAVED -> fsaved F (bvmap_set k v F').
Proof.
intros F F' k v H Hk j Hj. rewrite QEpW.reg_get_set_other; [apply H; exact Hj|].
intros E. apply Hk. rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 5) with 32 by reflexivity. cbn in Hj.
repeat (destruct Hj as [<-|Hj]; [cbn; tauto|]). destruct Hj.
Qed.
Ltac fsaved_tmp := repeat (apply fsaved_set_tmp; [| vm_compute; intuition discriminate]); first [apply fsaved_refl | assumption].
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QXUB.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma asan_inited_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x69fa8) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG K.
do 5 step.
match goal with |- context [v_sltiu ?x 1] => replace (v_sltiu x 1) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity) end.
step. exact K.
Qed.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf2e99 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aeb8) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma strlen_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (str slack : list byte),
0 <= A < 2^64 ->
bytes_at asegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ bytes_at asegs m' A (str ++ Z_to_bv 8 0 :: slack))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xde074) fc None m (seg_rom asegs)).
Proof.
intros until slack. intros HA STR NONUL PAD MI.
pose proof (strlen_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack) as X.
rewrite (unsigned_lit A) in X by lia.
eapply evt_mono; [eapply X; [exact STR | exact NONUL | exact PAD | exact MI] |].
intros ms' P. unfold strlen_post in P. rewrite ?(unsigned_lit A) in P by lia. exact P.
Qed.

Section MuslAStrlen.

Lemma astrlen_sound_U : astrlen_spec_U.
Proof.
unfold astrlen_spec_U.
intros until Q. intros UP RT Hs0 Hs47 Hslo Ha0 NONUL Hlen40 Hlen STR PAD ST LO LOS SPA MI RA K.
subst a0. unfold_consts. word_range sp SPR.
remember (Z.of_nat (length str)) as len eqn:Elen.
pose proof (bytes_at_bound _ _ _ _ STR) as ABs. rewrite length_app in ABs. cbn [length] in ABs.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [INITED RTC].
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [GOTFL RTC].
apply Forall_cons_iff in RTC as [REALS RTC]. apply Forall_cons_iff in RTC as [RSTR RTC]. cbn [fst snd] in INITED, REALS, GOTFL, RSTR.
do 56 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in REALS. apply ro_C8_of_bytes_at in GOTFL. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (INITEDc : ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact INITED]). clear INITED.
assert (RSTRc : ro_cells asegs m 0x183de3 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact RSTR]). clear RSTR.
stash STR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold A_STRLEN_STUB_U. carve_frame 64%nat ST.
step.
do 12 step.
step.
apply asan_inited_spec; [exact MI | assumption |].
replace (ret_pc (Z_to_bv 64 0x4fe18)) with (Z_to_bv 64 0x4fe18) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_false.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply try_asan_init_spec; [exact MI | assumption | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; lia
| lia | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
intros a1x m2 MU2 WM2 MI2 ST1'.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (bv_unsigned sp - 2144 - 16) with (bv_unsigned sp - 2160) in * by lia.
replace (ret_pc (Z_to_bv 64 0x4fe20)) with (Z_to_bv 64 0x4fe20) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 5 step.

unstash STR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STR1 : bytes_at asegs mc s (str ++ Z_to_bv 8 0 :: slack))
by (eapply bytes_at_transport; [exact STR | eassumption | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia])
end.
clear STR.
call strlen_specZ; [lia | exact STR1 | exact NONUL | rewrite <- Elen; exact PAD | assumption |].
rewrite <- ?Elen.
step. if_false.
do 4 step. if_false.
step.
step. step. step.
step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step.

assert (TAILG : forall (xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 z5 q3 q4 q5 q6 : word) mz,
munch [(lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
bytes_at asegs mz s (str ++ Z_to_bv 8 0 :: slack) ->
stk asegs mz lo (bv_unsigned sp + -64) ->
rw_cells asegs mz (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp q0 q1 q2 sp w1 (Z_to_bv 64 len) y1 y2 y3 y4 y5 y6 y7
w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2136)) z5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 0x4fe9c) fc None mz (seg_rom asegs))).
{ intros xra q0 q1 q2 y1 y2 y3 y4 y5 y6 y7 w1 w2 w3 z5 q3 q4 q5 q6 mz MUz WMz MIz STRz STz FRz.
repeat match goal with H : ro_cells asegs ?mc _ _ |- _ => clear H | H : stk asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
try match goal with H : rw_cells asegs ?mc _ _ |- _ => lazymatch mc with mz => fail | _ => clear H end end.
do 11 step.
eapply K; [exact MUz | exact WMz | exact MIz | exact STRz | release_frame FRz STz (bv_unsigned sp); exact STz]. }
step.
destruct (Z.le_gt_cases 64 len) as [Hbig | Hsmall].
{
if_truex.
destruct Hlen as [Hlen | AM]; [lia|].
clear GOT CELL.
step.
step. if_truex.
step. step. step.
match goal with H : bytes_at _ _ s (str ++ _) |- _ => rename H into STRc; stash STRc end.
try match goal with H : bytes_at _ _ s (str ++ _) |- _ => clear H end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc |- _ =>
eapply region_is_poisoned_sound_U with (s := s) (n := len + 1) (lo := lo);
[ eapply unpoisoned_transport; [exact UP | exact MUc | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s (len + 1)); try eassumption; unfold A_SB; lia]
| eapply asan_rt_ok_transport; [exact RT | exact MUc | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]]
| exact AM | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| assumption
| rewrite unsigned_lit by lia; reflexivity | ]
end end.
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 MU3 WM3 MI3 ST1'' UP3 RT3.
assert (STR3 : bytes_at asegs m3 s (str ++ Z_to_bv 8 0 :: slack))
by (unstash STRc; eapply bytes_at_transport; [exact STRc | exact MU3 | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia]).
clear STRc.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x4ffb8)) with (Z_to_bv 64 0x4ffb8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_true.
step. step.
lazymatch goal with MUc : munch _ m m3 |- _ => lazymatch goal with WMc : wmono _ m m3 |- _ =>
eapply TAILG; [exact MUc | exact WMc | exact MI3 | exact STR3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR]
end end. }

if_falsex.
assert (Hh : s / 8 <= (s + len) / 8 <= s / 8 + 8) by (Z.div_mod_to_equations; lia).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UP1 : unpoisoned asegs mc A_SB s (len + 1))
by (eapply unpoisoned_transport; [exact UP | match goal with H : munch _ m mc |- _ => exact H end
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB s (len + 1)); try eassumption; unfold A_SB; lia])
end.
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + len) / 8 + A_SB) UP1 ltac:(unfold A_SB; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + len) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UP1); lia |];
assert (HRL : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + len) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + len) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UP1) as (v & Hro & Hv); replace (s + (len + 1) - 1) with (s + len) in Hro, Hv by lia;
exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UP UP1.
do 3 step.
step. replace (len + s) with (s + len) by lia.
do 2 step; do 2 step; do 2 step.
sh_norm.
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
replace (2147450880 + (s + len) / 8) with ((s + len) / 8 + 2147450880) by lia.
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia. rewrite (unsigned_lit ((s + len) / 8 + 2147450880)) by lia.
rewrite !land_m8_64 by lia.
do 2 step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall (p0 p1 p2 y1 y2 y3 y4 y5 y6 y7 z5 p3 p4 p5 p6 : word),
evt asegs Q (MS (mkR (Z_to_bv 64 0x4fe34) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp p0 p1 p2 sp (Z_to_bv 64 (len + 1)) (Z_to_bv 64 len) y1 y2 y3 y4 y5 y6 y7
(Z_to_bv 64 s) (Z_to_bv 64 0x183ce8) (Z_to_bv 64 (bv_unsigned sp + -2136)) z5 s6 s7 s8 s9 s10 s11 p3 p4 p5 p6)
F (Z_to_bv 64 0x4fe9c) fc None mc (seg_rom asegs)))
by (intros p0 p1 p2 y1 y2 y3 y4 y5 y6 y7 z5 p3 p4 p5 p6;
lazymatch goal with MUc : munch _ m mc |- _ => lazymatch goal with WMc : wmono _ m mc |- _ =>
eapply TAILG; [exact MUc | exact WMc | assumption | match goal with H : bytes_at _ mc s (str ++ _) |- _ => exact H end
| eapply stk_merge; [exact ST1' | exact ST2 | lia] | exact FR ] end end)
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP : forall (Kn : nat) (i : Z) (x0 x1 x2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
Z.to_nat ((s + len) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + len) / 8 ->
evt asegs Q (MS (mkR (Z_to_bv 64 0x4fe34) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp (Z_to_bv 64 (len + 1)) (Z_to_bv 64 0) (Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + len) / 8 + 2147450880)) y3 y4 y5 y6 y7
(Z_to_bv 64 s) (Z_to_bv 64 0x183ce8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 len) s6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
F (Z_to_bv 64 0x4ff94) fc None mc (seg_rom asegs)))
end.
{ clear Hh V1c V2c HRL.
induction Kn as [|Kn IH]; intros i p0 p1 p2 q3 q4 q5 q6 q7 r3 r4 r5 r6 HK Hi Hig; [lia|].
pose proof (GS0 i Hi Hig) as HR.
step. rewrite ?zxb_zero. clear HR.
step. step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0.
step.
destruct (Z.eq_dec (s / 8 + i + 1) ((s + len) / 8)) as [Heq|Hne].
- if_falsex. step. step. if_true. step. step. apply TAIL.
- if_truex. replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia. apply (IH (i + 1)); lia. }
step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply TAIL. }

destruct HRL as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c.
step.
step. rewrite (sxb_small v) by lia. clear HR.
step. rewrite (unsigned_lit (s + len)) by lia. rewrite land7_mod8 by lia.
step. step. step. step.
destruct Hv as [-> | (Hk & Hlast)].
- rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
step.
destruct (Z.eq_dec (s / 8) ((s + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. step. step. apply TAIL.
+ if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((s + len) / 8 - s / 8 - 0)) 0); lia.
- rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_slt_1 (Z_to_bv 64 ((s + len) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; clear Hh; Z.div_mod_to_equations; lia).
rewrite !(unsigned_lit 1) by lia. change (Z.lxor 1 1) with 0. rewrite Z.land_0_r.
step.
destruct (Z.eq_dec (s / 8) ((s + len) / 8)) as [Heq1|Hne1].
+ if_truex. step. step. if_true. step. step. apply TAIL.
+ if_falsex. replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia.
apply (LOOP (Z.to_nat ((s + len) / 8 - s / 8 - 0)) 0); lia.
Qed.
End MuslAStrlen.
End RC__1.
End Mqg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MuslAMemcpy.
Hypothesis OBL_REAL_MEMCPY : real_memcpy_specZ_stmt.

Lemma real_memcpy_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= S < 2^64 -> S + n <= 2^64 -> 0 <= n < 2^63 ->
bytes_at asegs m S src -> length src = Z.to_nat n ->
rw_cells asegs m D [CB (Z.to_nat n) junk] -> (S + n <= D \/ D + n <= S) -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn HS HSn Hn SRC SRCL DST DISJ MI.
pose proof (OBL_REAL_MEMCPY ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as X.
rewrite (unsigned_lit D), (unsigned_lit S), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. cbn beta in P. rewrite ?(unsigned_lit D), ?(unsigned_lit S), ?(unsigned_lit n) in P by lia. exact P.
Qed.

Lemma amemcpy_sound_U : amemcpy_spec_U.
Proof.
unfold amemcpy_spec_U.
intros until Q. intros UPd0 UPs0 RT Hd0 Hd47 Hs0 Hs47 Hdlo Hslo Ha0 Ha1 Ha2 Hn Hsz Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. unfold_consts. word_range sp SPR.
pose proof RT as RTC. unfold asan_rt_ok, a4_rt_cells, a4_rt_consts in RTC. cbn [app] in RTC.
apply Forall_cons_iff in RTC as [GOTF RTC]. apply Forall_cons_iff in RTC as [FLAG RTC]. apply Forall_cons_iff in RTC as [_ RTC].
apply Forall_cons_iff in RTC as [_ RTC]. apply Forall_cons_iff in RTC as [REALM RTC]. cbn [fst snd] in GOTF, FLAG, REALM.
do 59 (apply Forall_cons_iff in RTC as [_ RTC]).
apply Forall_cons_iff in RTC as [GOT RTC]. apply Forall_cons_iff in RTC as [CELL _]. cbn [fst snd] in GOT, CELL.
unfold A_GOT_SB, A_SB_CELL, A_SB in GOT, CELL. unfold A_SB_CELL in GOT.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in REALM. apply ro_C8_of_bytes_at in GOT. apply ro_C8_of_bytes_at in CELL.
assert (FLAGc : ro_cells asegs m 0xf2e99 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.

stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_MEMCPY_U. carve_frame 72%nat ST.
do 12 step.

unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.

assert (TAIL2G : forall (xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 w7 z3 z4 z5 z6 : word) (oldz : list byte) mz,
munch [(d, d + n); (lo, bv_unsigned sp)] m mz -> wmono asegs m mz -> mem_inv asegs mz ->
stk asegs mz lo (bv_unsigned sp + -72) ->
rw_cells asegs mz (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mz d [CB (Z.to_nat n) oldz] -> bytes_at asegs mz s src ->
ro_cells asegs mz 0xea1c8 [C8 (Z_to_bv 64 0xdda10)] ->
evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x0 x1 x2 sp w1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 w2 w3 (Z_to_bv 64 (bv_unsigned sp + -2144)) w5 w6 w7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 0x61c0c) fc None mz (seg_rom asegs))).
{ intros xra x0 x1 x2 x3 x4 x5 x6 x7 w1 w2 w3 w5 w6 w7 z3 z4 z5 z6 oldz mz MUz WMz MIz STz FRz DSTz SRCz REALMz.
clear GOTF REALM GOT CELL FLAGc MU WM MU0 ST FR DST SRC1 MI.
step. step. step.
(call real_memcpy_specZ); [ lia | lia | lia | lia | lia | exact SRCz | exact SRCL | exact DSTz | lia | assumption | ].
do 12 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ src] |- _ => exact H end
| match goal with H : bytes_at _ ?mf s src |- _ => exact H end
| release_frame FRz STz (bv_unsigned sp); exact STz ]. }
destruct (Z.eq_dec n 0) as [Hn0 | Hnz].
{
clear UPd0 UPs0.
do 4 step. if_false.
step. step.
step. step.
subst n. rewrite !Z.add_0_r in *.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD0 : evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 0)
(zxb (Z_to_bv 8 1)) a4 a5 a6 a7 s2 (Z_to_bv 64 d) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 s) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61b78) fc None mc (seg_rom asegs)))
end.
{ step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step. change (0 + -65) with (-65). if_true.
step. if_false. step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_true.
step. if_false. step.
eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1 | exact REALM]. }
step.
destruct (Z.eq_dec d s) as [Heq | Hne].
- if_truex. exact AD0.
- if_falsex. step.
destruct (Z.lt_ge_cases s d) as [Hlt | Hge].
+ if_falsex. step. if_falsex. exact AD0.
+ if_truex. exact AD0. }
destruct (Z.lt_ge_cases 64 n) as [Hbig | Hsmall].
{
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia]);
assert (RT1 : asan_rt_ok mc)
by (eapply asan_rt_ok_transport; [exact RT | exact MU0 | intros cc Hcc2; pose proof (a4_rt_cells_in_img cc Hcc2); cbn; split; [left; lia | exact I]])
end.
destruct Hsz as [Hsz | [AMd AMs]]; [lia|].
do 4 step. if_false.
step. step.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ADB : evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(zxb (Z_to_bv 8 1)) a4 a5 a6 a7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61b78) fc None mc (seg_rom asegs)))
end.
{ step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step. if_truex.
step. if_truex.
do 5 step.
step.
stash SRC1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2144) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
eapply region_is_poisoned_sound_U with (s := s) (n := n) (lo := lo);
[ exact UPs1 | exact RT1 | exact AMs | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (SRC2 : bytes_at asegs m2 s src)
by (unstash SRC1; eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC1.
assert (UPd2 : unpoisoned asegs m2 A_SB d n).
{ eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia].
eapply munch_trans; [exact MU0 | eapply munch_weaken; [| exact MU2]]. unfold sub_fp; cbn [outside]; intros; lia. }
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU2 WM2 end.
replace (ret_pc (Z_to_bv 64 0x61ec0)) with (Z_to_bv 64 0x61ec0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. if_truex.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply region_is_poisoned_sound_U with (s := d) (n := n) (lo := lo);
[ exact UPd2 | exact RT2 | exact AMd | lia
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1'
| exact LO
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| exact MI2
| rewrite unsigned_lit by lia; reflexivity | ].
rewrite ?unsigned_lit by lia.
intros u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
assert (SRC3 : bytes_at asegs m3 s src)
by (unstash SRC2; eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear SRC2.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU3 WM3 end.
replace (ret_pc (Z_to_bv 64 0x61f60)) with (Z_to_bv 64 0x61f60) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL2G; [exact MU | exact WM | exact MI3 | eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR | exact DST | exact SRC3 | exact REALM]. }
clear UPs1 RT1.
step. if_falsex.
step.
destruct Hdisj as [Hsd|Hds].
- if_falsex. step. if_falsex. exact ADB.
- if_truex. exact ADB. }

assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (UPd1 : unpoisoned asegs mc A_SB d n)
by (eapply unpoisoned_transport; [exact (UPd0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : unpoisoned asegs mc A_SB s n)
by (eapply unpoisoned_transport; [exact (UPs0 ltac:(lia)) | exact MU0 | intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0.
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |]
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.
do 4 step. if_false.
step. step.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL2 : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61c0c) fc None mc (seg_rom asegs)))
by (intros x3 x4 x5 x6 x7; eapply TAIL2G; [exact MU | exact WM | exact MI | exact ST | exact FR | exact DST | exact SRC1 | exact REALM])
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7 s2 (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61f34) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOT CELL Hh HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply TAIL2
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61bc4) fc None mc (seg_rom asegs)))
end.
{ intros x3 x4 x5 x6 x7;
clear V1c V2c GS0 GOTF FLAGc Hh REALM HRLs;
step; step; rewrite (unsigned_lit d) by lia; rewrite (lxor_ones64 d) by lia; if_falsex;
step; step; rewrite (size_test_n n) by lia; cbv iota;
do 3 step;
step; replace (d + n + -1) with (d + n - 1) by lia;
do 2 step; do 2 step; do 2 step;
sh_norm;
replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia;
replace (2147450880 + (d + n - 1) / 8) with ((d + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (d / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((d + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLd as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (d + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((d + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply TAIL2
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ])
|  apply TAIL2 ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61e90) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOT CELL Hg REALM TAIL2 LOOP2 HRLd HRLs;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD : forall x3 : word, evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) x3 a4 a5 a6 a7 s2 (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (s + n)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x61b78) fc None mc (seg_rom asegs)))
end.
{ intros x3;
clear W1c W2c GR0 GOTF FLAGc Hg REALM TAIL2 LOOP2 HRLd;
step; step; rewrite (unsigned_lit s) by lia; rewrite (lxor_ones64 s) by lia; if_falsex;
step; step; step; rewrite (size_test_n n) by lia; cbv iota;
do 3 step;
step; replace (s + n + -1) with (s + n - 1) by lia;
do 2 step; do 2 step; do 2 step;
sh_norm;
replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia;
replace (2147450880 + (s + n - 1) / 8) with ((s + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (s / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((s + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia;
do 2 step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end;
[
destruct HRLs as (v & HR & Hv);
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia);
step; rewrite (sxb_small v) by lia; clear HR;
step; rewrite (unsigned_lit (s + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (Hk & Hlast)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((s + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; try clear Hg; try clear Hh; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ];
(step;
destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply MID
| if_falsex; replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia;
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia ])
|  apply MID ]. }

clear W1c W2c V1c V2c GR0 GS0 GOTF FLAGc GOT CELL Hg Hh REALM TAIL2 LOOP2 MID LOOP1 HRLd HRLs.
step. if_falsex.
step.
destruct Hdisj as [Hsd|Hds].
- if_falsex. step. if_falsex. apply AD.
- if_truex. apply AD.
Qed.
End MuslAMemcpy.
End RC__1.
