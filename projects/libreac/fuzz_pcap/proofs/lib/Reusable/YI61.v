(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI61.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP01 YP03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI08 YI0t YI0m YI0s YI6a.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable E : env.
Lemma U_zx2 : forall a x, U E a = x -> 0 <= x < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 31)) = 2 * x.
Proof.
intros a x Ha Hx. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 31) 63) with 31.
rewrite Ha, Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (rewrite M64_val; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
rewrite Z.shiftr_div_pow2 by lia.
replace (x * 2 ^ 32) with ((2 * x) * 2 ^ 31) by (change (2 ^ 32) with (2 * 2 ^ 31); lia).
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma alias_base_zx2 : forall nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v < 2 ^ 32 -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL e (SLit 32)) (SLit 31))) = sv_denot E (SOff nk 0).
Proof.
intros nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small E (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL e (SLit 32)) (SLit 31)) base (2 * v)); try lia.
- rewrite (U_atom E nk _ Hk) by lia. reflexivity.
- apply (U_atom E nb base Hb). lia.
- apply U_zx2; [exact He | lia].
Qed.
End c.
End b.
