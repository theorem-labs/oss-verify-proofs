(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI09 YI08 YI00 YI6c YI03.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable segs : list Segment.
Inductive chunk_bytes (E : env) (cs : list YP09.chunk) : Z -> list sv -> list Z -> Prop :=
| cb_nil : forall off, chunk_bytes E cs off [] []
| cb_cons : forall off e es b bs, In (mkChunk off (CVal 1 e)) cs -> bv_unsigned (sv_denot E e) mod 256 = b ->
chunk_bytes E cs (off + 1) es bs -> chunk_bytes E cs off (e :: es) (b :: bs).
Lemma garr8_of_chunk_bytes : forall E mem r p a es bs off,
region_ok segs E mem r -> r_base r = Some p -> bv_unsigned (ew E p) = a ->
chunk_bytes E (r_chunks r) off es bs -> garr8 segs mem (a + off) bs.
Proof.
intros E mem r p a es bs off HR Hb Hp HC. induction HC as [off | off e es b bs Hin Hbv HC IH].
- apply garr8_nil.
- intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split.
* exact (vval_mem_of_chunk_mod segs E mem r p a off 1%N e b HR Hb Hin Hp Hbv ltac:(cbn; lia)).
* rewrite <- Hbv. apply Z.mod_pos_bound. lia.
+ cbn [nth]. cbn [length] in Hj. specialize (IH j ltac:(lia)).
replace (a + off + Z.of_nat (Datatypes.S j)) with (a + (off + 1) + Z.of_nat j) by lia. exact IH.
Qed.
Lemma byte_sext16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 -> bv_unsigned (sv_denot E (SExt true 16 (SOff n 0))) mod 256 = v mod 256.
Proof.
intros E n v Hn Hv. change (U E (SExt true 16 (SOff n 0)) mod 256 = v mod 256).
rewrite U_SExt. rewrite mod256_zcanon, mod256_swrap by (cbn; lia). change (2 ^ Z.of_N 16) with (2 ^ 16). rewrite mod256_mod_pow2 by lia.
rewrite (U_atom E n v Hn) by lia. reflexivity.
Qed.
Lemma byte_sext16_hi : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SExt true 16 (SOff n 0)) (SLit 8))) mod 256 = (v / 256) mod 256.
Proof.
intros E n v Hn Hv. change (U E (SAlu ALU_SRL (SExt true 16 (SOff n 0)) (SLit 8)) mod 256 = (v / 256) mod 256).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 8) 63) with 8. rewrite mod256_zcanon, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 16) with 65536. rewrite (Z.mod_small v 65536) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with 65536. change (65536 / 2) with 32768.
destruct (Z.lt_ge_cases v 32768) as [Hlo | Hhi].
- rewrite (Z.mod_small (v + 32768) 65536) by lia. replace (v + 32768 - 32768) with v by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
- replace ((v + 32768) mod 65536) with (v - 32768) by (apply Z.mod_unique_pos with (q := 1); lia).
replace (v - 32768 - 32768) with (v - 65536) by lia.
assert (Ez : zcanon (v - 65536) = 2 ^ 64 + (v - 65536)) by (unfold zcanon, M64; symmetry; apply Z.mod_unique_pos with (q := -1); lia).
rewrite Ez. replace (2 ^ 64 + (v - 65536)) with (v + (2 ^ 56 - 256) * 256) by lia. rewrite Z.div_add by lia.
replace (v / 256 + (2 ^ 56 - 256)) with (v / 256 + (2 ^ 48 - 1) * 256) by lia. apply Z.mod_add. lia.
Qed.
Lemma chunk_bytes_length : forall E cs off es bs, chunk_bytes E cs off es bs -> length bs = length es.
Proof. intros E cs off es bs HC. induction HC; cbn; [reflexivity | f_equal; assumption]. Qed.
End d.
End c.
Ltac chunk_bytes_step byte_tac :=
lazymatch goal with
| |- chunk_bytes _ ?cs ?off _ _ =>
let o := eval vm_compute in off in
lazymatch cs with
| context [mkChunk o (CVal 1 ?e)] =>
eapply (cb_cons _ cs off e); [cbn [In]; tauto | byte_tac | ]
end
end.
Ltac chunk_bytes_tac n byte_tac :=
lazymatch n with
| O => apply cb_nil
| Datatypes.S ?m => chunk_bytes_step byte_tac; chunk_bytes_tac m byte_tac
end.
