(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "length"; "nat"; "list"; "app"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Nat"; "add"; "mul"; "sub"; "@Corelib.Init.Peano"; "le"; "lt"; "@Stdlib.ZArith.BinInt.Z"; "le"; "to_nat"; "mul"; "pow"; "lt"; "add"; "modulo"; "of_nat"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sublist"; "sv"; "valuation"; "enc_bytes"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "lget"; "lput"; "IX4"; "LD4"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "Z_to_le_bytes"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition lput (L : list byte) (off : nat) (bs : list byte) : list byte := ltac2:(tb__ "0|1|
S3SaQ8A1M0S1bG0Voff;VL;A3S3G0Vbs;S1cG0SdVoff;S0G0Vbs;A2A2VL;A3A3A3").

Lemma lput_length : ltac2:(tb__ "0|2|
S2SaQ8A1M0A1M1S1G1S10SdR2S0G0R1A2A2S0G0R3A2A2S4S1S0G0S24R4R3R2A3A2S0G0R4A2A3F_;Fbs;Foff;FL;").
Proof. intros L off bs H. unfold lput. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma lput_nth_in : ltac2:(tb__ "0|2|
S2SaQ8A1M0A1M1S1G1S1G0S10SdR4S0G0R3A2A2S0G0R5A2A2S5S10R5R3A2S11R3SdR5S0G0R4A2A2A2A2S4G0S1aG0R4S24R7R6R5A3R3A4S1aG0SfR4R6A2R5R3A4A3F_;F_;Fd;Fj;Fbs;Foff;FL;").
Proof.
  intros L off bs j d HL Hj. unfold lput.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Init.Nat.min off (length L)) with off by lia.
  rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma lput_nth_out : ltac2:(tb__ "0|2|
S2SaQ8A1M0A1M1S1G1S1G0S10SdR4S0G0R3A2A2S0G0R5A2A2S7S11R3R5A2S10SdR5S0G0R4A2A2R3A2A2S4G0S1aG0R4S24R7R6R5A3R3A4S1aG0R4R7R3A4A3F_;F_;Fd;Fj;Fbs;Foff;FL;").
Proof.
  intros L off bs j d HL Hj. unfold lput. destruct Hj as [Hj|Hj].
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn. destruct (Nat.ltb_spec j off); [reflexivity|lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Init.Nat.min off (length L)) with off by lia.
    rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Definition lget (L : list byte) (i : Z) : Z := ltac2:(tb__ "0|1|
S27S1eS14Z4M0Vi;A2G0VL;A3A1").

Lemma length_sublist_le4 : ltac2:(tb__ "0|2|
S8S2SaQ8A1M0A1S10S0G0S1eS14Z4M1R2A2G1R1A3A2U4A2FL;Fi;").
Proof. intros. unfold sublist. rewrite length_firstn. lia. Qed.

Lemma lget_range : ltac2:(tb__ "0|1|
S2SaQ8A1A1S8S5S12Z0S23R2R1A2M0A2S16G0S15Z2Z20A2A2A2Fi;FL;").
Proof.
  intros L i. unfold lget. pose proof (bytes_le_to_Z_bound (sublist (4 * i) 4 L)) as B.
  pose proof (bytes_le_to_Z_nonneg (sublist (4 * i) 4 L)) as B0.
  pose proof (length_sublist_le4 i L) as Hl.
  assert (2 ^ (8 * Z.of_nat (length (sublist (4 * i) 4 L))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma sublist_ext : ltac2:(tb__ "0|7|
S8S8S2SaQ8M0A1M1A1M2G2S12Z0M3R4A2M4G4S4S1S0G1R4A2S0G1R3A2A3S1S5S10S13R8A1M5R1A2S11R1SdG5S13R7A1A2A2A2S4G1S1aG1R2R7ScG0G3A2M6A4S1aG1R2R6G6A4A3F_;Fj;S4G2S1eR8R7R6A3S1eR8R7R5A3A3F_;F_;F_;F_;FL';FL;Fk;Fi;").
Proof.
  intros i k L L' Hi Hk Hlen H. unfold sublist.
  apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_firstn, !length_skipn. lia.
  - intros n Hn. rewrite length_firstn, length_skipn in Hn.
    rewrite !nth_firstn. destruct (Nat.ltb_spec n (Z.to_nat k)); [|lia]. rewrite !nth_skipn. apply H. lia.
Qed.

Lemma lget_lput_other : ltac2:(tb__ "0|4|
S2SaQ8A1M0A1M1S8G1S8S4S1S0G0R2A2U4M2A3S12Z0M3R4A2S12G3R3A2S6S4S8R6R4A3A1S10SdSeG2S13R7A1A2G2A2S0G0R8A2A2S4S8S23S24R9SeG2S13R8A1A2R7A3R6A2S23R9R6A2A3F_;F_;F_;F_;F_;Fj;Fbs;Fi;FL;").
Proof.
  intros L i bs j Hbs Hi Hj Hij HL. unfold lget. f_equal. apply sublist_ext; try lia.
  - apply lput_length. lia.
  - intros q Hq. apply lput_nth_out; [lia|]. rewrite Hbs. nia.
Qed.

Lemma lget_lput_same : ltac2:(tb__ "0|3|
S2SaQ8A1M0A1M1S8G1S4S1S0G0R1A2U4M2A3S12Z0R3A2S10SdSeG2S13R4A1A2G2A2S0G0R5A2A2S4S8S23S24R6SeG2S13R5A1A2R4A3R5A2S27R4A1A3F_;F_;F_;Fbs;Fi;FL;").
Proof.
  intros L i bs Hbs Hi HL. unfold lget. f_equal.
  apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite sublist_length; [lia|lia|lia|]. rewrite lput_length; [|lia]. lia.
  - intros n Hn. rewrite sublist_length in Hn by (try lia; rewrite lput_length; lia).
    rewrite sublist_nth by lia. rewrite lput_nth_in by lia. f_equal. lia.
Qed.

Lemma bytes_le_to_Z_enc4 : ltac2:(tb__ "0|1|
SaQ40M0A1S4S8S27S21U4R1A2A1S18SbG0R1A2S15Z2Z20A2A2A3Fv;").
Proof.
  intros v. unfold enc_bytes. rewrite bytes_le_to_Z_Z_to_le_bytes by (pose proof (urange v); lia). reflexivity.
Qed.

Lemma sublist_lget : ltac2:(tb__ "0|3|
S2SaQ8A1M0A1M1S8S12Z0R1A2S12S17S14Z4M2R2A2G2A2S19S0G0R3A2A1A2S4G1S1eS14G2R3A2G2R4A3S28U4S23R4R3A2A2A3F_;F_;Fi;FL;").
Proof.
  intros L i Hi HL. unfold lget.
  replace 4%nat with (length (sublist (4 * i) 4 L)) by (rewrite sublist_length; lia).
  symmetry. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.

Definition IX4 (e : sv) : sv := SAlu ALU_SLL e (SLit 2).
Definition LD4 (l : positive) (e : sv) : sv := SLBytes l (IX4 e) 4.

Lemma U_IX4 : ltac2:(tb__ "0|1|
S20S1fS16SbQ40M0S1dR2R1A2A2S15Z2Z3eA2A2S4S8SbG0S1dR3S25R2A1A2A2S14Z4SbG0S1dR3R2A2A2A2A3F_;Fe;Frho;").
Proof.
  intros rho e He. unfold IX4. rewrite U_sll_lit. change (2 ^ (2 mod 64)) with 4. unfold M64v.
  pose proof (urange (eval rho e)). rewrite Z.mod_small; lia.
Qed.

Lemma U_LD4 : ltac2:(tb__ "0|1|
S20S9S1fS16SbQ40M0S1dR3R1A2A2S15Z2Z3eA2A2S4S8SbG0S1dR4S26R3R2A2A2A2S23S22R4R3A2SbG0S1dR4R2A2A2A2A3F_;Fe;Fl;Frho;").
Proof.
  intros rho l e He. unfold LD4. cbn [eval]. change (SAlu ALU_SLL e (SLit 2)) with (IX4 e). rewrite (U_IX4 rho e He).
  unfold le_bytes_to_word, lget. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound (sublist (4 * bv_unsigned (eval rho e)) 4 (rl rho l))) as B.
  pose proof (bytes_le_to_Z_nonneg (sublist (4 * bv_unsigned (eval rho e)) 4 (rl rho l))) as B0.
  pose proof (length_sublist_le4 (bv_unsigned (eval rho e)) (rl rho l)) as Hl.
  assert (2 ^ (8 * Z.of_nat (length (sublist (4 * bv_unsigned (eval rho e)) 4 (rl rho l)))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  apply bv_wrap_small. change (bv_modulus 64%N) with (2 ^ 64). lia.
Qed.
