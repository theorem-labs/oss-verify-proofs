(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "modulo"; "pow"; "le"; "lt"; "lor"; "shiftl"; "shiftr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SExt"; "SAlu"; "SLit"; "SVar"; "eval"; "rw"; "@Corelib.Init.Datatypes"; "false"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AmSecx"; "SECX"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ZEval WalkArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma urange64 (w : word) : ltac2:(tb__ "0|1|
SfS2Z0S18Q40Vw;A2M0A2S3G0S1Z2Z40A2A2A2").
Proof. pose proof (bv_unsigned_in_range _ w) as H. change (bv_modulus 64%N) with (2 ^ 64) in H. lia. Qed.

Definition SECX : sv := ltac2:(tb__ "0|3|
S8S13S7SdQ20M0S7SeG0SaPacA1M1A3A3S8S14S7SdG0S7SeG0S8S15G1S9Z20A1M2A3A3A3G2A3A3").
Lemma halves_id (x : Z) : ltac2:(tb__ "0|4|
SfS2Z0Vx;A2S3Vx;S1Z2M0Z40A2M1A2A2S10S12S4S0S0S11Z20M2Vx;A2G1A2S1G0G2A2M3A2S0S5S0S0S11G2S6Vx;G2A2A2G1A2G3A2G2A2G1A2A2Vx;A3F_;").
Proof.
  intros Hx.
  assert (LO : ((toS 32 x) mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32).
  { unfold toS. destruct (x mod 2 ^ 32 <? 2 ^ (32 - 1)) eqn:E.
    - rewrite (Z.mod_small (x mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound x (2 ^ 32)); lia). apply Z.mod_mod. lia.
    - replace ((x mod 2 ^ 32 - 2 ^ 32) mod 2 ^ 64) with (x mod 2 ^ 32 - 2 ^ 32 + 2 ^ 64) by (pose proof (Z.mod_pos_bound x (2 ^ 32)); Z.to_euclidean_division_equations; nia).
      replace (x mod 2 ^ 32 - 2 ^ 32 + 2 ^ 64) with (x mod 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 32) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_mod. lia. }
  assert (HIW : ((toS 32 (Z.shiftr x 32)) mod 2 ^ 64) mod 2 ^ 32 = x / 2 ^ 32).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (RQ : 0 <= x / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold toS. rewrite (Z.mod_small (x / 2 ^ 32) (2 ^ 32)) by lia.
    destruct (x / 2 ^ 32 <? 2 ^ (32 - 1)) eqn:E.
    - rewrite (Z.mod_small _ (2 ^ 64)) by lia. apply Z.mod_small. lia.
    - replace ((x / 2 ^ 32 - 2 ^ 32) mod 2 ^ 64) with (x / 2 ^ 32 - 2 ^ 32 + 2 ^ 64) by (Z.to_euclidean_division_equations; nia).
      replace (x / 2 ^ 32 - 2 ^ 32 + 2 ^ 64) with (x / 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 32) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite LO, HIW. rewrite Z.shiftl_mul_pow2 by lia.
  assert (RQ : 0 <= x / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (x / 2 ^ 32 * 2 ^ 32) (2 ^ 64)) by nia.
  assert (DJ : Z.land (x mod 2 ^ 32) (x / 2 ^ 32 * 2 ^ 32) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n 32).
    - rewrite (Z.mul_pow2_bits_low (x / 2 ^ 32) 32 n) by lia. apply Bool.andb_false_r.
    - rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact DJ. rewrite <- Z.add_nocarry_lxor by exact DJ.
  pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma secx_eval (rhoX : valuation) : ltac2:(tb__ "0|0|
S10S17Q40A1SbVrhoX;S16A2ScVrhoX;PacA2A3").
Proof.
  apply bv_eq. rewrite (eval_zeval rhoX SECX eq_refl). cbn -[Z.pow Z.modulo Z.shiftl Z.shiftr Z.lor toS Z.mul Z.sub Z.add Z.ltb].
  unfold zr_of. pose proof (urange64 (rw rhoX 172%positive)) as RX. set (x := bv_unsigned (rw rhoX 172%positive)) in *.
  rewrite (Z.mod_small x) by lia. change (32 mod 2 ^ 64) with 32. change (32 mod 64) with 32.
  rewrite (Z.mod_small x) by lia.
  rewrite (Z.mod_small ((toS 32 x mod 2 ^ 64) mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (toS 32 x mod 2 ^ 64) (2 ^ 32)); lia).
  rewrite (Z.mod_mod _ (2 ^ 64)) by lia.
  exact (halves_id x RX).
Qed.

