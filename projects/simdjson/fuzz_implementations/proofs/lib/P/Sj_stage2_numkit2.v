(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_stage2_numkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma pow5_idx : forall e, -342 <= e <= 308 ->
  8 * (bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616) mod 18446744073709551616
  = (16 * e) mod 18446744073709551616.
Proof.
  intros e HE. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  lia.
Qed.

Lemma pow5_read : forall (m : word -> option byte) e d, -342 <= e <= 308 -> (d = 1376 \/ d = 1384) ->
  exists w, ov_read_bytes psegs m
              (Z_to_bv 64 (8 * (bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616) + 91928 + d)) 8 = Some (le8 w).
Proof.
  intros m e d HE Hd.
  apply (pow_tab_read m (16 * e + 4280 + d)); [lia | lia |].
  unfold wa, T_POW. apply wz_eq_mod.
  pose proof (pow5_idx e HE) as HI.
  set (X := bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1) mod 18446744073709551616) in *.
  lia.
Qed.

Local Close Scope Z_scope.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Ltac nreg_val R n :=
  let p := eval vm_compute in (Z.to_pos (n + 1)) in
  let v := eval lazy beta iota delta [tget] in (tget p R) in
  lazymatch v with Some ?x => x end.
Ltac nforget n :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := nreg_val R n in
    tryif is_var x then idtac else
    (let y8 := nreg_val R 8%Z in let y18 := nreg_val R 18%Z in let y19 := nreg_val R 19%Z in let y20 := nreg_val R 20%Z in
     tryif first [constr_eq x y8 | constr_eq x y18 | constr_eq x y19 | constr_eq x y20] then idtac
     else (let j := fresh "jk" in generalize x; intro j))
  end.
Ltac nforget_F :=
  lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) =>
    tryif is_var F then idtac else (let j := fresh "jF" in generalize F; intro j) end.

Ltac nforget_all keep :=
  let go n := (tryif keep n then nforget n else idtac) in
  go 1%Z; go 5%Z; go 6%Z; go 7%Z; go 9%Z; go 10%Z; go 11%Z; go 12%Z; go 13%Z; go 14%Z; go 15%Z; go 16%Z; go 17%Z;
  go 21%Z; go 22%Z; go 23%Z; go 24%Z; go 25%Z; go 26%Z; go 27%Z; go 28%Z; go 29%Z; go 30%Z; go 31%Z;
  nforget_F.
Ltac srun_cut_f cuts keep :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => cuts pc end; nstep; nforget_all keep).
Ltac nexp_f cuts fin keep := srun_cut_f cuts keep; first [ fin | (nbranch; nexp_f cuts fin keep) ].

From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_tables.
Lemma sown_read_at : forall (m : word -> option byte) c a, mem_inv psegs m -> (0 <= c < 256)%Z -> a = wa (T_SOWN + c) ->
  ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (sown c)].
Proof. intros m c a MI Hc ->. apply sown_read; assumption. Qed.
Ltac s2_load_sown :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | MIh : mem_inv segs m |- _ =>
          let Ea := addr_expr a in
          let idx := lazymatch Ea with
                     | Z.add 83848%Z ?i => i
                     | Z.add ?i 83848%Z => i
                     end in
          rewrite (sown_read_at m idx a MIh ltac:(lia) ltac:(unfold wa, T_SOWN; f_equal; lia))
      end
  end;
  load_post.
