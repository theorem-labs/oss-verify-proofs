(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0h YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF47 YF4b YF4c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Definition CLZ_TERM {imgk : img} : sv := ltac:(img_eval_last (fun imgk : img => ((sr_get (ss_regs S_X) (19%bv : bv 5))))).
Definition CLZ_TERM' : sv :=
let v0 := SOff 42 0 in let v1 := SLit 1 in let v2 := SAlu ALU_SRL v0 v1 in let v3 := SAlu ALU_OR v0 v2 in let v4 := SLit 2 in
let v5 := SAlu ALU_SRL v3 v4 in let v6 := SAlu ALU_OR v3 v5 in let v7 := SLit 4 in let v8 := SAlu ALU_SRL v6 v7 in let v9 := SAlu ALU_OR v6 v8 in
let v10 := SLit 8 in let v11 := SAlu ALU_SRL v9 v10 in let v12 := SAlu ALU_OR v9 v11 in let v13 := SLit 16 in let v14 := SAlu ALU_SRL v12 v13 in
let v15 := SAlu ALU_OR v12 v14 in let v16 := SLit 32 in let v17 := SAlu ALU_SRL v15 v16 in let v18 := SAlu ALU_OR v15 v17 in
let v20 := SLit (-1) in let v21 := SAlu ALU_XOR v18 v20 in let v22 := SAlu ALU_SRL v21 v1 in let v23 := SLit 6148914691236517205 in
let v24 := SAlu ALU_AND v22 v23 in let v25 := SAlu ALU_SUB v21 v24 in let v26 := SLit 3689348814741910323 in let v27 := SAlu ALU_AND v25 v26 in
let v28 := SAlu ALU_SRL v25 v4 in let v29 := SAlu ALU_AND v28 v26 in let v30 := SAlu ALU_ADD v27 v29 in let v31 := SAlu ALU_SRL v30 v7 in
let v32 := SAlu ALU_ADD v30 v31 in let v33 := SLit 1085102592571150095 in let v34 := SAlu ALU_AND v32 v33 in let v35 := SLit 72340172838076673 in
let v36 := SMd M_MUL v34 v35 in let v37 := SLit 56 in SAlu ALU_SRL v36 v37.
Lemma CLZ_TERM'_eq {imgk : img} : CLZ_TERM' = CLZ_TERM.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.

Definition zA (op : aluop) (a b : Z) : Z := zcanon (zalu_raw 63 64 op a b).
Definition clzS (x : Z) : Z :=
let v0 := zcanon (x + 0) in let v1 := zcanon 1 in let v2 := zA ALU_SRL v0 v1 in let v3 := zA ALU_OR v0 v2 in let v4 := zcanon 2 in
let v5 := zA ALU_SRL v3 v4 in let v6 := zA ALU_OR v3 v5 in let v7 := zcanon 4 in let v8 := zA ALU_SRL v6 v7 in let v9 := zA ALU_OR v6 v8 in
let v10 := zcanon 8 in let v11 := zA ALU_SRL v9 v10 in let v12 := zA ALU_OR v9 v11 in let v13 := zcanon 16 in let v14 := zA ALU_SRL v12 v13 in
let v15 := zA ALU_OR v12 v14 in let v16 := zcanon 32 in let v17 := zA ALU_SRL v15 v16 in let v18 := zA ALU_OR v15 v17 in
let v20 := zcanon (-1) in let v21 := zA ALU_XOR v18 v20 in let v22 := zA ALU_SRL v21 v1 in let v23 := zcanon 6148914691236517205 in
let v24 := zA ALU_AND v22 v23 in let v25 := zA ALU_SUB v21 v24 in let v26 := zcanon 3689348814741910323 in let v27 := zA ALU_AND v25 v26 in
let v28 := zA ALU_SRL v25 v4 in let v29 := zA ALU_AND v28 v26 in let v30 := zA ALU_ADD v27 v29 in let v31 := zA ALU_SRL v30 v7 in
let v32 := zA ALU_ADD v30 v31 in let v33 := zcanon 1085102592571150095 in let v34 := zA ALU_AND v32 v33 in let v35 := zcanon 72340172838076673 in
let v36 := zcanon (zmd_raw 64 M_MUL v34 v35) in let v37 := zcanon 56 in zA ALU_SRL v36 v37.
Lemma zev_CLZ_TERM {imgk : img} : forall rho, zev rho CLZ_TERM = clzS (rho 42%nat).
Proof. intros rho. rewrite <- CLZ_TERM'_eq. unfold CLZ_TERM'. cbv zeta. cbn [zev]. unfold clzS, zA. cbv zeta. img_refl. Qed.
Fixpoint sweep (f : Z -> bool) (k : nat) (z : Z) : bool := match k with O => true | S k' => f z && sweep f k' (z + 1) end.
Lemma sweep_val : forall f k z, sweep f k z = true -> forall q, z <= q < z + Z.of_nat k -> f q = true.
Proof.
intros f k. induction k as [|k IH]; intros z Hs q Hq; [img_try (cbn in Hq; img_lia)|].
cbn [sweep] in Hs. apply andb_prop in Hs as [Hf Hs].
destruct (Z.eq_dec q z) as [->|Hne]; [img_try (img_exact Hf)|]. img_apply (IH (z + 1) Hs). rewrite Nat2Z.inj_succ in Hq. img_lia.
Qed.
Notation clz_okb := (fun p : Z => Z.eqb (Z.lxor (clzS (4096 * p)) 63) (Z.log2 p + 12)).
