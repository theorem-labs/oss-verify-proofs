(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP Image.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require G3Pure_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition PT_BASE : Z := 0x14f40.   Definition PE_BASE : Z := 0x164b8.

Lemma PT_ro : ro_bytes_b rsegs PT_BASE G3Pure_u.PT_BYTES = true.
Proof. vmc_refl. Qed.
Lemma PE_ro : ro_bytes_b rsegs PE_BASE G3Pure_u.PE_BYTES = true.
Proof. vmc_refl. Qed.

Lemma pt_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PT_BASE + 8 * i)) 8 = Some (firstn 8 (skipn (Z.to_nat (8 * i)) G3Pure_u.PT_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PT_BASE G3Pure_u.PT_BYTES MI PT_ro ltac:(unfold PT_BASE; lia) ltac:(rewrite G3Pure_u.PT_len; unfold PT_BASE, G3Pure_u.NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite G3Pure_u.PT_len; unfold G3Pure_u.NPOW; lia].
Qed.
Lemma pe_read : forall m i, mem_inv rsegs m -> 0 <= i < 687 ->
  ov_read_bytes rsegs m (wa (PE_BASE + 4 * i)) 4 = Some (firstn 4 (skipn (Z.to_nat (4 * i)) G3Pure_u.PE_BYTES)).
Proof.
  intros m i MI Hi. pose proof (ro_cells_image rsegs m PE_BASE G3Pure_u.PE_BYTES MI PE_ro ltac:(unfold PE_BASE; lia) ltac:(rewrite G3Pure_u.PE_len; unfold PE_BASE, G3Pure_u.NPOW; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  apply bytes_at_read; [exact RO | lia | rewrite G3Pure_u.PE_len; unfold G3Pure_u.NPOW; lia].
Qed.

Definition TOINT : word := Z_to_bv 64 0x4330000000000000.
Definition ceil_e (x : word) : Z := Z.shiftr (Z.shiftl (bv_unsigned x) 1 mod 18446744073709551616) 53.
Definition ceil_y (x : word) : word :=
  if Z.leb (2 ^ 63) (bv_unsigned x) then fsub_d RNE (fadd_d RNE (fsub_d RNE x TOINT) TOINT) x
  else fsub_d RNE (fsub_d RNE (fadd_d RNE x TOINT) TOINT) x.
Definition ceil_m (x : word) : word :=
  if Z.ltb 1074 (ceil_e x) then x
  else if feq_d x (fcvt_d_w RNE (Z_to_bv 64 0)) then x
  else if Z.ltb 1022 (ceil_e x) then
         (if flt_d (ceil_y x) (fcvt_d_w RNE (Z_to_bv 64 0)) then fadd_d RNE (fadd_d RNE x (ceil_y x)) (fcvt_d_w RNE (Z_to_bv 64 1))
          else fadd_d RNE x (ceil_y x))
  else if Z.leb (2 ^ 63) (bv_unsigned x) then sgnj_val F_SGNJN (Z_to_bv 64 0) (Z_to_bv 64 0)
  else fcvt_d_w RNE (Z_to_bv 64 1).

Definition KCX (x : Z) : word := fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 x)) (Z_to_bv 64 G3Pure_u.KC_CONST).
Definition FLO : word := Z_to_bv 64 0xc1e0000000200000.
Definition FHI : word := Z_to_bv 64 0x41e0000000000000.
Definition KCWB (x : Z) : word := fcvt_w_d RTZ (ceil_m (KCX x)).
Definition kcb_okw (ple : Z) : bool :=
  let c := ceil_m (KCX (-50 - ple)) in
  (flt_d FLO c && flt_d c FHI && Z.eqb (bv_signed (KCWB (-50 - ple))) (G3Pure_u.KCZ (-50 - ple)))%bool.
Lemma kcb_all : forallb kcb_okw (G3Pure_u.zseq (-1127) 2099) = true.
Proof. vmc_refl. Qed.
Lemma kcb_facts : forall ple, -1127 <= ple <= 971 ->
  flt_d FLO (ceil_m (KCX (-50 - ple))) = true /\ flt_d (ceil_m (KCX (-50 - ple))) FHI = true /\ bv_signed (KCWB (-50 - ple)) = G3Pure_u.KCZ (-50 - ple).
Proof.
  intros ple Hp. pose proof (proj1 (forallb_forall _ _) kcb_all ple (G3Pure_u.zseq_in (-1127) 2099 ple ltac:(lia))) as H.
  unfold kcb_okw in H. cbv zeta in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H3. auto.
Qed.
