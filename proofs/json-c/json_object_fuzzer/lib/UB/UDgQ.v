(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Module GwI.
Definition segs := rsegs.
End GwI.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x2 := getreg 2%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "sp=" x2.

Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.le8_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.le8_lit)]. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.le4_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.le4_lit)]. Qed.
Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac zstep0 := zs.

Ltac name_cb n H := match type of H with context [CB n ?l] => let j := fresh "jk" in set (j := l) in H; clearbody j end.

Lemma shl52_land64 : forall f, (0 <= f)%Z -> Z.land (Z.shiftl f 52) 18446744073709551615 = (4503599627370496 * (f mod 4096))%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.shl52_land64) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.shl52_land64)]. Qed.
Lemma land_bit11 : forall f, Z.land f 2048 = (2048 * ((f / 2048) mod 2))%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.land_bit11) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.land_bit11)]. Qed.
Lemma land_bit0 : forall f, Z.land f 1 = (f mod 2)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.land_bit0) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.land_bit0)]. Qed.

Lemma signbitl_range : forall x, (0 <= signbitl x <= 1)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.signbitl_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.signbitl_range)]. Qed.

Lemma fpclassifyl_range : forall x, (0 <= fpclassifyl x <= 4)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.fpclassifyl_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.fpclassifyl_range)]. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.sx32_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.sx32_lit)]. Qed.

Ltac unwrapK K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Lemma fother : ltac2:(Q6nq.tyx '(@QQRC.Mq0.fother) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.fother) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.fother)]. Qed.

Definition zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma gw_eq_zb : @zb = ltac:(GwInst.gw_term (@QQRC.Mq0.zb) (@zb)). Proof. unfold zb, QQRC.Mq0.zb; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zb : gw_eqs.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.bytes_le_to_Z_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.bytes_le_to_Z_range)]. Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.Z_to_le_bytes_to_Z) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.Z_to_le_bytes_to_Z)]. Qed.

Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.le4_of_bytes) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.le4_of_bytes)]. Qed.

Lemma u32arr_of_u8arr : ltac2:(Q6nq.tyx '(@QQRC.Mq0.u32arr_of_u8arr) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.u32arr_of_u8arr) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.u32arr_of_u8arr)]. Qed.

Lemma u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.u8arr_of_u32arr) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.u8arr_of_u32arr)]. Qed.

Definition wnth (ws : list word) (i : Z) : word := nth (Z.to_nat i) ws (Z_to_bv 64 0).
Lemma gw_eq_wnth : @wnth = ltac:(GwInst.gw_term (@QQRC.Mq0.wnth) (@wnth)). Proof. unfold wnth, QQRC.Mq0.wnth; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_wnth : gw_eqs.
Definition wval (ws : list word) (i : Z) : Z := (bv_unsigned (wnth ws i) mod 4294967296)%Z.
Lemma gw_eq_wval : @wval = ltac:(GwInst.gw_term (@QQRC.Mq0.wval) (@wval)). Proof. unfold wval, QQRC.Mq0.wval; rewrite ?gw_eq_wnth; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_wval : gw_eqs.

Lemma nth_error_wnth : forall ws i, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> nth_error ws (Z.to_nat i) = Some (wnth ws i).
Proof. rewrite ?gw_eq_wnth; first [GwInst.gw_exact (@QQRC.Mq0.nth_error_wnth) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.nth_error_wnth)]. Qed.

Lemma wval_upd_same : ltac2:(Q6nq.tyx '(@QQRC.Mq0.wval_upd_same) [[@gw_eq_wval]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_wnth__3; @gw_eq_wnth__2; @gw_eq_wnth]] '([4294967296]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_wval; first [GwInst.gw_exact (@QQRC.Mq0.wval_upd_same) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.wval_upd_same)]. Qed.
Lemma wval_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j ->
wval (upd ws (Z.to_nat i) v) j = wval ws j.
Proof. rewrite ?gw_eq_wval; first [GwInst.gw_exact (@QQRC.Mq0.wval_upd_other) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.wval_upd_other)]. Qed.
Lemma wval_range : forall ws i, (0 <= wval ws i < 4294967296)%Z.
Proof. rewrite ?gw_eq_wval; first [GwInst.gw_exact (@QQRC.Mq0.wval_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.wval_range)]. Qed.

Lemma div1e9_magic : ltac2:(Q6nq.tyx '(@QQRC.Mq0.div1e9_magic) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_wnth__3; @gw_eq_wnth__2; @gw_eq_wnth]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]] '([1000000000; 19342813113834067]%Z : list Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.div1e9_magic) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.div1e9_magic)]. Qed.

Lemma sx32_zero : forall w : word, bv_unsigned (sx32 w) = 0%Z <-> (bv_unsigned w mod 4294967296 = 0)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.sx32_zero) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.sx32_zero)]. Qed.
Lemma sx32_nonzero : forall w : word, bv_unsigned (sx32 w) <> 0%Z <-> (bv_unsigned w mod 4294967296 <> 0)%Z.
Proof. first [GwInst.gw_exact (@QQRC.Mq0.sx32_nonzero) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.sx32_nonzero)]. Qed.

Lemma mulhu_M_range : ltac2:(Q6nq.tyx '(@QQRC.Mq0.mulhu_M_range) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_wnth__3; @gw_eq_wnth__2; @gw_eq_wnth]; [@gw_eq_wval__3; @gw_eq_wval__2; @gw_eq_wval]] '([19342813113834067; 18446744073709551616]%Z : list Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@QQRC.Mq0.mulhu_M_range) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq0.mulhu_M_range)]. Qed.
