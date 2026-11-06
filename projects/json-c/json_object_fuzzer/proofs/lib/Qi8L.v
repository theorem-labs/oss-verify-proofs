(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QdBa QqdR QfYR QfcC Ql2m QnDM_c1 QDUx Q9Ay QX7A QhY6 QIsN QYaS QwyL QN1y Qn2i QGmo QvBB QKwd QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QqdR QfYR QfcC Ql2m.
Import QnDM_c1 QDUx Q9Ay.
Import QX7A QhY6 QIsN QYaS QwyL QN1y Qn2i QGmo QvBB.Mq1 QKwd.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Definition FMODL : Z := 0xd83cc.
Definition RFMODL_DEPTH : Z := 192.

Ltac lit_loads :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in (bv_swrap 32 (c mod 2^64))%Z in
let c'' := eval vm_compute in (c' mod 2^64)%Z in
replace (sx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c'') by (unfold sx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
| |- context [zx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in ((c mod 2^64) mod 2^32)%Z in
replace (zx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c') by (unfold zx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
end.

Definition extsf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Lemma extendsftf2_2p120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv rsegs m ->
evt rsegs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) fc C_2P120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) (Z_to_bv 64 0xcb90c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear -K1; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear -K2; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma extendsftf2_2pm120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv rsegs m ->
evt rsegs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) fc C_2PM120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) (Z_to_bv 64 0xcb90c) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear -K1; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear -K2; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma m_fpclassifyl_canon : forall y, fpclassifyl (lo64 y + 2^64 * hi64 y) = m_fpclassifyl y.
Proof.
intros y. unfold fpclassifyl, m_fpclassifyl. change (lo64 y + 2^64 * hi64 y)%Z with (canon y).
rewrite lo64_canon, hi64_canon. unfold nz. reflexivity.
Qed.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - RFMODL_DEPTH) q
/\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).

Definition rfmodl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
stk rsegs m (q - RFMODL_DEPTH) q -> mem_inv rsegs m ->
(4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
m_fmodl X Y = Some r ->
evt rsegs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom rsegs)).

Section Fmodl.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (X Y r : Z).
Hypothesis SPLO : (4096 <= q - RFMODL_DEPTH)%Z.
Hypothesis SPHI : (q < 2^63)%Z.
Hypothesis HM : m_fmodl X Y = Some r.

Notation POST := (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Definition frame : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv rsegs m /\ munch [(q - RFMODL_DEPTH, q)]%Z m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -80) frame /\ stk rsegs m (q - RFMODL_DEPTH) (q + -80).
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST); unfold frame in FR; unfold RFMODL_DEPTH in MU, ST.
Ltac mk_finv := unfold finv, frame, RFMODL_DEPTH; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|hyp].

Definition Fok (F' : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. intros k _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set10 : forall F' v, Fok F' -> Fok (bvmap_set 10 v F').
Proof. intros F' v H k Hk. rewrite reg_get_set_other by (intros E; apply Hk; rewrite <- E; reflexivity). apply H. exact Hk. Qed.

Definition exv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x7fff.
Definition eyv : Z := Z.land (Z.shiftr (hi64 Y) 48) 0x7fff.
Definition sxv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x8000.

#[using="Type"] Lemma L_ret : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8448) fc None m (seg_rom rsegs)).
Proof.
intros until x1. intros FI FOK. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold rfmodl_post, RFMODL_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact FOK].
Qed.

Definition DS : divtf3_stmt := QYaS.divtf3_spec.
#[using="Type"] Lemma stk_lower : forall m lo lo' hi, stk rsegs m lo hi -> (lo <= lo' <= hi)%Z -> stk rsegs m lo' hi.
Proof. intros m lo lo' hi ST H. exact (proj2 (stk_split _ _ _ _ _ ST H)). Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 192)%Z (q + -80)%Z |- _ =>
let ST1 := fresh "ST1" in let ST2 := fresh "ST2" in
destruct (stk_split _ _ _ (q + -80 - K)%Z _ ST ltac:(lia)) as [ST1 ST2]; clear ST;
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -80 - K)%Z (q + -80)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1 STn ltac:(lia)) as ST; clear ST1 STn end
end.

#[using="SPLO SPHI"] Lemma L_nan : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_div (f128_mul X Y) (f128_mul X Y) ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8428) fc None m (seg_rom rsegs)).
Proof.
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. zs.
zs. call_split 112%Z (eapply (divtf3_callq DS); [hyp | hyp | lia]).
rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="SPLO SPHI"] Lemma L_zero : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_mul (f128_of_i32 0) X ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd85ec) fc None m (seg_rom rsegs)).
Proof.
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="Type"] Lemma L_retx : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1 lo hi,
finv m -> Fok F' -> Z_to_bv 64 lo = Z_to_bv 64 (lo64 r) -> Z_to_bv 64 hi = Z_to_bv 64 (hi64 r) ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd865c) fc None m (seg_rom rsegs)).
Proof.
intros until hi. intros FI FOK Hlo Hhi. pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. rewrite Hlo, Hhi. apply L_ret; [exact FI | exact FOK].
Qed.

#[using="Type"] Lemma sxv_cases : sxv = 0%Z \/ sxv = 32768%Z.
Proof. unfold sxv. change 32768%Z with (2^15)%Z. rewrite land_pow2_bit by lia. destruct (Z.testbit _ _); [right|left]; reflexivity. Qed.
#[using="Type"] Lemma sext_field : forall e, Z.land (Z.lor (Z.land e 65535) sxv) 65535 = Z.land (Z.lor e sxv) 65535.
Proof.
intros e. rewrite !zb_land_lor_distr_l, <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.
#[using="Type"] Lemma exv_range : (0 <= exv < 32768)%Z.
Proof. unfold exv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range X). lia. Qed.
#[using="Type"] Lemma eyv_range : (0 <= eyv < 32768)%Z.
Proof. unfold eyv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range Y). lia. Qed.
#[using="Type"] Lemma shr48X : Z.shiftr (hi64 X) 48 = (hi64 X / 2^48)%Z. Proof. apply Z.shiftr_div_pow2. lia. Qed.

#[using="Type"] Lemma land_M_16 : forall e, Z.land (Z.land e 18446744073709551615) 65535 = Z.land e 65535.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

#[using="Type"] Lemma pack_bridge : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land xhi 281474976710655) (Z.land (Z.shiftl (Z.lor (Z.land E 65535) sxv) 48) 18446744073709551615))
= Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof.
intros xhi xlo E Hxlo. rewrite Z.lor_comm. rewrite (proj1 (pack_eq xhi xlo _ Hxlo)). rewrite sext_field. reflexivity.
Qed.
#[using="Type"] Lemma pack_bridge_lo : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof. intros xhi xlo E Hxlo. exact (proj2 (pack_eq xhi xlo _ Hxlo)). Qed.

#[using="SPLO SPHI"] Lemma L_scale : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 <= ex < 2^20)%Z ->
fmodl_scale sxv (xhi, xlo, ex) = r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd862c) fc None m (seg_rom rsegs)).
Proof.
intros until ex. intros FI FOK Rh Rl Re HS.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof sxv_cases as SX. unfold sxv in SX.
unfold fmodl_scale in HS.
zs. zs. zs. zs. zs. zs. brs K1.
-
replace (ex <=? 0) with true in HS by (symmetry; apply Z.leb_le; lia).
do 7 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo (ex + 120)) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
zs. zs. zs. callw (eapply extendsftf2_2pm120; hyp).
zs. zs. zs. zs. rewrite (pack_bridge_lo xhi xlo (ex + 120)) by lia.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite HS. apply L_ret; [mk_finv | apply Fok_set10; exact FOK].
- replace (ex <=? 0) with false in HS by (symmetry; apply Z.leb_gt; lia).
do 6 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo ex) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
eapply L_retx; [exact FI | exact FOK | rewrite <- HS; apply pack_bridge_lo; lia | rewrite <- HS; reflexivity].
Qed.

#[using="SPLO SPHI"] Lemma L_L2 : forall (n : nat) m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) st',
finv m -> Fok F' ->
(0 <= xhi < 2^48)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 + Z.of_nat n <= ex < 2^20)%Z ->
fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) = Some st' -> fmodl_scale sxv st' = r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8610) fc None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; intros until st'; intros FI FOK Rh Rl Re HL HS; [discriminate HL|].
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_norm_body in HL. rewrite fmodl_norm_loop_step in HL.
zs. zs. zs. zs. zs. zs. fixw. zs.

set (b := Z.shiftr xlo 63) in *. assert (Rb : (0 <= b <= 1)%Z) by (subst b; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E1 : Z.land (Z.shiftl xhi 1) 18446744073709551615 = (xhi * 2)%Z) by (rewrite land_W64, Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia).
rewrite !E1 in *.
assert (E2 : Z.lor (xhi * 2) b = (b + xhi * 2)%Z) by (rewrite Z.lor_comm; change (xhi * 2)%Z with (xhi * 2^1)%Z; apply lor_low_high; lia).
rewrite !E2 in *.
assert (E3 : u64 (2 * xhi + b) = (b + xhi * 2)%Z) by (unfold u64; rewrite Z.mod_small by lia; lia).
rewrite !E3 in HL.
assert (E4 : Z.shiftr (b + xhi * 2) 48 = Z.shiftr (xhi * 2) 48) by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
rewrite E4 in HL.
assert (R5 : (0 <= Z.shiftr (xhi * 2) 48 < 2^16)%Z) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E6 : Z.land (Z.shiftl xlo 1) 18446744073709551615 = u64 (2 * xlo)) by (unfold u64; rewrite land_W64, Z.shiftl_mul_pow2 by lia; f_equal; lia).
rewrite ?E6 in *. pose proof (Z.mod_pos_bound (2 * xlo) (2^64) ltac:(lia)) as R6. unfold u64 in *.
replace (Z_to_bv 64 (Z.shiftl xlo 1)) with (Z_to_bv 64 ((2 * xlo) mod 2^64)%Z) by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2, Z.mod_mod by lia; f_equal; lia).
replace (ex + -1)%Z with (ex - 1)%Z by lia.
(if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?Z.shiftr_div_pow2 in K2 by lia.
-
replace (Z.shiftr (xhi * 2) 48 =? 0) with true in HL by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
eapply (IH m); [exact FI | exact FOK | | | | exact HL | exact HS]; lia.
- replace (Z.shiftr (xhi * 2) 48 =? 0) with false in HL by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia).
injection HL as <-.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
Qed.

#[using="SPLO SPHI"] Lemma L_K2 : forall m (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K2 sxv (xhi, xlo, ex) = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8604) fc None m (seg_rom rsegs)).
Proof.
intros until ex. intros FI FOK Rh Rl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K2 in HK. change 130%nat with (S 129) in HK. rewrite fmodl_norm_loop_step in HK.
pose proof (shr48_range xhi Rh) as R48.
rewrite Z.shiftr_div_pow2 in R48 by lia.
zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)); rewrite ?Z.shiftr_div_pow2 in K1 by lia.
- replace (Z.shiftr xhi 48 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia). injection HK as HS.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
- replace (Z.shiftr xhi 48 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
destruct (fmodl_norm_loop 129 _) as [st'|] eqn:HL; [|discriminate HK]. injection HK as HS.
eapply L_L2; [exact FI | exact FOK | | exact Rl | | exact HL | exact HS].
+ Z.div_mod_to_equations. lia.
+ lia.
Qed.

#[using="SPLO SPHI"] Lemma L_fin : forall m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo yhi ylo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K1 X yhi ylo sxv (inl (xhi, xlo, ex)) = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd85cc) fc None m (seg_rom rsegs)).
Proof.
intros until ex. intros FI FOK Rxh Rxl Ryh Ryl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K1, fmodl_fin in HK.
destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4). cbv zeta in B1, B2, B3.
set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
zs. zs. zs. rewrite B2.
rewrite (shr63_eqb hi') in HK by lia.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (hi' <? 2^63) with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
- replace (hi' <? 2^63) with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. rewrite <- B4. pose proof (Z.mod_pos_bound (xlo - ylo) (2^64) ltac:(lia)) as Rlo. unfold u64 in HK, Rlo |- *.
assert (RL : (0 <= Z.lor hi' ((xlo - ylo) mod 2^64) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
change 18446744073709551616%Z with (2^64)%Z in *.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with false in HK by (symmetry; apply Z.eqb_neq; exact K2).
rewrite <- (Z_to_bv_mod64 (xlo - ylo)).
eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with true in HK by (symmetry; apply Z.eqb_eq; exact K2).
injection HK as Hr. zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
Qed.

#[using="Type"] Lemma dbl_bridge : forall h b, (0 <= h < 2^64)%Z -> (0 <= b <= 1)%Z ->
Z.lor (Z.land (Z.shiftl h 1) 18446744073709551615) b = u64 (2 * h + b).
Proof.
intros h b Hh Hb. rewrite land_W64, Z.shiftl_mul_pow2 by lia. unfold u64.
replace ((h * 2^1) mod 2^64)%Z with ((h mod 2^63) * 2^1)%Z by (Z.div_mod_to_equations; lia).
rewrite Z.lor_comm, lor_low_high by (try lia; Z.div_mod_to_equations; lia).
Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma shr63_b : forall l, (0 <= l < 2^64)%Z -> (0 <= Z.shiftr l 63 <= 1)%Z.
Proof. intros l Hl. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma u64_range : forall v, (0 <= u64 v < 2^64)%Z.
Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
#[using="Type"] Lemma zbv_shl1 : forall v, Z_to_bv 64 (Z.shiftl v 1) = Z_to_bv 64 (u64 (2 * v)).
Proof. intros. rewrite zbv_u64, Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

#[using="SPLO SPHI"] Lemma L_L1 : forall (yhi ylo ey : Z) (n : nat) m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) res,
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
(-2^18 <= ey)%Z -> (ey < ex < 2^18)%Z ->
fmodl_sub_loop (S n) X yhi ylo ey (xhi, xlo, ex) = Some res -> fmodl_K1 X yhi ylo sxv res = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8564) fc None m (seg_rom rsegs)).
Proof.
intros yhi ylo ey. induction n as [|n IH]; intros until res; intros FI FOK Rxh Rxl Ryh Ryl Rey Rex HL HK.
all: pose proof FI as FI'; dest_finv FI'; unfold RFMODL_DEPTH in SPLO; pose proof (hi64_range X) as RHX.
all: rewrite fmodl_sub_loop_step in HL; replace (ey <? ex) with true in HL by (symmetry; apply Z.ltb_lt; lia).
all: unfold fmodl_sub_body in HL.
all: destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4); cbv zeta in B1, B2, B3.
all: set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
all: rewrite (shr63_eqb hi') in HL by lia.
all: pose proof (shr63_b xlo Rxl) as Rb; pose proof (u64_range (xlo - ylo)) as Rlo; pose proof (shr63_b (u64 (xlo - ylo)) Rlo) as Rb2.
all: zs; zs; zs; rewrite B2; zs; (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).

- replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [fmodl_sub_loop] in HL. discriminate HL.
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
cbn [fmodl_sub_loop] in HL. discriminate HL.
-
replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. rewrite (dbl_bridge xhi (Z.shiftr xlo 63)) by lia.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
zs. zs. zs. rewrite (dbl_bridge hi' (Z.shiftr (u64 (xlo - ylo)) 63)) by lia. zs.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
Qed.

#[using="Type"] Lemma ex_field : forall v, (0 <= v < 2^16)%Z -> Z.shiftr (Z.land (Z.shiftl v 49) 18446744073709551615) 49 = Z.land v 32767.
Proof.
intros v Hv. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
destruct (Z.lt_ge_cases i 15).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
Qed.
#[using="Type"] Lemma mant_or_range : forall h, (0 <= Z.lor (Z.land h 281474976710655) 281474976710656 < 2^64)%Z.
Proof.
intros h. pose proof (land48_range h) as R. change 0x0000ffffffffffff%Z with 281474976710655%Z in R.
change 281474976710656%Z with (1 * 2^48)%Z. rewrite lor_low_high by lia. lia.
Qed.

#[using="SPLO SPHI"] Lemma L_setup : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1
(uxh uxl uyh uyl ex ey : Z),
finv m -> Fok F' ->
(0 <= uxh < 2^64)%Z -> (0 <= uxl < 2^64)%Z -> (0 <= uyh < 2^64)%Z -> (0 <= uyl < 2^64)%Z ->
(-2^18 <= ey < 2^18)%Z -> (-2^18 <= ex < 2^18)%Z ->
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl ey
(Z.lor (Z.land uxh 0x0000ffffffffffff) (2^48), uxl, ex) with
| Some res => fmodl_K1 X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl sxv res
| None => None end = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 uyl) (Z_to_bv 64 uxl) (Z_to_bv 64 uyh) (Z_to_bv 64 uxh) (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd8528) fc None m (seg_rom rsegs)).
Proof.
intros until ey. intros FI FOK R1 R2 R3 R4 R5 R6 HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (mant_or_range uxh) as Q1. pose proof (mant_or_range uyh) as Q2.
change (2^48)%Z with 281474976710656%Z in HK. change 0x0000ffffffffffff%Z with 281474976710655%Z in HK.
do 7 zs. rewrite ?land_W64, ?(Z.mod_small (Z.lor _ _) (2^64)) by lia.
zs. brs K1.
-
destruct (fmodl_sub_loop _ _ _ _ _ _) as [res|] eqn:HL; [|discriminate HK].
eapply L_L1; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HL | exact HK].
- zs. rewrite fmodl_sub_loop_step in HK. replace (ey <? ex) with false in HK by (symmetry; apply Z.ltb_ge; lia).
eapply L_fin; [exact FI | exact FOK | lia | lia | lia | lia | lia | exact HK].
Qed.

Definition UX : Z := mk128 (Z.land (hi64 X) 0x7fffffffffffffff) (lo64 X).
Definition UY : Z := mk128 (Z.land (hi64 Y) 0x7fffffffffffffff) (lo64 Y).
#[using="Type"] Lemma UX_words : lo64 UX = lo64 X /\ hi64 UX = Z.land (hi64 X) 0x7fffffffffffffff.
Proof. unfold UX. pose proof (lo64_range X). pose proof (land63_range (hi64 X) (hi64_range X)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.
#[using="Type"] Lemma UY_words : lo64 UY = lo64 Y /\ hi64 UY = Z.land (hi64 Y) 0x7fffffffffffffff.
Proof. unfold UY. pose proof (lo64_range Y). pose proof (land63_range (hi64 Y) (hi64_range Y)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Definition K_normy (ux ex uy ey : Z) : option Z :=
(let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X yhi (lo64 uy) ey (xhi, lo64 ux, ex) with
| Some res => fmodl_K1 X yhi (lo64 uy) sxv res
| None => None end)%Z.

#[using="SPLO SPHI"] Lemma L_normy : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1 (ux ex : Z) (wl wh : word),
finv m -> Fok F' -> (-2^18 <= ex < 2^18)%Z ->
K_normy ux ex (f128_mul UY C_2P120) (Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120)%Z = Some r ->
wl = Z_to_bv 64 (lo64 ux) -> wh = Z_to_bv 64 (hi64 ux) ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 UY)) wl (Z_to_bv 64 (hi64 UY)) wh (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 0) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd84f8) fc None m (seg_rom rsegs)).
Proof.
intros until wh. intros FI FOK Re HK -> ->.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (lo64_range UY) as R1. pose proof (hi64_range UY) as R2. pose proof (lo64_range ux) as R3. pose proof (hi64_range ux) as R4.
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
set (uy' := f128_mul UY C_2P120) in *. pose proof (lo64_range uy') as R5. pose proof (hi64_range uy') as R6.
pose proof (shr48_range (hi64 uy') R6) as R7.
zs. zs. zs. zs.
unfold K_normy in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | | lia | exact HK].
rewrite Z.shiftr_div_pow2 in R7 |- * by lia. lia.
Qed.

#[using="SPLO SPHI"] Lemma L_norm : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey) = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 (Z.land (hi64 Y) 0x7fffffffffffffff)) (Z_to_bv 64 (Z.land (hi64 X) 0x7fffffffffffffff))
(Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 exv) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xd84e4) fc None m (seg_rom rsegs)).
Proof.
intros until x1. intros FI FOK HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof exv_range as REX. pose proof eyv_range as REY.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
zs. zs. rewrite (fpc_exp_field (hi64 Y)) by lia. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (exv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia).
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. rewrite <- EUXl, <- EUXh. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
rewrite EUXl.
set (ux' := f128_mul UX C_2P120) in *. pose proof (lo64_range ux') as R5. pose proof (hi64_range ux') as R6.
pose proof (shr48_range (hi64 ux') R6) as R7. rewrite Z.shiftr_div_pow2 in R7 by lia.
zs. zs. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+
replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUYl, EUYh in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | lia | | exact HK].
rewrite Z.shiftr_div_pow2 by lia. lia.
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [mk_finv | apply Fok_set10; exact FOK | | exact HK | reflexivity | reflexivity].
rewrite Z.shiftr_div_pow2 by lia. lia.
- replace (exv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUXl, EUXh, EUYl, EUYh in HK.
eapply L_setup; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HK].
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [exact FI | exact FOK | lia | exact HK | rewrite EUXl; reflexivity | rewrite EUXh; reflexivity].
Qed.

Definition K_norm : option Z :=
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey).
Definition K_cmp : option Z :=
if f128_le UX UY <=? 0 then (if f128_le UX UY =? 0 then Some (f128_mul (f128_of_i32 0) X) else Some X) else K_norm.

#[using="SPLO SPHI"] Lemma L_cmp : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) x1,
finv m ->
(if exv =? 32767 then Some (f128_div (f128_mul X Y) (f128_mul X Y)) else K_cmp) = Some r ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8488) fc None m (seg_rom rsegs)).
Proof.
intros until x1. intros FI HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof (shr48_range (hi64 X) RHX) as R48.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
pose proof exv_range as REX.
zs. zs. zs. zs. try rewrite (ex_field (Z.shiftr (hi64 X) 48)) by lia. change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv.
zs. fixw. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
- replace (exv =? 32767) with true in HK by (symmetry; apply Z.eqb_eq; lia). injection HK as Hr.
eapply L_nan; [exact FI | apply Fok_refl | symmetry; exact Hr].
- replace (exv =? 32767) with false in HK by (symmetry; apply Z.eqb_neq; lia). unfold K_cmp in HK.
pose proof (f128_le_range UX UY) as RLE.
zs. zs. zs. zs. zs. zs. zs. zs.
rewrite <- EUXl, <- EUXh, <- EUYl, <- EUYh.
zs. callw (eapply letf2_callv; hyp).
zs. brs K2.
+ replace (f128_le UX UY <=? 0) with false in HK by (symmetry; apply Z.leb_gt; lia).
rewrite EUXl, EUXh, EUYl, EUYh. eapply L_norm; [mk_finv | apply Fok_refl | exact HK].
+ replace (f128_le UX UY <=? 0) with true in HK by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
* replace (f128_le UX UY =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K3 RLE; mlia2). injection HK as Hr.
rewrite EUXl. replace (Z_to_bv 64 (f128_le UX UY)) with (Z_to_bv 64 0) by (f_equal; clear -K3 RLE; mlia2).
eapply L_zero; [mk_finv | apply Fok_refl | symmetry; exact Hr].
* replace (f128_le UX UY =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K3 RLE; mlia2). injection HK as Hr.
zs. rewrite EUXl. eapply L_retx; [mk_finv | apply Fok_refl | rewrite Hr; reflexivity | rewrite Hr; reflexivity].
Qed.

#[using="SPLO SPHI HM"] Lemma L_entry : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
stk rsegs m0 (q - RFMODL_DEPTH) q -> mem_inv rsegs m0 ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m0 (seg_rom rsegs)).
Proof.
intros until t6. intros ST MI.
pose proof (munch_refl [(q - RFMODL_DEPTH, q)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
unfold RFMODL_DEPTH in ST, MU, SPLO. unfold FMODL.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof HM as HK. rewrite m_fmodl_split in HK. cbv zeta in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv in HK. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv in HK.
fold UX UY in HK.
zs. carve_frame 80%nat ST.
do 15 zs.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
set (t00 := f128_of_i32 0) in *. pose proof (lo64_range t00) as RT1. pose proof (hi64_range t00) as RT2.
pose proof (f128_le_range Y t00) as RLE.
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (f128_le Y t00 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K1 RLE; mlia2). cbn [orb] in HK.
zs. zs. zs. callw (eapply fpclassifyl_spec; eassumption). norm_rsegs.
rewrite !ulit_lo64, !ulit_hi64, m_fpclassifyl_canon.
assert (RC : (0 <= m_fpclassifyl Y <= 4)%Z) by (unfold m_fpclassifyl; repeat (destruct (_ : bool)); lia).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (m_fpclassifyl Y =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K2 RC; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
+ replace (m_fpclassifyl Y =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K2 RC; mlia2). cbn [orb] in HK.
eapply L_cmp; [mk_finv | exact HK].
- replace (f128_le Y t00 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K1 RLE; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
Qed.
End Fmodl.

Lemma rfmodl_spec : rfmodl_stmt.
Proof.
unfold rfmodl_stmt. intros. eapply L_entry; eassumption.
Qed.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache Qy5Y Qbf8 QSzV QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import Qbf8 QSzV QvBB.Mq1.
Export QnkH.Mq1.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. intros. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
pose proof (f_equal bv_unsigned E) as E2. rewrite !Qy5Y.unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells rsegs m A [CB 1 bs] -> exists b, rw_cells rsegs m A [CB 1 [b]].
Proof.
intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells rsegs m A (CB 0 [] :: cs) -> rw_cells rsegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bytes_at rsegs m' A buf.
Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
bytes_at rsegs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv rsegs m ->
evt rsegs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb250) fc None m (seg_rom rsegs)).
Proof.
intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply QSzV.memchr_spec with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
intros ms' P. unfold QSzV.memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv rsegs m ->
evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply Qbf8.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold Qbf8.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 64) (q)
/\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
/\ rw_cells rsegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
/\ bytes_at rsegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at rsegs m T (zbytes txt) -> rw_cells rsegs m D [CB 1 [dj]] ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 STRING_READ) fc None m (seg_rom rsegs)).

End Mq1.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QlEo_c1 Q2qa QytA Q4J3 QPjm QJE4 QWTl QXxF QUZl Q7S0 QGeV QYTG QCwx QFqQ Q98Z QkLq QnOf QdZ1 QQbX Qv4L Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QDUx.Mq2 Q9Ay.Mq9 QXxF.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.

Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq2 QQbX.Mq1 QdZ1.Mq0 Qv4L.Mq1 QnkH.Mq3 QnkH.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce49c) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (rid : N) (off : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
(Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce484) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce460) fc None m (seg_rom rsegs)).
Proof.
intros until off. intros MR CNT BRK C0 C1b.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

#[using="Type"] Lemma ram_brk0_node :
impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0)
(epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0xce4a0) fc None m (seg_rom rsegs) /\ 0 <= r < 2^64))
(MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0xce49c) fc None m (seg_rom rsegs)).
Proof.
unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0xce49c + 4)%Z with 0xce4a0%Z by reflexivity.
apply evt_done. split; [reflexivity| exact Hr].
Qed.

#[using="Type"] Lemma ram_brk_node_at (pc : Z) :
(pc = 0xce484 \/ pc = 0xce4c0) -> forall cur req, req <> 0 ->
impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
(epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom rsegs)))
(MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
intros Hpc cur req NZ. unfold rbrk_regs.
destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
[ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
| rewrite apply_mem_none ];
apply evt_done; reflexivity).
Qed.
End BRKNODES.

#[using="Type"] Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
(m : word -> option byte) (cur : Z),
0 < cur < 2^64 -> cur mod 4096 = 0 ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists a2' m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce4c0) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce4a0) fc None m (seg_rom rsegs)).
Proof.
intros until cur. intros CR CAL TC MI.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (land_neg_aligned cur CR CAL) as AL.
assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
change (cur mod 4096 = 0) with (pgal cur) in CAL.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in TC. change (6566376 + 920) with 6567296 in MU. change (6566376 + 928) with 6567304 in MU.

st1. st1. rewrite ?AL, ?AL'. st1. st1.
replace (0 + cur) with cur by lia.

st1. st1. st1. st1.
replace (8192 + cur) with (cur + 8192) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

#[using="Type"] Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
(m : word -> option byte) (cur : Z),
0 < cur -> cur + 8192 < 2^64 ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xce4e4) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
(Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce4c4) fc None m (seg_rom rsegs)).
Proof.
intros until cur. intros C0 C1b TC.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in TC.

st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

#[using="Type"] Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce570) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce4e4) fc None m (seg_rom rsegs)).
Proof.
intros until nw. intros NW HC TC MI.
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in TC.
change (6566376 + 40) with 6566416 in MU. change (6566376 + 48) with 6566424 in MU. change (6566376 + 920) with 6567296 in MU. change (6566376 + 928) with 6567304 in MU.

st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

#[using="Type"] Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells rsegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce570) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells rsegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce488) fc None m (seg_rom rsegs)).
Proof.
intros until nw. intros NW HC TC MI.

st1. rewrite bv_eqb_refl. cbv iota.
eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

#[using="Type"] Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce4f8) fc None m (seg_rom rsegs)).
Proof.
intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
lazymatch type of C1 with rw_cells _ _ _ ?cs =>
assert (C1' : rw_cells rsegs m RCTX cs)
by (eapply Q98Z.Mq2.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
clear C1.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6566376 + 912) with 6567288 in TC.
change (6566376 + 920) with 6567296 in MU, MU0. change (6566376 + 928) with 6567304 in MU, MU0.

st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
{ eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
- unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
- first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (6566376 + 912) with 6567288.
replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with H : rw_cells rsegs ?mX 6567288 _ |- _ => exact H end. }
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
F fc (m : word -> option byte) (st : mstate) (old : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce488) fc None m (seg_rom rsegs)).
Proof.
intros until old. intros MR CNT O0 O1 MI.
pose proof MR as (WF & (_ & _ & _ & _ & _ & C6 & _) & _). unfold ctx_tail_cells in C6.

st1.
assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.

#[using="Type"] Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
rw_cells rsegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce510) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce4c4) fc None m (seg_rom rsegs)).
Proof.
intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.

st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
{ apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
rewrite CF; clear CF.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE Q8P7 QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.

Import QnDM_c1.Mq0 Q2qa.Mq1 QytA QlQE Qy5Y.Mq6 Q4J3.Mq4.
Export Q8P7.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QWTl.Mq2 QWTl.Mq3 Q9Ay.Mq9.
Export QBeb.
Import QCwx.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RAMpre := (@AMpre_g ref_reserved rc_secret).
Notation ram_pre := (am_pre_g ref_reserved rc_secret).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

#[using="AMP"] Lemma rAMpre_init : RAMpre (am_init_st st).
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
- rewrite A3. exact rc_secret_range.
- right; reflexivity.
- destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

#[using="Type"] Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

#[using="RC__ AMP"] Lemma rAMI_init : AMI st (am_init_st st).
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
(split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| intros rid r Hr; exists r; repeat split; auto; lia
| intros rid r' H1 H2; cbn in H1; congruence
| cbn; lia
| intros P _ HP; exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
| intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
| exact (amp_rpos st AMP) ]).
- cbn. rewrite (amp_s_secret st AMP). exact rc_secret_range.
- exact (amp_secret st AMP).
Qed.

#[using="Type"] Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E6.
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.

#[using="Type"] Lemma ram_rel_final stX st1 mo :
AMI st stX ->
c_active (ctx st1) = c_active (ctx stX) -> c_usage (ctx st1) = c_usage (ctx stX) -> c_unmap_seq (ctx st1) = c_unmap_seq (ctx stX) ->
c_bounces (ctx st1) = c_bounces (ctx stX) -> c_seq (ctx st1) = c_seq (ctx stX) -> c_mmap_counter (ctx st1) = c_mmap_counter (ctx stX) ->
s_groups st1 = s_groups stX -> s_slots st1 = s_slots stX -> s_shadow st1 = s_shadow stX -> s_tick st1 = s_tick stX ->
s_reserved st1 = s_reserved stX -> s_regions st1 = s_regions stX -> s_next_rid st1 = s_next_rid stX ->
(forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas st1) !! a)) ->
(forall g, Some g <> mo -> (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) -> get_meta_rec st1 g = get_meta_rec stX g) ->
(forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m) ->
(forall P : N -> Prop, (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P stX -> ptrs_in P st1) ->
am_rel st st1 mo.
Proof.
intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split.
- intros sc. unfold active. rewrite E1, C7. reflexivity.
- intros sc. unfold usage. rewrite E2, C8. reflexivity.
- intros i. unfold bounces. rewrite E4, C10. reflexivity.
- intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
- rewrite E5, C11. reflexivity.
- rewrite E6, C1. reflexivity.
- rewrite EG, XG. reflexivity.
- rewrite ESl, XS. reflexivity.
- rewrite ESh, XSH. reflexivity.
- rewrite ET, XT. reflexivity.
- rewrite ERs, XR. reflexivity.
- intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
- exact HR.
- intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
- intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
- rewrite EN. exact XNX.
- intros a Ha. apply HA. rewrite XA. exact Ha.
- intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
- intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.

#[using="Type"] Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof.
intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
- intros m Hm. discriminate.
Qed.

#[using="Type"] Lemma ram_rel_take stX q :
AMI st stX -> c_avail_meta (ctx st) = Some q -> (s_metas st) !! q = None -> meta_slot st q ->
am_rel st (am_took stX q (c_avail_meta_count (ctx stX) - 1)) (Some q).
Proof.
intros AI AVM MQ MSq. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
unfold am_took. rewrite upd_meta_put.
eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
- intros a Ha. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
+ apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
- intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta.
+ cbn. exact I.
+ cbn. exact I.
+ unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
+ pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
try assumption; try reflexivity.
cbn. rewrite C3, AVM in H2. exact H2.
Qed.

#[using="Type"] Lemma ram_rel_carve stX p r :
AMI st stX -> (s_regions stX) !! (fst p) = Some r -> r_kind r <> RKGroup ->
(s_areas stX) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas stX) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx stX) = Some tl -> is_Some ((s_areas stX) !! tl)) ->
am_rel st (am_took (carve_st stX p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
{ replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }

assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
/\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
/\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
/\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
/\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
/\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
/\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
{ destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
- destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
+ intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct H0 as (H1 & _). exact H1.
* destruct H0 as (_ & H2 & _). exact H2.
* destruct H0 as (_ & _ & H3 & _). exact H3.
* exact HP.
* exact HP.
* destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
{ apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
split; [exact Q8|]. split; [| exact Q10].
intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
- rewrite (carve_st_none stX p HT ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. exact Ha.
+ intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
rewrite EC. unfold am_took. rewrite upd_meta_put.
set (stD := set_areas _ stC).
eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
- intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
+ apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
- intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
+ unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
+ apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct (RP P HPp HP0) as (H1 & _). exact H1.
* exact HPp.
* destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
* destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
split; [exact H8|]. split; [| exact H10].
intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

#[using="Type"] Lemma ram_rel_deq stI h nx pv :
AMI st stI ->
c_free_meta_head (ctx st) = Some h -> c_free_meta_head (ctx stI) = Some h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv -> (nx = h <-> pv = h) ->
meta_slot st h -> clr_links (get_meta_rec st h) = meta0 ->
m_mem (get_meta_rec st nx) = None -> m_next (get_meta_rec st nx) <> None ->
m_mem (get_meta_rec st pv) = None -> m_next (get_meta_rec st pv) <> None ->
am_rel st (dequeue LFree h stI) (Some h).
Proof.
intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
destruct (aptr_eqb nx h) eqn:E.
-
apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
* change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
* pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
-
assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
{ change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
rewrite !get_meta_rec_put_other by congruence. apply GM. }
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
rewrite !get_meta_rec_put_other by assumption. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same, R3. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
assert (P1 : ptrs_in P st1).
{ unfold st1. apply QWTl.Mq5.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
- destruct (H8 pv) as (X & _ & _). exact X.
- destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P2 : ptrs_in P st2).
{ unfold st2. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P3 : ptrs_in P st3).
{ unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
apply rptrs_in_upd_ctx; cbn; try reflexivity.
- exact Q2.
- change (ctx st2) with (ctx stI). exact H2.
- change (ctx st2) with (ctx stI). exact H3.
- change (ctx st2) with (ctx stI). exact H4.
- change (ctx st2) with (ctx stI). exact H5.
- change (ctx st2) with (ctx stI). exact H7.
- exact P2. }
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
rewrite R3. rewrite <- GM. exact Q3.
Qed.

#[using="Type"] Lemma rAMI_ctx stX f :
AMI st stX ->
ctx_core_eq (ctx stX) (f (ctx stX)) -> 0 <= c_secret (f (ctx stX)) < 2^64 ->
(c_avail_meta_areas (f (ctx stX)) = c_avail_meta_areas (ctx stX)
\/ exists q r, c_avail_meta_areas (f (ctx stX)) = Some q /\ (s_regions stX) !! (fst q) = Some r /\ r_kind r <> RKGroup) ->
(c_brk (f (ctx stX)) = c_brk (ctx stX)
\/ c_brk (f (ctx stX)) = BrkDead
\/ exists rid off r, c_brk (f (ctx stX)) = BrkLive rid off /\ (s_regions stX) !! rid = Some r /\ r_kind r <> RKGroup) ->
AMI st (upd_ctx f stX).
Proof.
intros AI CE SR HA HB. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split; cbn; try assumption.
- destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
- intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
+ destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
+ destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
+ exact (XP P HPn HP0).
Qed.

#[using="Type"] Lemma rAMI_new_region stX k base len :
AMI st stX -> k <> RKGroup -> 0 < len ->
AMI st (fst (new_region k base len stX))
/\ (s_regions (fst (new_region k base len stX))) !! (s_next_rid stX) = Some (mkRegion k base len)
/\ (forall q, fst q <> s_next_rid stX -> conc (fst (new_region k base len stX)) q = conc stX q)
/\ (forall off, conc (fst (new_region k base len stX)) (s_next_rid stX, off) = base + off).
Proof.
intros AI NK LEN. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
unfold new_region. cbn [fst].
set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
split; [| split; [| split]].
- split; cbn -[insert]; try assumption.
+ intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
+ intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
+ unfold rid. lia.
+ intros P HPn HP0. apply (QWTl.Mq5.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
+ intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
+ intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
- rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
- intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
- intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

#[using="Type"] Lemma rAMI_grow stX rid r off :
AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof.
intros AI Hr NK LEN st'. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
assert (CQ : forall q, conc st' q = conc stX q).
{ intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
split; cbn -[insert]; try assumption.
- intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
destruct (decide (q = rid)) as [->|NE].
+ rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
intros HG. exfalso. apply NK. rewrite K'. exact HG.
+ exists r'. auto.
- intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
- intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
destruct (decide (q = rid)) as [->|NE].
+ apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
+ apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
- intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
+ destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
+ apply XF. exact Hq.
- intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QdZ1.Mq3 QQbX.Mq3 Qv4L.Mq7 Qv4L.Mq0 Qv4L.Mq8 QnkH.Mq7.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rcoarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
(pw st (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8f8) fc None m (seg_rom rsegs)
/\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR : rmrep st1 m1.
Hypothesis MI : mem_inv rsegs m1.

#[using="LB m1 MF MR"] Lemma ractive_ptr_facts sc g : active st sc = Some g -> 0 < conc st1 g /\ conc st1 g + 40 <= alloc_ceiling /\ meta_slot st1 g
/\ (exists b, m_mem (get_meta_rec st g) = Some b)
/\ 0 <= m_avail (get_meta_rec st g) < 2^32 /\ 0 <= m_freed (get_meta_rec st g) < 2^32
/\ 0 <= m_last_idx (get_meta_rec st g) + 32 * m_freeable (get_meta_rec st g) + 64 * m_sizeclass (get_meta_rec st g) + 4096 * m_maplen (get_meta_rec st g) < 2^64.
Proof.
intros ACT.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & NN).
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hm). cbv zeta in FG. destruct FG as (MSL & AV & FR & LI & FB & SC & ML & _).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _).
split; [exact G0|]. split; [exact GC|]. split; [exact MSL|]. split; [exists b; reflexivity|]. split; [exact AV|]. split; [exact FR|].
pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. lia.
Qed.

#[using="RC__ LB MF MR"] Lemma rcoarse_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' : word) F fc (n sc : Z),
0 <= sc < 48 -> (sc < 32 -> 0 <= Z.lor sc 1 < 48) ->
evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce83c) fc None m1 (seg_rom rsegs)).
Proof.
intros until sc. intros SC48 SC1.
pose proof MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
unfold RNEED_LOCKS, RCTX, RMLOCK, RDEBRUIJN in *. unfold alloc_ceiling in *.

step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (actives st1) sc _ (wa (6566376 + 80 + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.

assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368) a0' a1' a2' a3' a4 a5 a6 a7
(pw st1 (active st sc')) (Z_to_bv 64 159528) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8e8) fc None m1 (seg_rom rsegs))).
{ intros a0' a1' a2' a3' sc' SC'.
destruct (active st sc') as [g|] eqn:ACT'.
- destruct (ractive_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW). unfold alloc_ceiling in GC.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & _).
change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM.
step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [subst gw; reflexivity| reflexivity].
- unfold pw. cbn [oconc].
step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368) a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159528) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8f4) fc None m1 (seg_rom rsegs))).
{ intros a0' a1' a2' a3' sc' ACT'. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159528) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8d4) fc None m1 (seg_rom rsegs))).
{ intros a1' a2' a3' s4' sc' SC'.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (actives st1) sc' _ (wa (6566376 + 80 + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
step. step. apply J40. exact SC'. }

step.
destruct (active st sc) as [g|] eqn:ACT.
-
destruct (ractive_ptr_facts sc g ACT) as (G0 & GC & _). unfold alloc_ceiling in GC.
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. exact SC48.
-
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
coarse_sc st sc = if b then
(let usage1 := usage st (Z.lor sc 1) in
let usage1 := match active st (Z.lor sc 1) with
| None => usage1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
end in
if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
{ intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }

step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
+
rewrite (CS false) by (subst sc; reflexivity).
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
+
step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), land_ones64 in K3 by lia.
*
rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
* assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.

step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
--
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). exact EV. }
step. step. apply J4c. exact ACT.
-- pose proof (proj1 (land_1_even sc) K4) as EV.

pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (usages st1) sc _ (wa (6566376 + 464 + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
step. pose proof (FU sc) as FUsc.
step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
**
assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.

step. rewrite (unsigned_lit sc) by lia. fold sc1.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (actives st1) sc1 _ (wa (6566376 + 80 + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
step.
pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (usages st1) sc1 _ (wa (6566376 + 464 + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
step. pose proof (FU sc1) as FU1.

set (u1 := match active st sc1 with
| None => usage st sc1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
assert (U1 : 0 <= u1 < 2^61).
{ unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
{ rewrite (CS true COND). reflexivity. }
clear CS.
assert (J20 : forall (a2' a3' : word),
evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6566368) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159528) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8c8) fc None m1 (seg_rom rsegs))).
{ intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
-
rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. exact SC1.
-
step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. exact SC48. }
change (Z_to_bv 64 0) with (wz 0).
destruct (active st sc1) as [g1|] eqn:ACT1.
+++
destruct (ractive_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1). unfold alloc_ceiling in G1C.
pose proof (rmeta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM1.
step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
cbn [default from_option id] in u1.

step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
***
assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NA). reflexivity. }
apply J20.
*** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.

step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NF). reflexivity. }
apply J20.
---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.

step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
2:{ unfold u1. rewrite K8, K9. reflexivity. }
apply J20.
+++
unfold pw. cbn [oconc].
step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by reflexivity.
apply J20.
**
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
step. step. apply J4c. exact ACT.
Qed.
End COARSE.
End RC__1.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_1 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mul_srliw27_sxv k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ k))) * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
gw (wz k) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce954) fc None m3 (seg_rom rsegs)
/\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
/\ munch [(G + 24, G + 28)]%Z m m3 /\ wmono rsegs m m3 /\ mem_inv rsegs m3
/\ rw_cells rsegs m3 (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)].

#[using="Type"] Lemma rfast_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw prev next memw : word) F fc m
(G avail k freed mword : Z),
bv_unsigned gw = G ->
rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
mem_inv rsegs m -> (G + 40 <= 0x10000 \/ 0x645000 <= G) ->
0 < avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= mword < 2^64 ->
0 <= k < 32 -> lowbit avail = 2 ^ k ->
evt rsegs (rfc_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v F fc m G avail k prev next memw freed mword)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv avail)) a1 a2 a3 a4 a5 a6 a7
gw (Z_to_bv 64 RDEBRUIJN) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8f8) fc None m (seg_rom rsegs)).
Proof.
intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
unfold RMLOCK, RDEBRUIJN in *.
assert (P2 : 0 < 2 ^ k <= avail).
{ destruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.

step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
rewrite (swrap_word (sxv avail - sxv (2 ^ k))).

step.
lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
[C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
[| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
end.

step.
apply evt_done. unfold rfc_post.
do 4 eexists.
lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
split; [reflexivity|].
split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.
End RC__2.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_2 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rcore0_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw : word) F fc (m : mem),
evt rsegs (fun ms' => exists a1', ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce930) fc None m (seg_rom rsegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8f8) fc None m (seg_rom rsegs)).
Proof.
intros.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))). rewrite (negw_and_lowbit 0) by lia. rewrite lowbit_0.
step. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. }
apply evt_done. eexists. reflexivity.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB HENF MF TP CLO LO N0 NT BL"] Lemma rfast_core_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word) (sc : Z) (g : aptr),
let mr := get_meta_rec st g in
let mask := m_avail mr in
let first := lowbit mask in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
active st sc = Some g -> 0 < mask -> n + 4 <= 16 * size_class sc ->
rimplT o (K (upd_meta g (m_set_avail (mask - first)) st1) (Some (g, ctz32 first))) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (wz (sxv mask)) a1 a2 a3 a4 a5 a6 a7
(pw st1 (Some g)) (Z_to_bv 64 RDEBRUIJN) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce8f8) fc None m1 (seg_rom rsegs)).
Proof.
intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & _). change (get_meta_rec st g) with mr in GSC.
pose proof (mf_gmeta _ _ MF) as FG0.
assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
{ change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
destruct (m_mem mr) as [b|] eqn:Hm.
- specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
destruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48. lia.
- exfalso. destruct (FA sc g ACT) as (_ & _ & NN). apply NN. exact Hm. }
destruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr).
destruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK). fold first in LBK.
assert (P2k : 0 < 2 ^ k <= mask).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE'). unfold first, lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
destruct (rfast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr).
fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. destruct FC as (CTR & SEC & INI & _).

assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)). unfold alloc_ceiling in GC.
set (G := conc st1 g) in *.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.

riprefixT.
eapply evt_mono.
{ eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
(m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
| |- _ => idtac end.
all: try lia. all: try assumption. }
intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
destruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM').

pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
replace (ctz32 first) with k by (rewrite LBK; symmetry; exact CTZ).
replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
change (pw st1 (Some g)) with (pw st2 (Some g)).
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
{ intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
eapply (HENF st2 g b r k m3 s errv).
-  rewrite E3. unfold st2. apply rmrep_meta_set_avail; [exact MR| exact MSL| lia].
- apply ticks_ok_upd_meta. exact TK.
- eapply unk_agree_munch; [| exact MU | |].
+ eapply unk_agree_ext; [exact UA| reflexivity| intros; reflexivity| reflexivity].
+ intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
+ intros rid r1 H1. exact (RB rid r1 H1).
- exact MI'.
- eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_munch_frame; [| exact MU| exact WM|].
+ eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_mono; [|exact Ha].
intros rid r1 H1. exists r1. repeat split; auto. lia.
+ intros x Hx NC. cbn. split; [|exact I].
intros HX. apply NC. left. right. right. right. exists rid0, r0. split; [exact Hr0|]. split; [exact Hk0|]. lia.
- intros a Ha. right. right. left. apply SPANFP.
replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [exact Ha|].
unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
- exact CTR.
- exact SO.
- intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
- apply mrel_same; reflexivity.
- exact BL.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.
End FASTCORE.

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="as_inv RAS HENF HFAIL MR0 TP CLO LO NT BL"] Lemma ras_call_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
as_pre st st1 sc n FUEL ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
0 <= sc < 48 ->
rimplT o (alloc_slot full_lay FUEL st1 sc n
(fun st2 idx => if idx <? 0 then K st2 None
else match active st2 sc with
| Some gp => K st2 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce930) fc None m1 (seg_rom rsegs)).
Proof.
intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO. pose proof (RAS_STACK_ge sc) as ASG. pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
subst tp. unfold RATP in *. rewrite unsigned_lit in ERR by lia.
unfold RMLOCK, RDEBRUIJN in *.
riprefixT.

step. rewrite sextw_small by lia. step. step.

step. apply evt_done.
eapply (RAS FUEL) with (st0 := st) (lo := lo).
all: lazymatch goal with
| |- as_pre _ _ _ _ _ => try exact PRE
| |- rmrep _ _ => try exact MR
| |- ticks_ok _ => try exact TK
| |- unk_agree _ _ _ => try exact UA
| |- brk_link_ps _ _ => try exact BL
| |- rauxv_ok _ _ => try (rewrite unsigned_lit by lia; eapply rauxv_ok_weaken; [exact AUX| unfold alloc_ceiling; lia])
| |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; exact ST)
| |- mem_inv _ _ => try assumption
| |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; exact ERR)
| |- _ => idtac
end.
all: try (rewrite ?unsigned_lit by lia; unfold alloc_ceiling; lia).
all: try reflexivity.

intros st2 idx s' ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES).
replace (ret_pc (Z_to_bv 64 0xce940)) with (Z_to_bv 64 0xce940) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.

pose proof (rframe_after_call (RC__:=RC__) st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:(unfold alloc_ceiling; lia)) as FR'.
assert (AUX2' : rauxv_ok m' (bv_unsigned sp)) by (eapply (rauxv_ok_malloc_fp st st2 lo _ m0 m' m1 m'); [exact MR0| exact MR'| exact AUX| exact PE'| unfold alloc_ceiling; lia| lia]).
assert (PE2 : rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m').
{ eapply rpres_except_trans; [| eapply rpres_except_mono; [exact PE'|]; intros a Ha; eapply rmalloc_fp_sp_mono; [|exact Ha]; lia].
eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_st_mono; [exact MREL|].
eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. repeat split; auto. lia. }
assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|exact MREL]; apply mrel_same; reflexivity).
pose proof MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _). unfold RCTX in CXA'. unfold RMLOCK in ML'.
clear MU WM PE AUX.
destruct RES as [[-> E12] | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
-
change (-1 <? 0) with true. cbv iota.
riprefixT.
step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
clear KB.
step. step.

step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact ML']. }
intros ms'' ->.
replace (ret_pc (Z_to_bv 64 0xce99c)) with (Z_to_bv 64 0xce99c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

step. step. step. step. step. step. step. step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. eapply (HFAIL st2 m' s' errv').
all: try assumption.
-
replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
riprefixT.
step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
clear KB.
step. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read rsegs mc _ (actives st2) sc (pw st2 (Some g)) (wa (6566376 + 80 + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.
apply evt_done.
change (Z_to_bv 64 idx) with (wz idx).
eapply (HENF st2 g b r idx m' s' errv').
all: try assumption.
+ intros a Ha. eapply rmalloc_fp_sp_mono; [|apply SPANFP; exact Ha]. lia.
+ intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. exact X.
Qed.
End ASCALL.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB as_inv RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL"] Lemma rmalloc_small_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
sc = size_to_class n -> 0 <= sc < 48 -> n + 4 <= 16 * size_class sc ->
(forall sc', 0 <= sc' < 48 -> n + 4 <= 16 * size_class sc' -> as_pre st st1 sc' n FUEL) ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_small_ctrl full_lay st1 n K bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xce83c) fc None m1 (seg_rom rsegs)).
Proof.
intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
pose proof (RAS_STACK_ge 0) as ASG. unfold st1 in *.
rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
pose proof (coarse_sc_cases st sc SC48) as CC.
assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
{ destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
set (sc' := coarse_sc st sc) in *.
change (active (set_tick t st) sc') with (active st sc').
riprefixT. eapply evt_cut.
{ eapply (rcoarse_walk st LB m1 t MF MR); [exact SC48| intros; apply lor1_range; lia]. }
fold sc'. intros ms' (a0' & a1' & a2' & a3' & -> & HA0).
change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
destruct (active st sc') as [g|] eqn:ACT'.
- cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
+
rewrite AZ, lowbit_0. cbn.
eapply evt_cut. { apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
+
apply evt_done.
destruct (ractive_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _).
destruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK).
assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
cbn [negb]. cbv iota.
change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
eapply rfast_core_implT; try eassumption; try lia.
- cbn iota. subst a0'.
eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
Qed.
End SMALL.

End RC__3.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb Q4vs QDUx.Mqb QPjm.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq1 Qv4L.Mq4 QdZ1.Mq2 QQbX.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs).

Definition rentry_cases (ms' : machine_state) : Prop :=

(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0xce300 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0xce0e4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xce1a8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xce13c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xce0b8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.

#[using="Type"] Lemma meta_word_sc52 mr : mw_ok mr ->
Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96) /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

#[using="i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].

#[using="EH"] Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> ntf_cond st g i = false ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce0dc) fc None m1 (seg_rom rsegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). unfold alloc_ceiling in *.
st1. rewrite ?(unsigned_lit (conc st g)) by lia.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
-
rpost_common MU WM MI ST FR MR m1 junk.
left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
-
assert (M0 : mask = 0) by (apply MZ; lia).
rpost_common MU WM MI ST FR MR m1 junk.
right; left. split; [exact HC|]. split; [exact M0|].
do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

#[using="EH"] Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce094) fc None m1 (seg_rom rsegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
unfold alloc_ceiling, RCTX in *.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
rmeta_chunk MR MSL CH.

st1. clear CH.
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
- destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
specialize (G50 HC ltac:(congruence)).

st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (6566376 + 80 + 8 * sc)) with (Z_to_bv 64 (6566376 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
+ pose proof (NINJ ltac:(lia)) as ->.
rpost_common MU WM MI ST FR MR m1 junk.
do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
+ assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
rpost_common MU WM MI ST FR MR m1 junk.
do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
- st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
rpost_common MU WM MI ST FR MR m1 junk.
do 2 right; left. split; [exact HC|]. split; [exact NX|].
do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

#[using="EH"] Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdfe4) fc None m1 (seg_rom rsegs)).
Proof.
intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).

st1. st1. st1.
st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
{
eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
assert (SC48 : sc < 48) by lia. clear K2.
assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
specialize (USG SC48).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (RS' : ov_read_bytes rsegs m1 (Z_to_bv 64 (159560 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (159560 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }

st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.

assert (K690 : forall (t0' : word),
m_maplen mr <> 0 ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 159560) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 6566376) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce038) fc None m1 (seg_rom rsegs))).
{ intros t0' MLNZ.
assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
assert (GSR : 0 < get_stride mr < 2^64).
{ unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }

st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
replace (159560 + sc * 2) with (159560 + 2 * sc) by lia.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
{ eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
assert (OKF : okay_to_free st g =
if negb (optr_eqb (m_next mr) (Some g)) then true
else if negb (is_bouncing sc st) then true
else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
{ rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }

rmeta_chunk MR MSL CH.
st1. clear CH.
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
{ assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
pose proof (NINJ ltac:(lia)) as Enx. subst nx.
rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc) by lia. st1.
st1. if_cases K7; zify_cond K7.
{ assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.

st1.
pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
pose proof (BND (sc - 7)) as BR.
replace (Z_to_bv 64 (6566376 + 880 + (sc - 7))) with (Z_to_bv 64 (6566376 + (sc + -7) + 880)) in RDB by (f_equal; lia).
st1. clear RDB. st1.
st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
{ replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
replace (wa (6566376 + 464 + 8 * sc)) with (Z_to_bv 64 (6566376 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.

st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
{ replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.

st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
- replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
- replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }

assert (K678 :
(m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt rsegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 159560) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 6566376) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xce020) fc None m1 (seg_rom rsegs))).
{ intros COND.
assert (STR : get_stride mr = 16 * size_class sc).
{ unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
- replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
apply K690. lia. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
{ apply K678. left. lia. }

st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
{ apply K678. right. lia. }

st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
apply K690. lia.
Qed.

#[using="EH MI0 LO LOLE"] Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st m -> stk rsegs m lo (bv_unsigned sp) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcdf80) fc None m (seg_rom rsegs)).
Proof.
intros until t6. intros MR ST.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR.
pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof rmaskw_range as MWR'.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & G6) & _).
unfold alloc_ceiling, RGOT_SSP, RSSP_GUARD in *. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.

st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR G4 G5.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
rmeta_chunk MR1 MSL CH.

st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
st1. rewrite (meta_word_freeable _ MW).
st1. rewrite (meta_word_sc52 _ MW).
clear CH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.

st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }

st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
st1. rewrite addiw_m1_word.

pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
- assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
-
apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.

End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkAv QvVw QNtS QXzy QFef Q4tl Q7ap Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QdBa QqdR QfYR QfcC Ql2m.
Import QnDM_c1 QDUx Q9Ay.
Import QkAv QvVw QNtS QXzy QFef QCwx Q4tl Q7ap QvBB.Mq2 Quzq.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Definition FMODL : Z := 0xdaa90.
Definition RFMODL_DEPTH : Z := 192.

Ltac lit_loads :=
repeat match goal with
| |- context [sx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in (bv_swrap 32 (c mod 2^64))%Z in
let c'' := eval vm_compute in (c' mod 2^64)%Z in
replace (sx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c'') by (unfold sx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
| |- context [zx32 (Z_to_bv 64 ?c)] =>
lazymatch isZcst c with true => idtac end;
let c' := eval vm_compute in ((c mod 2^64) mod 2^32)%Z in
replace (zx32 (Z_to_bv 64 c)) with (Z_to_bv 64 c') by (unfold zx32; apply Z_to_bv_eqm; vm_compute; reflexivity)
end.

Definition extsf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs)
/\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.

Lemma extendsftf2_2p120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv usegs m ->
evt usegs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) fc C_2P120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744071486570496) F) (Z_to_bv 64 0xcdfd0) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear -K1; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear -K2; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma extendsftf2_2pm120 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv usegs m ->
evt usegs (extsf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) fc C_2PM120 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 18446744069473304576) F) (Z_to_bv 64 0xcdfd0) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI.
zs. lit_loads. zs. zs. zs. zs. zs.
(if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]); try (exfalso; clear -K1; cbv in K1; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ | exfalso; lia ]); try (exfalso; clear -K2; cbv in K2; lia).
do 11 zs.
apply evt_done. unfold extsf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

Lemma m_fpclassifyl_canon : forall y, fpclassifyl (lo64 y + 2^64 * hi64 y) = m_fpclassifyl y.
Proof.
intros y. unfold fpclassifyl, m_fpclassifyl. change (lo64 y + 2^64 * hi64 y)%Z with (canon y).
rewrite lo64_canon, hi64_canon. unfold nz. reflexivity.
Qed.

Definition rfmodl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - RFMODL_DEPTH, q)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - RFMODL_DEPTH) q
/\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k).

Definition rfmodl_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X Y r : Z),
stk usegs m (q - RFMODL_DEPTH) q -> mem_inv usegs m ->
(4096 <= q - RFMODL_DEPTH)%Z -> (q < 2^63)%Z ->
m_fmodl X Y = Some r ->
evt usegs (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom usegs)).

Section Fmodl.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (X Y r : Z).
Hypothesis SPLO : (4096 <= q - RFMODL_DEPTH)%Z.
Hypothesis SPHI : (q < 2^63)%Z.
Hypothesis HM : m_fmodl X Y = Some r.

Notation POST := (rfmodl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Definition frame : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv usegs m /\ munch [(q - RFMODL_DEPTH, q)]%Z m0 m /\ wmono usegs m0 m
/\ rw_cells usegs m (q + -80) frame /\ stk usegs m (q - RFMODL_DEPTH) (q + -80).
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST); unfold frame in FR; unfold RFMODL_DEPTH in MU, ST.
Ltac mk_finv := unfold finv, frame, RFMODL_DEPTH; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|hyp].

Definition Fok (F' : bvmap 5 word) : Prop := forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. intros k _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set10 : forall F' v, Fok F' -> Fok (bvmap_set 10 v F').
Proof. intros F' v H k Hk. rewrite reg_get_set_other by (intros E; apply Hk; rewrite <- E; reflexivity). apply H. exact Hk. Qed.

Definition exv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x7fff.
Definition eyv : Z := Z.land (Z.shiftr (hi64 Y) 48) 0x7fff.
Definition sxv : Z := Z.land (Z.shiftr (hi64 X) 48) 0x8000.

#[using="Type"] Lemma L_ret : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdab0c) fc None m (seg_rom usegs)).
Proof.
intros until x1. intros FI FOK. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold rfmodl_post, RFMODL_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST | exact FOK].
Qed.

Definition DS : divtf3_stmt := QXzy.divtf3_spec.
#[using="Type"] Lemma stk_lower : forall m lo lo' hi, stk usegs m lo hi -> (lo <= lo' <= hi)%Z -> stk usegs m lo' hi.
Proof. intros m lo lo' hi ST H. exact (proj2 (stk_split _ _ _ _ _ ST H)). Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 192)%Z (q + -80)%Z |- _ =>
let ST1 := fresh "ST1" in let ST2 := fresh "ST2" in
destruct (stk_split _ _ _ (q + -80 - K)%Z _ ST ltac:(lia)) as [ST1 ST2]; clear ST;
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -80 - K)%Z (q + -80)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1 STn ltac:(lia)) as ST; clear ST1 STn end
end.

#[using="SPLO SPHI"] Lemma L_nan : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_div (f128_mul X Y) (f128_mul X Y) ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdaaec) fc None m (seg_rom usegs)).
Proof.
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. zs.
zs. call_split 112%Z (eapply (divtf3_callq DS); [hyp | hyp | lia]).
rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="SPLO SPHI"] Lemma L_zero : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' -> r = f128_mul (f128_of_i32 0) X ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdacb0) fc None m (seg_rom usegs)).
Proof.
intros until x1. intros FI FOK Hr. dest_finv FI. unfold RFMODL_DEPTH in SPLO.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite <- Hr. apply L_ret; [mk_finv | exact FOK].
Qed.

#[using="Type"] Lemma L_retx : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) F' x1 lo hi,
finv m -> Fok F' -> Z_to_bv 64 lo = Z_to_bv 64 (lo64 r) -> Z_to_bv 64 hi = Z_to_bv 64 (hi64 r) ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdad20) fc None m (seg_rom usegs)).
Proof.
intros until hi. intros FI FOK Hlo Hhi. pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
zs. zs. zs. rewrite Hlo, Hhi. apply L_ret; [exact FI | exact FOK].
Qed.

#[using="Type"] Lemma sxv_cases : sxv = 0%Z \/ sxv = 32768%Z.
Proof. unfold sxv. change 32768%Z with (2^15)%Z. rewrite land_pow2_bit by lia. destruct (Z.testbit _ _); [right|left]; reflexivity. Qed.
#[using="Type"] Lemma sext_field : forall e, Z.land (Z.lor (Z.land e 65535) sxv) 65535 = Z.land (Z.lor e sxv) 65535.
Proof.
intros e. rewrite !zb_land_lor_distr_l, <- Z.land_assoc, Z.land_diag. reflexivity.
Qed.
#[using="Type"] Lemma exv_range : (0 <= exv < 32768)%Z.
Proof. unfold exv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range X). lia. Qed.
#[using="Type"] Lemma eyv_range : (0 <= eyv < 32768)%Z.
Proof. unfold eyv. rewrite Z.land_comm. change 32768%Z with (2^15)%Z. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [cbn; lia|]. apply Z.shiftr_nonneg. pose proof (hi64_range Y). lia. Qed.
#[using="Type"] Lemma shr48X : Z.shiftr (hi64 X) 48 = (hi64 X / 2^48)%Z. Proof. apply Z.shiftr_div_pow2. lia. Qed.

#[using="Type"] Lemma land_M_16 : forall e, Z.land (Z.land e 18446744073709551615) 65535 = Z.land e 65535.
Proof. intros. rewrite <- Z.land_assoc. reflexivity. Qed.

#[using="Type"] Lemma pack_bridge : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 (Z.lor (Z.land xhi 281474976710655) (Z.land (Z.shiftl (Z.lor (Z.land E 65535) sxv) 48) 18446744073709551615))
= Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof.
intros xhi xlo E Hxlo. rewrite Z.lor_comm. rewrite (proj1 (pack_eq xhi xlo _ Hxlo)). rewrite sext_field. reflexivity.
Qed.
#[using="Type"] Lemma pack_bridge_lo : forall xhi xlo E, (0 <= xlo < 2^64)%Z ->
Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land (Z.lor E sxv) 65535) 48)) xlo)).
Proof. intros xhi xlo E Hxlo. exact (proj2 (pack_eq xhi xlo _ Hxlo)). Qed.

#[using="SPLO SPHI"] Lemma L_scale : forall m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 <= ex < 2^20)%Z ->
fmodl_scale sxv (xhi, xlo, ex) = r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdacf0) fc None m (seg_rom usegs)).
Proof.
intros until ex. intros FI FOK Rh Rl Re HS.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof sxv_cases as SX. unfold sxv in SX.
unfold fmodl_scale in HS.
zs. zs. zs. zs. zs. zs. brs K1.
-
replace (ex <=? 0) with true in HS by (symmetry; apply Z.leb_le; lia).
do 7 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo (ex + 120)) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
zs. zs. zs. callw (eapply extendsftf2_2pm120; hyp).
zs. zs. zs. zs. rewrite (pack_bridge_lo xhi xlo (ex + 120)) by lia.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
zs. rewrite HS. apply L_ret; [mk_finv | apply Fok_set10; exact FOK].
- replace (ex <=? 0) with false in HS by (symmetry; apply Z.leb_gt; lia).
do 6 zs. rewrite ?land_M_16. change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv. rewrite (pack_bridge xhi xlo ex) by lia.
rewrite (land_W64 xlo), (Z.mod_small xlo) by lia.
eapply L_retx; [exact FI | exact FOK | rewrite <- HS; apply pack_bridge_lo; lia | rewrite <- HS; reflexivity].
Qed.

#[using="SPLO SPHI"] Lemma L_L2 : forall (n : nat) m (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) st',
finv m -> Fok F' ->
(0 <= xhi < 2^48)%Z -> (0 <= xlo < 2^64)%Z -> (-2^20 + Z.of_nat n <= ex < 2^20)%Z ->
fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) = Some st' -> fmodl_scale sxv st' = r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) (Z_to_bv 64 32768) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdacd4) fc None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; intros until st'; intros FI FOK Rh Rl Re HL HS; [discriminate HL|].
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_norm_body in HL. rewrite fmodl_norm_loop_step in HL.
zs. zs. zs. zs. zs. zs. fixw. zs.

set (b := Z.shiftr xlo 63) in *. assert (Rb : (0 <= b <= 1)%Z) by (subst b; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E1 : Z.land (Z.shiftl xhi 1) 18446744073709551615 = (xhi * 2)%Z) by (rewrite land_W64, Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia).
rewrite !E1 in *.
assert (E2 : Z.lor (xhi * 2) b = (b + xhi * 2)%Z) by (rewrite Z.lor_comm; change (xhi * 2)%Z with (xhi * 2^1)%Z; apply lor_low_high; lia).
rewrite !E2 in *.
assert (E3 : u64 (2 * xhi + b) = (b + xhi * 2)%Z) by (unfold u64; rewrite Z.mod_small by lia; lia).
rewrite !E3 in HL.
assert (E4 : Z.shiftr (b + xhi * 2) 48 = Z.shiftr (xhi * 2) 48) by (rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
rewrite E4 in HL.
assert (R5 : (0 <= Z.shiftr (xhi * 2) 48 < 2^16)%Z) by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (E6 : Z.land (Z.shiftl xlo 1) 18446744073709551615 = u64 (2 * xlo)) by (unfold u64; rewrite land_W64, Z.shiftl_mul_pow2 by lia; f_equal; lia).
rewrite ?E6 in *. pose proof (Z.mod_pos_bound (2 * xlo) (2^64) ltac:(lia)) as R6. unfold u64 in *.
replace (Z_to_bv 64 (Z.shiftl xlo 1)) with (Z_to_bv 64 ((2 * xlo) mod 2^64)%Z) by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2, Z.mod_mod by lia; f_equal; lia).
replace (ex + -1)%Z with (ex - 1)%Z by lia.
(if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?Z.shiftr_div_pow2 in K2 by lia.
-
replace (Z.shiftr (xhi * 2) 48 =? 0) with true in HL by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
eapply (IH m); [exact FI | exact FOK | | | | exact HL | exact HS]; lia.
- replace (Z.shiftr (xhi * 2) 48 =? 0) with false in HL by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia).
injection HL as <-.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
Qed.

#[using="SPLO SPHI"] Lemma L_K2 : forall m (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K2 sxv (xhi, xlo, ex) = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xhi) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdacc8) fc None m (seg_rom usegs)).
Proof.
intros until ex. intros FI FOK Rh Rl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K2 in HK. change 130%nat with (S 129) in HK. rewrite fmodl_norm_loop_step in HK.
pose proof (shr48_range xhi Rh) as R48.
rewrite Z.shiftr_div_pow2 in R48 by lia.
zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)); rewrite ?Z.shiftr_div_pow2 in K1 by lia.
- replace (Z.shiftr xhi 48 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; rewrite Z.shiftr_div_pow2 by lia; lia). injection HK as HS.
eapply L_scale; [exact FI | exact FOK | lia | lia | lia | exact HS].
- replace (Z.shiftr xhi 48 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; rewrite Z.shiftr_div_pow2 by lia; lia).
destruct (fmodl_norm_loop 129 _) as [st'|] eqn:HL; [|discriminate HK]. injection HK as HS.
eapply L_L2; [exact FI | exact FOK | | exact Rl | | exact HL | exact HS].
+ Z.div_mod_to_equations. lia.
+ lia.
Qed.

#[using="SPLO SPHI"] Lemma L_fin : forall m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x24 x28 x29 x30 x31 : word) F' x1
(xhi xlo yhi ylo ex : Z),
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z -> (-2^19 <= ex < 2^19)%Z ->
fmodl_K1 X yhi ylo sxv (inl (xhi, xlo, ex)) = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdac90) fc None m (seg_rom usegs)).
Proof.
intros until ex. intros FI FOK Rxh Rxl Ryh Ryl Re HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
unfold fmodl_K1, fmodl_fin in HK.
destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4). cbv zeta in B1, B2, B3.
set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
zs. zs. zs. rewrite B2.
rewrite (shr63_eqb hi') in HK by lia.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (hi' <? 2^63) with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
- replace (hi' <? 2^63) with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. rewrite <- B4. pose proof (Z.mod_pos_bound (xlo - ylo) (2^64) ltac:(lia)) as Rlo. unfold u64 in HK, Rlo |- *.
assert (RL : (0 <= Z.lor hi' ((xlo - ylo) mod 2^64) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
change 18446744073709551616%Z with (2^64)%Z in *.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with false in HK by (symmetry; apply Z.eqb_neq; exact K2).
rewrite <- (Z_to_bv_mod64 (xlo - ylo)).
eapply L_K2; [exact FI | exact FOK | lia | lia | lia | exact HK].
+ replace (Z.lor hi' ((xlo - ylo) mod 2 ^ 64) =? 0) with true in HK by (symmetry; apply Z.eqb_eq; exact K2).
injection HK as Hr. zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
Qed.

#[using="Type"] Lemma dbl_bridge : forall h b, (0 <= h < 2^64)%Z -> (0 <= b <= 1)%Z ->
Z.lor (Z.land (Z.shiftl h 1) 18446744073709551615) b = u64 (2 * h + b).
Proof.
intros h b Hh Hb. rewrite land_W64, Z.shiftl_mul_pow2 by lia. unfold u64.
replace ((h * 2^1) mod 2^64)%Z with ((h mod 2^63) * 2^1)%Z by (Z.div_mod_to_equations; lia).
rewrite Z.lor_comm, lor_low_high by (try lia; Z.div_mod_to_equations; lia).
Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma shr63_b : forall l, (0 <= l < 2^64)%Z -> (0 <= Z.shiftr l 63 <= 1)%Z.
Proof. intros l Hl. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma u64_range : forall v, (0 <= u64 v < 2^64)%Z.
Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
#[using="Type"] Lemma zbv_shl1 : forall v, Z_to_bv 64 (Z.shiftl v 1) = Z_to_bv 64 (u64 (2 * v)).
Proof. intros. rewrite zbv_u64, Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

#[using="SPLO SPHI"] Lemma L_L1 : forall (yhi ylo ey : Z) (n : nat) m (x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31 : word) F' x1
(xhi xlo ex : Z) res,
finv m -> Fok F' ->
(0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
(-2^18 <= ey)%Z -> (ey < ex < 2^18)%Z ->
fmodl_sub_loop (S n) X yhi ylo ey (xhi, xlo, ex) = Some res -> fmodl_K1 X yhi ylo sxv res = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 yhi) (Z_to_bv 64 xhi) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ylo) (Z_to_bv 64 xlo) x20 x21 (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdac28) fc None m (seg_rom usegs)).
Proof.
intros yhi ylo ey. induction n as [|n IH]; intros until res; intros FI FOK Rxh Rxl Ryh Ryl Rey Rex HL HK.
all: pose proof FI as FI'; dest_finv FI'; unfold RFMODL_DEPTH in SPLO; pose proof (hi64_range X) as RHX.
all: rewrite fmodl_sub_loop_step in HL; replace (ey <? ex) with true in HL by (symmetry; apply Z.ltb_lt; lia).
all: unfold fmodl_sub_body in HL.
all: destruct (sbb_bridge xhi xlo yhi ylo Rxh Rxl Ryh Ryl) as (B1 & B2 & B3 & B4); cbv zeta in B1, B2, B3.
all: set (hi' := if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi)) in *.
all: rewrite (shr63_eqb hi') in HL by lia.
all: pose proof (shr63_b xlo Rxl) as Rb; pose proof (u64_range (xlo - ylo)) as Rlo; pose proof (shr63_b (u64 (xlo - ylo)) Rlo) as Rb2.
all: zs; zs; zs; rewrite B2; zs; (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).

- replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia). cbn [fmodl_sub_loop] in HL. discriminate HL.
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
cbn [fmodl_sub_loop] in HL. discriminate HL.
-
replace (hi' <? 2^63) with false in HL by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. rewrite (dbl_bridge xhi (Z.shiftr xlo 63)) by lia.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
- replace (hi' <? 2^63) with true in HL by (symmetry; apply Z.ltb_lt; lia).
zs. rewrite <- (Z_to_bv_mod64 (xlo - ylo)). change ((xlo - ylo) mod 2^64)%Z with (u64 (xlo - ylo)).
assert (RL : (0 <= Z.lor hi' (u64 (xlo - ylo)) < 2^64)%Z) by (apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; lia).
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); rewrite ?land_W64 in K2; rewrite ?(Z.mod_small (Z.lor _ _) (2^64)) in K2 by lia; change 18446744073709551616%Z with (2^64)%Z in K2.
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with true in HL by (symmetry; apply Z.eqb_eq; exact K2).
injection HL as <-. cbn [fmodl_K1] in HK. injection HK as Hr.
zs. eapply L_zero; [exact FI | exact FOK | symmetry; exact Hr].
+ replace (Z.lor hi' (u64 (xlo - ylo)) =? 0) with false in HL by (symmetry; apply Z.eqb_neq; exact K2).
zs. zs. zs. rewrite (dbl_bridge hi' (Z.shiftr (u64 (xlo - ylo)) 63)) by lia. zs.
zs. fixw. zs. rewrite zbv_shl1. zs. brs K3.
*
rewrite fmodl_sub_loop_step in HL. replace (ey <? ex - 1) with false in HL by (symmetry; apply Z.ltb_ge; lia).
injection HL as <-. zs. replace (ex - 1)%Z with ey in HK by lia.
eapply L_fin; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | exact HK].
* eapply IH; [exact FI | exact FOK | apply u64_range | apply u64_range | lia | lia | lia | lia | exact HL | exact HK].
Qed.

#[using="Type"] Lemma ex_field : forall v, (0 <= v < 2^16)%Z -> Z.shiftr (Z.land (Z.shiftl v 49) 18446744073709551615) 49 = Z.land v 32767.
Proof.
intros v Hv. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.land_spec, Z.land_spec by lia.
change 18446744073709551615%Z with (Z.ones 64). change 32767%Z with (Z.ones 15).
destruct (Z.lt_ge_cases i 15).
- rewrite Z.shiftl_spec, !Z.ones_spec_low by lia. rewrite !Bool.andb_true_r. f_equal. lia.
- rewrite (Z.ones_spec_high 64), (Z.ones_spec_high 15) by lia. now rewrite !Bool.andb_false_r.
Qed.
#[using="Type"] Lemma mant_or_range : forall h, (0 <= Z.lor (Z.land h 281474976710655) 281474976710656 < 2^64)%Z.
Proof.
intros h. pose proof (land48_range h) as R. change 0x0000ffffffffffff%Z with 281474976710655%Z in R.
change 281474976710656%Z with (1 * 2^48)%Z. rewrite lor_low_high by lia. lia.
Qed.

#[using="SPLO SPHI"] Lemma L_setup : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1
(uxh uxl uyh uyl ex ey : Z),
finv m -> Fok F' ->
(0 <= uxh < 2^64)%Z -> (0 <= uxl < 2^64)%Z -> (0 <= uyh < 2^64)%Z -> (0 <= uyl < 2^64)%Z ->
(-2^18 <= ey < 2^18)%Z -> (-2^18 <= ex < 2^18)%Z ->
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl ey
(Z.lor (Z.land uxh 0x0000ffffffffffff) (2^48), uxl, ex) with
| Some res => fmodl_K1 X (Z.lor (Z.land uyh 0x0000ffffffffffff) (2^48)) uyl sxv res
| None => None end = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 uyl) (Z_to_bv 64 uxl) (Z_to_bv 64 uyh) (Z_to_bv 64 uxh) (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 ey) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdabec) fc None m (seg_rom usegs)).
Proof.
intros until ey. intros FI FOK R1 R2 R3 R4 R5 R6 HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (mant_or_range uxh) as Q1. pose proof (mant_or_range uyh) as Q2.
change (2^48)%Z with 281474976710656%Z in HK. change 0x0000ffffffffffff%Z with 281474976710655%Z in HK.
do 7 zs. rewrite ?land_W64, ?(Z.mod_small (Z.lor _ _) (2^64)) by lia.
zs. brs K1.
-
destruct (fmodl_sub_loop _ _ _ _ _ _) as [res|] eqn:HL; [|discriminate HK].
eapply L_L1; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HL | exact HK].
- zs. rewrite fmodl_sub_loop_step in HK. replace (ey <? ex) with false in HK by (symmetry; apply Z.ltb_ge; lia).
eapply L_fin; [exact FI | exact FOK | lia | lia | lia | lia | lia | exact HK].
Qed.

Definition UX : Z := mk128 (Z.land (hi64 X) 0x7fffffffffffffff) (lo64 X).
Definition UY : Z := mk128 (Z.land (hi64 Y) 0x7fffffffffffffff) (lo64 Y).
#[using="Type"] Lemma UX_words : lo64 UX = lo64 X /\ hi64 UX = Z.land (hi64 X) 0x7fffffffffffffff.
Proof. unfold UX. pose proof (lo64_range X). pose proof (land63_range (hi64 X) (hi64_range X)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.
#[using="Type"] Lemma UY_words : lo64 UY = lo64 Y /\ hi64 UY = Z.land (hi64 Y) 0x7fffffffffffffff.
Proof. unfold UY. pose proof (lo64_range Y). pose proof (land63_range (hi64 Y) (hi64_range Y)). rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Definition K_normy (ux ex uy ey : Z) : option Z :=
(let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
match fmodl_sub_loop (S (Z.to_nat (ex - ey))) X yhi (lo64 uy) ey (xhi, lo64 ux, ex) with
| Some res => fmodl_K1 X yhi (lo64 uy) sxv res
| None => None end)%Z.

#[using="SPLO SPHI"] Lemma L_normy : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' x1 (ux ex : Z) (wl wh : word),
finv m -> Fok F' -> (-2^18 <= ex < 2^18)%Z ->
K_normy ux ex (f128_mul UY C_2P120) (Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120)%Z = Some r ->
wl = Z_to_bv 64 (lo64 ux) -> wh = Z_to_bv 64 (hi64 ux) ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 UY)) wl (Z_to_bv 64 (hi64 UY)) wh (Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 ex) (Z_to_bv 64 0) s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdabbc) fc None m (seg_rom usegs)).
Proof.
intros until wh. intros FI FOK Re HK -> ->.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO. pose proof (hi64_range X) as RHX.
pose proof (lo64_range UY) as R1. pose proof (hi64_range UY) as R2. pose proof (lo64_range ux) as R3. pose proof (hi64_range ux) as R4.
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
set (uy' := f128_mul UY C_2P120) in *. pose proof (lo64_range uy') as R5. pose proof (hi64_range uy') as R6.
pose proof (shr48_range (hi64 uy') R6) as R7.
zs. zs. zs. zs.
unfold K_normy in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | | lia | exact HK].
rewrite Z.shiftr_div_pow2 in R7 |- * by lia. lia.
Qed.

#[using="SPLO SPHI"] Lemma L_norm : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) F' x1,
finv m -> Fok F' ->
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey) = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 (Z.land (hi64 Y) 0x7fffffffffffffff)) (Z_to_bv 64 (Z.land (hi64 X) 0x7fffffffffffffff))
(Z_to_bv 64 (Z.shiftr (hi64 X) 48)) (Z_to_bv 64 exv) x24 s9 s10 s11 x28 x29 x30 x31)
F' (Z_to_bv 64 0xdaba8) fc None m (seg_rom usegs)).
Proof.
intros until x1. intros FI FOK HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof exv_range as REX. pose proof eyv_range as REY.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
zs. zs. rewrite (fpc_exp_field (hi64 Y)) by lia. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv.
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (exv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia).
zs. zs. zs. callw (eapply extendsftf2_2p120; hyp).
zs. zs. rewrite <- EUXl, <- EUXh. zs. zs.
zs. call_split 80%Z (eapply multf3_callq; [hyp | hyp | lia]).
rewrite EUXl.
set (ux' := f128_mul UX C_2P120) in *. pose proof (lo64_range ux') as R5. pose proof (hi64_range ux') as R6.
pose proof (shr48_range (hi64 ux') R6) as R7. rewrite Z.shiftr_div_pow2 in R7 by lia.
zs. zs. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+
replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUYl, EUYh in HK.
eapply L_setup; [mk_finv | apply Fok_set10; exact FOK | lia | lia | lia | lia | lia | | exact HK].
rewrite Z.shiftr_div_pow2 by lia. lia.
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [mk_finv | apply Fok_set10; exact FOK | | exact HK | reflexivity | reflexivity].
rewrite Z.shiftr_div_pow2 by lia. lia.
- replace (exv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (eyv =? 0) with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in HK. unfold K_normy in HK.
rewrite EUXl, EUXh, EUYl, EUYh in HK.
eapply L_setup; [exact FI | exact FOK | lia | lia | lia | lia | lia | lia | exact HK].
+ replace (eyv =? 0) with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
rewrite <- EUYl, <- EUYh, K2. eapply L_normy; [exact FI | exact FOK | lia | exact HK | rewrite EUXl; reflexivity | rewrite EUXh; reflexivity].
Qed.

Definition K_norm : option Z :=
(let '(ux, ex) := (if exv =? 0 then (f128_mul UX C_2P120, Z.shiftr (hi64 (f128_mul UX C_2P120)) 48 - 120) else (UX, exv))%Z in
let '(uy, ey) := (if eyv =? 0 then (f128_mul UY C_2P120, Z.shiftr (hi64 (f128_mul UY C_2P120)) 48 - 120) else (UY, eyv))%Z in
K_normy ux ex uy ey).
Definition K_cmp : option Z :=
if f128_le UX UY <=? 0 then (if f128_le UX UY =? 0 then Some (f128_mul (f128_of_i32 0) X) else Some X) else K_norm.

#[using="SPLO SPHI"] Lemma L_cmp : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) x1,
finv m ->
(if exv =? 32767 then Some (f128_div (f128_mul X Y) (f128_mul X Y)) else K_cmp) = Some r ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 X)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xdab4c) fc None m (seg_rom usegs)).
Proof.
intros until x1. intros FI HK.
pose proof FI as FI'. dest_finv FI'. unfold RFMODL_DEPTH in SPLO.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof (shr48_range (hi64 X) RHX) as R48.
pose proof (land63_range (hi64 X) RHX) as R63X. pose proof (land63_range (hi64 Y) RHY) as R63Y.
destruct UX_words as [EUXl EUXh]. destruct UY_words as [EUYl EUYh].
pose proof exv_range as REX.
zs. zs. zs. zs. try rewrite (ex_field (Z.shiftr (hi64 X) 48)) by lia. change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv.
zs. fixw. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
- replace (exv =? 32767) with true in HK by (symmetry; apply Z.eqb_eq; lia). injection HK as Hr.
eapply L_nan; [exact FI | apply Fok_refl | symmetry; exact Hr].
- replace (exv =? 32767) with false in HK by (symmetry; apply Z.eqb_neq; lia). unfold K_cmp in HK.
pose proof (f128_le_range UX UY) as RLE.
zs. zs. zs. zs. zs. zs. zs. zs.
rewrite <- EUXl, <- EUXh, <- EUYl, <- EUYh.
zs. callw (eapply letf2_callv; hyp).
zs. brs K2.
+ replace (f128_le UX UY <=? 0) with false in HK by (symmetry; apply Z.leb_gt; lia).
rewrite EUXl, EUXh, EUYl, EUYh. eapply L_norm; [mk_finv | apply Fok_refl | exact HK].
+ replace (f128_le UX UY <=? 0) with true in HK by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K3; zify_cond K3; try (rewrite ?signed_of_Z in K3 by lia)).
* replace (f128_le UX UY =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K3 RLE; mlia2). injection HK as Hr.
rewrite EUXl. replace (Z_to_bv 64 (f128_le UX UY)) with (Z_to_bv 64 0) by (f_equal; clear -K3 RLE; mlia2).
eapply L_zero; [mk_finv | apply Fok_refl | symmetry; exact Hr].
* replace (f128_le UX UY =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K3 RLE; mlia2). injection HK as Hr.
zs. rewrite EUXl. eapply L_retx; [mk_finv | apply Fok_refl | rewrite Hr; reflexivity | rewrite Hr; reflexivity].
Qed.

#[using="SPLO SPHI HM"] Lemma L_entry : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
stk usegs m0 (q - RFMODL_DEPTH) q -> mem_inv usegs m0 ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m0 (seg_rom usegs)).
Proof.
intros until t6. intros ST MI.
pose proof (munch_refl [(q - RFMODL_DEPTH, q)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
unfold RFMODL_DEPTH in ST, MU, SPLO. unfold FMODL.
pose proof (hi64_range X) as RHX. pose proof (lo64_range X) as RLX. pose proof (hi64_range Y) as RHY. pose proof (lo64_range Y) as RLY.
pose proof HM as HK. rewrite m_fmodl_split in HK. cbv zeta in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32767) with exv in HK. change (Z.land (Z.shiftr (hi64 Y) 48) 32767) with eyv in HK.
change (Z.land (Z.shiftr (hi64 X) 48) 32768) with sxv in HK.
fold UX UY in HK.
zs. carve_frame 80%nat ST.
do 15 zs.
zs. callw (eapply floatsitf_callv with (v := 0%Z) (i := 0%Z); [hyp | lia | reflexivity]).
set (t00 := f128_of_i32 0) in *. pose proof (lo64_range t00) as RT1. pose proof (hi64_range t00) as RT2.
pose proof (f128_le_range Y t00) as RLE.
zs. zs. zs. zs. zs. callw (eapply letf2_callv; hyp).
zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia)).
-
replace (f128_le Y t00 =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K1 RLE; mlia2). cbn [orb] in HK.
zs. zs. zs. callw (eapply fpclassifyl_spec; eassumption). norm_rsegs.
rewrite !ulit_lo64, !ulit_hi64, m_fpclassifyl_canon.
assert (RC : (0 <= m_fpclassifyl Y <= 4)%Z) by (unfold m_fpclassifyl; repeat (destruct (_ : bool)); lia).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ replace (m_fpclassifyl Y =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K2 RC; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
+ replace (m_fpclassifyl Y =? 0) with false in HK by (symmetry; apply Z.eqb_neq; clear -K2 RC; mlia2). cbn [orb] in HK.
eapply L_cmp; [mk_finv | exact HK].
- replace (f128_le Y t00 =? 0) with true in HK by (symmetry; apply Z.eqb_eq; clear -K1 RLE; mlia2). cbn [orb] in HK. injection HK as Hr.
eapply L_nan; [mk_finv | apply Fok_refl | symmetry; exact Hr].
Qed.
End Fmodl.

Lemma rfmodl_spec : rfmodl_stmt.
Proof.
unfold rfmodl_stmt. intros. eapply L_entry; eassumption.
Qed.

End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QeTw Q1BE QvBB.Mq2.
Export QnkH.Mqd.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. intros. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
pose proof (f_equal bv_unsigned E) as E2. rewrite !Qy5Y.unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells usegs m A [CB 1 bs] -> exists b, rw_cells usegs m A [CB 1 [b]].
Proof.
intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells usegs m A cs -> rw_cells usegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells usegs m A (CB 0 [] :: cs) -> rw_cells usegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ bytes_at usegs m' A buf.
Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
bytes_at usegs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv usegs m ->
evt usegs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdd914) fc None m (seg_rom usegs)).
Proof.
intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply Q1BE.memchr_spec with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
intros ms' P. unfold Q1BE.memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at usegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv usegs m ->
evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply QeTw.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold QeTw.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - 64) (q)
/\ rw_cells usegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
/\ rw_cells usegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
/\ bytes_at usegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
rw_cells usegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at usegs m T (zbytes txt) -> rw_cells usegs m D [CB 1 [dj]] ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk usegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 STRING_READ) fc None m (seg_rom usegs)).

End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 QDUx.Mq2 Q9Ay.Mq9 QXxF.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.

Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 QnOf QdZ1.Mq7 QQbX.Mq5 QdZ1.Mq5 Qv4L.Mqc QnkH.Mqe QnkH.Mqf.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b60) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (rid : N) (off : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
(Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0b48) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b24) fc None m (seg_rom usegs)).
Proof.
intros until off. intros MR CNT BRK C0 C1b.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

#[using="Type"] Lemma ram_brk0_node :
impl usegs (at_node usegs) (enode (NBrk 0) dec_brk0)
(epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0xd0b64) fc None m (seg_rom usegs) /\ 0 <= r < 2^64))
(MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0xd0b60) fc None m (seg_rom usegs)).
Proof.
unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0xd0b60 + 4)%Z with 0xd0b64%Z by reflexivity.
apply evt_done. split; [reflexivity| exact Hr].
Qed.

#[using="Type"] Lemma ram_brk_node_at (pc : Z) :
(pc = 0xd0b48 \/ pc = 0xd0b84) -> forall cur req, req <> 0 ->
impl usegs (at_node usegs) (enode (NBrk req) (dec_brk cur req))
(epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom usegs)))
(MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
Proof.
intros Hpc cur req NZ. unfold rbrk_regs.
destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
[ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
| rewrite apply_mem_none ];
apply evt_done; reflexivity).
Qed.
End BRKNODES.

#[using="Type"] Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
(m : word -> option byte) (cur : Z),
0 < cur < 2^64 -> cur mod 4096 = 0 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists a2' m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0b84) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b64) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros CR CAL TC MI.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (land_neg_aligned cur CR CAL) as AL.
assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
change (cur mod 4096 = 0) with (pgal cur) in CAL.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in TC. change (6576296 + 920) with 6577216 in MU. change (6576296 + 928) with 6577224 in MU.

st1. st1. rewrite ?AL, ?AL'. st1. st1.
replace (0 + cur) with cur by lia.

st1. st1. st1. st1.
replace (8192 + cur) with (cur + 8192) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

#[using="Type"] Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
(m : word -> option byte) (cur : Z),
0 < cur -> cur + 8192 < 2^64 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xd0ba8) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
(Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b88) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros C0 C1b TC.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in TC.

st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

#[using="Type"] Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0c34) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ba8) fc None m (seg_rom usegs)).
Proof.
intros until nw. intros NW HC TC MI.
pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in TC.
change (6576296 + 40) with 6576336 in MU. change (6576296 + 48) with 6576344 in MU. change (6576296 + 920) with 6577216 in MU. change (6576296 + 928) with 6577224 in MU.

st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

#[using="Type"] Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells usegs m RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0c34) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' RCTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells usegs m' (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b4c) fc None m (seg_rom usegs)).
Proof.
intros until nw. intros NW HC TC MI.

st1. rewrite bv_eqb_refl. cbv iota.
eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

#[using="Type"] Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bbc) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
lazymatch type of C1 with rw_cells _ _ _ ?cs =>
assert (C1' : rw_cells usegs m RCTX cs)
by (eapply Q98Z.Mq5.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
clear C1.
pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
unfold RCTX, RMLOCK, RSSP_GUARD in *. change (6576296 + 912) with 6577208 in TC.
change (6576296 + 920) with 6577216 in MU, MU0. change (6576296 + 928) with 6577224 in MU, MU0.

st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
{ eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
- unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
- first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (6576296 + 912) with 6577208.
replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with H : rw_cells usegs ?mX 6577208 _ |- _ => exact H end. }
apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

#[using="Type"] Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
F fc (m : word -> option byte) (st : mstate) (old : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b4c) fc None m (seg_rom usegs)).
Proof.
intros until old. intros MR CNT O0 O1 MI.
pose proof MR as (WF & (_ & _ & _ & _ & _ & C6 & _) & _). unfold ctx_tail_cells in C6.

st1.
assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl usegs m) CNT C6 eq_refl eq_refl MI).
Qed.

#[using="Type"] Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
rmrep st m0 -> munch [(RCTX + 920, RCTX + 928)]%Z m0 m -> wmono usegs m0 m ->
c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
rw_cells usegs m (RCTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0bd4) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 920, RCTX + 928)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0b88) fc None m (seg_rom usegs)).
Proof.
intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.

st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
{ apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
rewrite CF; clear CF.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QdZ1 QQbX Qv4L.Mqi Qv4L.Mqb Qv4L QnkH.Mqi.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rcoarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
(pw st (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fbc) fc None m (seg_rom usegs)
/\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR : rmrep st1 m1.
Hypothesis MI : mem_inv usegs m1.

#[using="LB m1 MF MR"] Lemma ractive_ptr_facts sc g : active st sc = Some g -> 0 < conc st1 g /\ conc st1 g + 40 <= alloc_ceiling /\ meta_slot st1 g
/\ (exists b, m_mem (get_meta_rec st g) = Some b)
/\ 0 <= m_avail (get_meta_rec st g) < 2^32 /\ 0 <= m_freed (get_meta_rec st g) < 2^32
/\ 0 <= m_last_idx (get_meta_rec st g) + 32 * m_freeable (get_meta_rec st g) + 64 * m_sizeclass (get_meta_rec st g) + 4096 * m_maplen (get_meta_rec st g) < 2^64.
Proof.
intros ACT.
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & NN).
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hm). cbv zeta in FG. destruct FG as (MSL & AV & FR & LI & FB & SC & ML & _).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _).
split; [exact G0|]. split; [exact GC|]. split; [exact MSL|]. split; [exists b; reflexivity|]. split; [exact AV|]. split; [exact FR|].
pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. lia.
Qed.

#[using="RC__ LB MF MR"] Lemma rcoarse_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' : word) F fc (n sc : Z),
0 <= sc < 48 -> (sc < 32 -> 0 <= Z.lor sc 1 < 48) ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0f00) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros SC48 SC1.
pose proof MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
unfold RNEED_LOCKS, RCTX, RMLOCK, RDEBRUIJN in *. unfold alloc_ceiling in *.

step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc _ (wa (6576296 + 80 + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.

assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288) a0' a1' a2' a3' a4 a5 a6 a7
(pw st1 (active st sc')) (Z_to_bv 64 159624) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fac) fc None m1 (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc' SC'.
destruct (active st sc') as [g|] eqn:ACT'.
- destruct (ractive_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW). unfold alloc_ceiling in GC.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & _).
change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM.
step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [subst gw; reflexivity| reflexivity].
- unfold pw. cbn [oconc].
step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288) a0' a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159624) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fb8) fc None m1 (seg_rom usegs))).
{ intros a0' a1' a2' a3' sc' ACT'. step.
apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. do 4 eexists. split; [reflexivity| reflexivity]. }

assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159624) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0f98) fc None m1 (seg_rom usegs))).
{ intros a1' a2' a3' s4' sc' SC'.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc' _ (wa (6576296 + 80 + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
step. step. apply J40. exact SC'. }

step.
destruct (active st sc) as [g|] eqn:ACT.
-
destruct (ractive_ptr_facts sc g ACT) as (G0 & GC & _). unfold alloc_ceiling in GC.
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. exact SC48.
-
unfold pw. cbn [oconc].
if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
clear K1.
assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
coarse_sc st sc = if b then
(let usage1 := usage st (Z.lor sc 1) in
let usage1 := match active st (Z.lor sc 1) with
| None => usage1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
end in
if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
{ intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }

step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
+
rewrite (CS false) by (subst sc; reflexivity).
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
+
step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), land_ones64 in K3 by lia.
*
rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
* assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.

step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
--
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). exact EV. }
step. step. apply J4c. exact ACT.
-- pose proof (proj1 (land_1_even sc) K4) as EV.

pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (usages st1) sc _ (wa (6576296 + 464 + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
step. pose proof (FU sc) as FUsc.
step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
**
assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.

step. rewrite (unsigned_lit sc) by lia. fold sc1.
step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st1) sc1 _ (wa (6576296 + 80 + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
step.
pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (usages st1) sc1 _ (wa (6576296 + 464 + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
step. pose proof (FU sc1) as FU1.

set (u1 := match active st sc1 with
| None => usage st sc1 + 3
| Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
assert (U1 : 0 <= u1 < 2^61).
{ unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
{ rewrite (CS true COND). reflexivity. }
clear CS.
assert (J20 : forall (a2' a3' : word),
evt usegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 6576288) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 159624) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0f8c) fc None m1 (seg_rom usegs))).
{ intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
-
rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. exact SC1.
-
step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. exact SC48. }
change (Z_to_bv 64 0) with (wz 0).
destruct (active st sc1) as [g1|] eqn:ACT1.
+++
destruct (ractive_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1). unfold alloc_ceiling in G1C.
pose proof (rmeta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM1.
step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
cbn [default from_option id] in u1.

step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
***
assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NA). reflexivity. }
apply J20.
*** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.

step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
replace (wz (usage st sc1)) with (wz u1).
2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NF). reflexivity. }
apply J20.
---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.

step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
2:{ unfold u1. rewrite K8, K9. reflexivity. }
apply J20.
+++
unfold pw. cbn [oconc].
step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
step. rewrite (wz_unsigned (usage st sc1)) by lia.
replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by reflexivity.
apply J20.
**
rewrite (CS false).
2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
step. step. apply J4c. exact ACT.
Qed.
End COARSE.
End RC__1.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_1 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mul_srliw27_sxv k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ k))) * rDB32)))) 27) = rdbi k.
Proof.
intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m3,
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
gw (wz k) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1018) fc None m3 (seg_rom usegs)
/\ m3 = write_to_mem m (wa (G + 24)) (le4 (wz (avail - 2 ^ k)))
/\ munch [(G + 24, G + 28)]%Z m m3 /\ wmono usegs m m3 /\ mem_inv usegs m3
/\ rw_cells usegs m3 (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)].

#[using="Type"] Lemma rfast_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw prev next memw : word) F fc m
(G avail k freed mword : Z),
bv_unsigned gw = G ->
rw_cells usegs m (bv_unsigned gw) [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
mem_inv usegs m -> (G + 40 <= 0x10000 \/ 0x647000 <= G) ->
0 < avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= mword < 2^64 ->
0 <= k < 32 -> lowbit avail = 2 ^ k ->
evt usegs (rfc_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v F fc m G avail k prev next memw freed mword)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv avail)) a1 a2 a3 a4 a5 a6 a7
gw (Z_to_bv 64 RDEBRUIJN) s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fbc) fc None m (seg_rom usegs)).
Proof.
intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
unfold RMLOCK, RDEBRUIJN in *.
assert (P2 : 0 < 2 ^ k <= avail).
{ destruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.

step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv usegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
rewrite (swrap_word (sxv avail - sxv (2 ^ k))).

step.
lazymatch goal with H : rw_cells usegs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
apply (rw_cells_congr usegs mc (bv_unsigned gw) cs
[C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
[| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
end.

step.
apply evt_done. unfold rfc_post.
do 4 eexists.
lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
split; [reflexivity|].
split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.
End RC__2.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_2 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rcore0_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw : word) F fc (m : mem),
evt usegs (fun ms' => exists a1', ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1' a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ff4) fc None m (seg_rom usegs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz (sxv 0)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fbc) fc None m (seg_rom usegs)).
Proof.
intros.
step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))). rewrite (negw_and_lowbit 0) by lia. rewrite lowbit_0.
step. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. }
apply evt_done. eexists. reflexivity.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB HENF MF TP CLO LO N0 NT BL"] Lemma rfast_core_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word) (sc : Z) (g : aptr),
let mr := get_meta_rec st g in
let mask := m_avail mr in
let first := lowbit mask in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
active st sc = Some g -> 0 < mask -> n + 4 <= 16 * size_class sc ->
rimplT o (K (upd_meta g (m_set_avail (mask - first)) st1) (Some (g, ctz32 first))) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (wz (sxv mask)) a1 a2 a3 a4 a5 a6 a7
(pw st1 (Some g)) (Z_to_bv 64 RDEBRUIJN) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0fbc) fc None m1 (seg_rom usegs)).
Proof.
intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
destruct (FA sc g ACT) as (SC48 & GSC & _). change (get_meta_rec st g) with mr in GSC.
pose proof (mf_gmeta _ _ MF) as FG0.
assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
{ change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
destruct (m_mem mr) as [b|] eqn:Hm.
- specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
destruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48. lia.
- exfalso. destruct (FA sc g ACT) as (_ & _ & NN). apply NN. exact Hm. }
destruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr).
destruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK). fold first in LBK.
assert (P2k : 0 < 2 ^ k <= mask).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE'). unfold first, lowbit in LBK.
rewrite LBK in E'. rewrite E'. exact LE'. }
destruct (rfast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr).
fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. destruct FC as (CTR & SEC & INI & _).

assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)). unfold alloc_ceiling in GC.
set (G := conc st1 g) in *.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.

riprefixT.
eapply evt_mono.
{ eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
(m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
| |- mem_inv _ _ => exact MI
| |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
| |- _ => idtac end.
all: try lia. all: try assumption. }
intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
destruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM').

pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
replace (ctz32 first) with k by (rewrite LBK; symmetry; exact CTZ).
replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
change (pw st1 (Some g)) with (pw st2 (Some g)).
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
{ intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
eapply (HENF st2 g b r k m3 s errv).
-  rewrite E3. unfold st2. apply rmrep_meta_set_avail; [exact MR| exact MSL| lia].
- apply ticks_ok_upd_meta. exact TK.
- eapply unk_agree_munch; [| exact MU | |].
+ eapply unk_agree_ext; [exact UA| reflexivity| intros; reflexivity| reflexivity].
+ intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
+ intros rid r1 H1. exact (RB rid r1 H1).
- exact MI'.
- eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
- eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_munch_frame; [| exact MU| exact WM|].
+ eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_mono; [|exact Ha].
intros rid r1 H1. exists r1. repeat split; auto. lia.
+ intros x Hx NC. cbn. split; [|exact I].
intros HX. apply NC. left. right. right. right. exists rid0, r0. split; [exact Hr0|]. split; [exact Hk0|]. lia.
- intros a Ha. right. right. left. apply SPANFP.
replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [exact Ha|].
unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
- exact CTR.
- exact SO.
- intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
- apply mrel_same; reflexivity.
- exact BL.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.
End FASTCORE.

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="as_inv RAS HENF HFAIL MR0 TP CLO LO NT BL"] Lemma ras_call_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
as_pre st st1 sc n FUEL ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
0 <= sc < 48 ->
rimplT o (alloc_slot full_lay FUEL st1 sc n
(fun st2 idx => if idx <? 0 then K st2 None
else match active st2 sc with
| Some gp => K st2 (Some (gp, idx))
| None => SVis (EUndef UBadPtr) (fun _ => bail)
end) bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0ff4) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO. pose proof (RAS_STACK_ge sc) as ASG. pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
subst tp. unfold RATP in *. rewrite unsigned_lit in ERR by lia.
unfold RMLOCK, RDEBRUIJN in *.
riprefixT.

step. rewrite sextw_small by lia. step. step.

step. apply evt_done.
eapply (RAS FUEL) with (st0 := st) (lo := lo).
all: lazymatch goal with
| |- as_pre _ _ _ _ _ => try exact PRE
| |- rmrep _ _ => try exact MR
| |- ticks_ok _ => try exact TK
| |- unk_agree _ _ _ => try exact UA
| |- brk_link_ps _ _ => try exact BL
| |- rauxv_ok _ _ => try (rewrite unsigned_lit by lia; eapply rauxv_ok_weaken; [exact AUX| unfold alloc_ceiling; lia])
| |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; exact ST)
| |- mem_inv _ _ => try assumption
| |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; exact ERR)
| |- _ => idtac
end.
all: try (rewrite ?unsigned_lit by lia; unfold alloc_ceiling; lia).
all: try reflexivity.

intros st2 idx s' ms' PO.
destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES).
replace (ret_pc (Z_to_bv 64 0xd1004)) with (Z_to_bv 64 0xd1004) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.

pose proof (rframe_after_call (RC__:=RC__) st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:(unfold alloc_ceiling; lia)) as FR'.
assert (AUX2' : rauxv_ok m' (bv_unsigned sp)) by (eapply (rauxv_ok_malloc_fp st st2 lo _ m0 m' m1 m'); [exact MR0| exact MR'| exact AUX| exact PE'| unfold alloc_ceiling; lia| lia]).
assert (PE2 : rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m').
{ eapply rpres_except_trans; [| eapply rpres_except_mono; [exact PE'|]; intros a Ha; eapply rmalloc_fp_sp_mono; [|exact Ha]; lia].
eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_st_mono; [exact MREL|].
eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. repeat split; auto. lia. }
assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|exact MREL]; apply mrel_same; reflexivity).
pose proof MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _). unfold RCTX in CXA'. unfold RMLOCK in ML'.
clear MU WM PE AUX.
destruct RES as [[-> E12] | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
-
change (-1 <? 0) with true. cbv iota.
riprefixT.
step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
clear KB.
step. step.

step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact ML']. }
intros ms'' ->.
replace (ret_pc (Z_to_bv 64 0xd1060)) with (Z_to_bv 64 0xd1060) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

step. step. step. step. step. step. step. step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. eapply (HFAIL st2 m' s' errv').
all: try assumption.
-
replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
riprefixT.
step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
clear KB.
step. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_read usegs mc _ (actives st2) sc (pw st2 (Some g)) (wa (6576296 + 80 + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
step.
apply evt_done.
change (Z_to_bv 64 idx) with (wz idx).
eapply (HENF st2 g b r idx m' s' errv').
all: try assumption.
+ intros a Ha. eapply rmalloc_fp_sp_mono; [|apply SPANFP; exact Ha]. lia.
+ intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. exact X.
Qed.
End ASCALL.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> QUZl.M R) (bail : QUZl.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB as_inv RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL"] Lemma rmalloc_small_implT :
forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
sc = size_to_class n -> 0 <= sc < 48 -> n + 4 <= 16 * size_class sc ->
(forall sc', 0 <= sc' < 48 -> n + 4 <= 16 * size_class sc' -> as_pre st st1 sc' n FUEL) ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
stk usegs m1 lo (bv_unsigned sp + -48) ->
rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_small_ctrl full_lay st1 n K bail) s Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd0f00) fc None m1 (seg_rom usegs)).
Proof.
intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
pose proof (RAS_STACK_ge 0) as ASG. unfold st1 in *.
rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
pose proof (coarse_sc_cases st sc SC48) as CC.
assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
{ destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
set (sc' := coarse_sc st sc) in *.
change (active (set_tick t st) sc') with (active st sc').
riprefixT. eapply evt_cut.
{ eapply (rcoarse_walk st LB m1 t MF MR); [exact SC48| intros; apply lor1_range; lia]. }
fold sc'. intros ms' (a0' & a1' & a2' & a3' & -> & HA0).
change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
destruct (active st sc') as [g|] eqn:ACT'.
- cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
+
rewrite AZ, lowbit_0. cbn.
eapply evt_cut. { apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
+
apply evt_done.
destruct (ractive_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _).
destruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK).
assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
cbn [negb]. cbv iota.
change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
eapply rfast_core_implT; try eassumption; try lia.
- cbn iota. subst a0'.
eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply rcore0_walk. }
intros ms'' (a1'' & ->). apply evt_done.
eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
Qed.
End SMALL.

End RC__3.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb Q4vs QDUx.Mqb QPjm.Mq3.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq3 Qv4L.Mqf QdZ1.Mq7 QQbX.Mq6.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs).

Definition rentry_cases (ms' : machine_state) : Prop :=

(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0xd09c4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0xd07a8 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xd086c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xd0800 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0xd077c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -96)
/\ rw_cells usegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.

#[using="Type"] Lemma meta_word_sc52 mr : mw_ok mr ->
Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv usegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -96) /\ rw_cells usegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

#[using="i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].

#[using="EH"] Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> ntf_cond st g i = false ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd07a0) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). unfold alloc_ceiling in *.
st1. rewrite ?(unsigned_lit (conc st g)) by lia.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
-
rpost_common MU WM MI ST FR MR m1 junk.
left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
-
assert (M0 : mask = 0) by (apply MZ; lia).
rpost_common MU WM MI ST FR MR m1 junk.
right; left. split; [exact HC|]. split; [exact M0|].
do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

#[using="EH"] Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0758) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
unfold alloc_ceiling, RCTX in *.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
rmeta_chunk MR MSL CH.

st1. clear CH.
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
- destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
specialize (G50 HC ltac:(congruence)).

st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (6576296 + 80 + 8 * sc)) with (Z_to_bv 64 (6576296 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
+ pose proof (NINJ ltac:(lia)) as ->.
rpost_common MU WM MI ST FR MR m1 junk.
do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
+ assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
rpost_common MU WM MI ST FR MR m1 junk.
do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
- st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
rpost_common MU WM MI ST FR MR m1 junk.
do 2 right; left. split; [exact HC|]. split; [exact NX|].
do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

#[using="EH"] Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd06a8) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).

st1. st1. st1.
st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
{
eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
assert (SC48 : sc < 48) by lia. clear K2.
assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
specialize (USG SC48).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (RS' : ov_read_bytes usegs m1 (Z_to_bv 64 (159656 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (159656 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }

st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.

assert (K690 : forall (t0' : word),
m_maplen mr <> 0 ->
evt usegs POST
(MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 159656) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 6576296) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd06fc) fc None m1 (seg_rom usegs))).
{ intros t0' MLNZ.
assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
assert (GSR : 0 < get_stride mr < 2^64).
{ unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }

st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
replace (159656 + sc * 2) with (159656 + 2 * sc) by lia.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
{ eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
assert (OKF : okay_to_free st g =
if negb (optr_eqb (m_next mr) (Some g)) then true
else if negb (is_bouncing sc st) then true
else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
{ rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }

rmeta_chunk MR MSL CH.
st1. clear CH.
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
{ assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
pose proof (NINJ ltac:(lia)) as Enx. subst nx.
rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc) by lia. st1.
st1. if_cases K7; zify_cond K7.
{ assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.

st1.
pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
pose proof (BND (sc - 7)) as BR.
replace (Z_to_bv 64 (6576296 + 880 + (sc - 7))) with (Z_to_bv 64 (6576296 + (sc + -7) + 880)) in RDB by (f_equal; lia).
st1. clear RDB. st1.
st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
{ replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.

st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
replace (wa (6576296 + 464 + 8 * sc)) with (Z_to_bv 64 (6576296 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.

st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
{ replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.

st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
- replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
- replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }

assert (K678 :
(m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 159656) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 6576296) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd06e4) fc None m1 (seg_rom usegs))).
{ intros COND.
assert (STR : get_stride mr = 16 * size_class sc).
{ unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
- replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
apply K690. lia. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
{ apply K678. left. lia. }

st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
{ apply K678. right. lia. }

st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
apply K690. lia.
Qed.

#[using="EH MI0 LO LOLE"] Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st m -> stk usegs m lo (bv_unsigned sp) ->
evt usegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0644) fc None m (seg_rom usegs)).
Proof.
intros until t6. intros MR ST.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR.
pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof rmaskw_range as MWR'.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & G6) & _).
unfold alloc_ceiling, RGOT_SSP, RSSP_GUARD in *. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.

st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR G4 G5.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
rmeta_chunk MR1 MSL CH.

st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
st1. rewrite (meta_word_freeable _ MW).
st1. rewrite (meta_word_sc52 _ MW).
clear CH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.

st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }

st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
st1. rewrite addiw_m1_word.

pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
- assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
-
apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.

End RC__1.
End Mqa.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q8P7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QBeb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation RAMpre := (@AMpre_g ref_reserved rc_secret).
Notation ram_pre := (am_pre_g ref_reserved rc_secret).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

#[using="AMP"] Lemma rAMpre_init : RAMpre (am_init_st st).
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
- rewrite A3. exact rc_secret_range.
- right; reflexivity.
- destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

#[using="Type"] Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
#[using="Type"] Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof. unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

#[using="RC__ AMP"] Lemma rAMI_init : AMI st (am_init_st st).
Proof.
unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
(split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| intros rid r Hr; exists r; repeat split; auto; lia
| intros rid r' H1 H2; cbn in H1; congruence
| cbn; lia
| intros P _ HP; exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
| intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
| exact (amp_rpos st AMP) ]).
- cbn. rewrite (amp_s_secret st AMP). exact rc_secret_range.
- exact (amp_secret st AMP).
Qed.

#[using="Type"] Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E6.
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.

#[using="Type"] Lemma ram_rel_final stX st1 mo :
AMI st stX ->
c_active (ctx st1) = c_active (ctx stX) -> c_usage (ctx st1) = c_usage (ctx stX) -> c_unmap_seq (ctx st1) = c_unmap_seq (ctx stX) ->
c_bounces (ctx st1) = c_bounces (ctx stX) -> c_seq (ctx st1) = c_seq (ctx stX) -> c_mmap_counter (ctx st1) = c_mmap_counter (ctx stX) ->
s_groups st1 = s_groups stX -> s_slots st1 = s_slots stX -> s_shadow st1 = s_shadow stX -> s_tick st1 = s_tick stX ->
s_reserved st1 = s_reserved stX -> s_regions st1 = s_regions stX -> s_next_rid st1 = s_next_rid stX ->
(forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas st1) !! a)) ->
(forall g, Some g <> mo -> (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) -> get_meta_rec st1 g = get_meta_rec stX g) ->
(forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m) ->
(forall P : N -> Prop, (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P stX -> ptrs_in P st1) ->
am_rel st st1 mo.
Proof.
intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split.
- intros sc. unfold active. rewrite E1, C7. reflexivity.
- intros sc. unfold usage. rewrite E2, C8. reflexivity.
- intros i. unfold bounces. rewrite E4, C10. reflexivity.
- intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
- rewrite E5, C11. reflexivity.
- rewrite E6, C1. reflexivity.
- rewrite EG, XG. reflexivity.
- rewrite ESl, XS. reflexivity.
- rewrite ESh, XSH. reflexivity.
- rewrite ET, XT. reflexivity.
- rewrite ERs, XR. reflexivity.
- intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
- exact HR.
- intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
- intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
- rewrite EN. exact XNX.
- intros a Ha. apply HA. rewrite XA. exact Ha.
- intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
- intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.

#[using="Type"] Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof.
intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
- intros m Hm. discriminate.
Qed.

#[using="Type"] Lemma ram_rel_take stX q :
AMI st stX -> c_avail_meta (ctx st) = Some q -> (s_metas st) !! q = None -> meta_slot st q ->
am_rel st (am_took stX q (c_avail_meta_count (ctx stX) - 1)) (Some q).
Proof.
intros AI AVM MQ MSq. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
unfold am_took. rewrite upd_meta_put.
eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
- intros a Ha. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
+ apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
- intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta.
+ cbn. exact I.
+ cbn. exact I.
+ unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
+ pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
try assumption; try reflexivity.
cbn. rewrite C3, AVM in H2. exact H2.
Qed.

#[using="Type"] Lemma ram_rel_carve stX p r :
AMI st stX -> (s_regions stX) !! (fst p) = Some r -> r_kind r <> RKGroup ->
(s_areas stX) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas stX) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
(forall tl, c_meta_area_tail (ctx stX) = Some tl -> is_Some ((s_areas stX) !! tl)) ->
am_rel st (am_took (carve_st stX p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
{ replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }

assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
/\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
/\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
/\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
/\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
/\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
/\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
{ destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
- destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
+ intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct H0 as (H1 & _). exact H1.
* destruct H0 as (_ & H2 & _). exact H2.
* destruct H0 as (_ & _ & H3 & _). exact H3.
* exact HP.
* exact HP.
* destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
{ apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
split; [exact Q8|]. split; [| exact Q10].
intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
- rewrite (carve_st_none stX p HT ANone). cbv zeta.
eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
+ intros a Ha. exact Ha.
+ intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
rewrite EC. unfold am_took. rewrite upd_meta_put.
set (stD := set_areas _ stC).
eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
- intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
- intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
- intros m Hm. inversion Hm; subst m. split.
+ rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
+ apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
- intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
+ unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
+ apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
* destruct (RP P HPp HP0) as (H1 & _). exact H1.
* exact HPp.
* destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
* destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
* destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
* pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
split; [exact H8|]. split; [| exact H10].
intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
-- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
-- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

#[using="Type"] Lemma ram_rel_deq stI h nx pv :
AMI st stI ->
c_free_meta_head (ctx st) = Some h -> c_free_meta_head (ctx stI) = Some h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv -> (nx = h <-> pv = h) ->
meta_slot st h -> clr_links (get_meta_rec st h) = meta0 ->
m_mem (get_meta_rec st nx) = None -> m_next (get_meta_rec st nx) <> None ->
m_mem (get_meta_rec st pv) = None -> m_next (get_meta_rec st pv) <> None ->
am_rel st (dequeue LFree h stI) (Some h).
Proof.
intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
destruct (aptr_eqb nx h) eqn:E.
-
apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
* change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
* pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
-
assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
{ change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
rewrite !get_meta_rec_put_other by congruence. apply GM. }
eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
+ intros a Ha; exact Ha.
+ intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
rewrite !get_meta_rec_put_other by assumption. reflexivity.
+ intros m Hm. inversion Hm; subst m. split.
* rewrite get_meta_rec_put_same, R3. exact CL.
* apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
+ intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
assert (P1 : ptrs_in P st1).
{ unfold st1. apply QWTl.Mq5.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
- destruct (H8 pv) as (X & _ & _). exact X.
- destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P2 : ptrs_in P st2).
{ unfold st2. apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
- unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
destruct (H8 pv) as (_ & _ & X). exact X. }
assert (P3 : ptrs_in P st3).
{ unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
apply rptrs_in_upd_ctx; cbn; try reflexivity.
- exact Q2.
- change (ctx st2) with (ctx stI). exact H2.
- change (ctx st2) with (ctx stI). exact H3.
- change (ctx st2) with (ctx stI). exact H4.
- change (ctx st2) with (ctx stI). exact H5.
- change (ctx st2) with (ctx stI). exact H7.
- exact P2. }
apply QWTl.Mq5.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
rewrite R3. rewrite <- GM. exact Q3.
Qed.

#[using="Type"] Lemma rAMI_ctx stX f :
AMI st stX ->
ctx_core_eq (ctx stX) (f (ctx stX)) -> 0 <= c_secret (f (ctx stX)) < 2^64 ->
(c_avail_meta_areas (f (ctx stX)) = c_avail_meta_areas (ctx stX)
\/ exists q r, c_avail_meta_areas (f (ctx stX)) = Some q /\ (s_regions stX) !! (fst q) = Some r /\ r_kind r <> RKGroup) ->
(c_brk (f (ctx stX)) = c_brk (ctx stX)
\/ c_brk (f (ctx stX)) = BrkDead
\/ exists rid off r, c_brk (f (ctx stX)) = BrkLive rid off /\ (s_regions stX) !! rid = Some r /\ r_kind r <> RKGroup) ->
AMI st (upd_ctx f stX).
Proof.
intros AI CE SR HA HB. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
split; cbn; try assumption.
- destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
- intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
+ destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
+ destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
+ exact (XP P HPn HP0).
Qed.

#[using="Type"] Lemma rAMI_new_region stX k base len :
AMI st stX -> k <> RKGroup -> 0 < len ->
AMI st (fst (new_region k base len stX))
/\ (s_regions (fst (new_region k base len stX))) !! (s_next_rid stX) = Some (mkRegion k base len)
/\ (forall q, fst q <> s_next_rid stX -> conc (fst (new_region k base len stX)) q = conc stX q)
/\ (forall off, conc (fst (new_region k base len stX)) (s_next_rid stX, off) = base + off).
Proof.
intros AI NK LEN. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
unfold new_region. cbn [fst].
set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
split; [| split; [| split]].
- split; cbn -[insert]; try assumption.
+ intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
+ intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
+ unfold rid. lia.
+ intros P HPn HP0. apply (QWTl.Mq5.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
+ intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
+ intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
- rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
- intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
- intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

#[using="Type"] Lemma rAMI_grow stX rid r off :
AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof.
intros AI Hr NK LEN st'. pose proof AI as AI'.
destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
{ intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
assert (CQ : forall q, conc st' q = conc stX q).
{ intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
split; cbn -[insert]; try assumption.
- intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
destruct (decide (q = rid)) as [->|NE].
+ rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
intros HG. exfalso. apply NK. rewrite K'. exact HG.
+ exists r'. auto.
- intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
- intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
destruct (decide (q = rid)) as [->|NE].
+ apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
+ apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
- intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
+ destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
+ apply XF. exact Hq.
- intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.

End RC__1.
