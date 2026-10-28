(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Qfw3 Q5Rg Qc3B UEQM QCcH Qsw7 QJjn QRUw QBGG Uh14 UmtA QoBT Q7T7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac TopFdp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes Qfw3.Mq2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import UEQM.
Import QCcH Qsw7 QJjn QRUw.
Import QBGG.
Import Uh14 UmtA QoBT Q7T7.
Import TopUbTac TopFdp.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac litn := fold_closed_in_goal.

Ltac freg H :=
lazymatch type of H with Sem.reg_get ?F ?k = ?v =>
match goal with |- context [Sem.reg_get F ?k'] =>
replace (Sem.reg_get F k') with v by (symmetry; exact H) end
end.
Ltac solve_fsaved :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; cbn [FSAVED In] in Hk;
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk];
repeat (first [ rewrite freg_get_other by (vm_compute; reflexivity)
| rewrite freg_get_same by (vm_compute; reflexivity) ]);
reflexivity.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones_low; [lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. Qed.

Lemma cfp_stop : forall ptr n, 0 <= n < 2^64 - 8 -> 0 <= ptr ->
Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 n) (Z_to_bv 64 (n + -7))) + -1)))
(bv_unsigned (Z_to_bv 64 (n + -7))) + ptr + -2)
= Z_to_bv 64 (ptr + Z.max (n - 7) 0 - 2).
Proof.
intros ptr n Hn Hp. destruct (Z.lt_ge_cases n 7) as [LT|GE].
- rewrite v_sltu_1'.
2:{ rewrite (unsigned_lit n) by lia. unfold_consts_goal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
replace (n + -7) with ((n + -7 + 2^64) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
rewrite (unsigned_lit 1) by lia. change (1 + -1) with 0. rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l.
f_equal. lia.
- rewrite v_sltu_0' by (rewrite (unsigned_lit n), (unsigned_lit (n + -7)) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
rewrite (unsigned_lit (n + -7)) by lia. rewrite land_ones64_l by lia. f_equal. lia.
Qed.

Lemma neq_wz : forall x y, 0 <= x < 2^64 -> -2^64 <= y < 2^64 -> x <> y -> x <> y + 2^64 ->
bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy N1 N2. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
destruct (Z.lt_ge_cases y 0).
- replace y with ((y + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma eq_wz : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_neq :=
lazymatch goal with |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
rewrite (neq_wz x y) by lia; cbn [negb]; cbv beta iota end.
Ltac if_eq :=
lazymatch goal with |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
rewrite (eq_wz x y) by lia; cbn [negb]; cbv beta iota end.

Section CfpJoP.
Definition cfp_pb1 := Eval vm_compute in match image_bytes rsegs 0x133b0 8 with Some bs => bs | None => [] end.
Definition cfp_pb2 := Eval vm_compute in match image_bytes rsegs 0x13418 8 with Some bs => bs | None => [] end.
Definition cfp_pb3 := Eval vm_compute in match image_bytes rsegs 0x133b8 8 with Some bs => bs | None => [] end.
#[using="Type"] Lemma cfp_ro_P : forall m, mem_inv rsegs m ->
ro_cells rsegs m 0x133b0 [CB 8 cfp_pb1] /\ ro_cells rsegs m 0x13418 [CB 8 cfp_pb2] /\ ro_cells rsegs m 0x133b8 [CB 8 cfp_pb3].
Proof.
intros m MI. split; [|split].
- change 8%nat with (length cfp_pb1). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb1)) with 8%Z. lia.
- change 8%nat with (length cfp_pb2). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb2)) with 8%Z. lia.
- change 8%nat with (length cfp_pb3). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ]. change (Z.of_nat (length cfp_pb3)) with 8%Z. lia.
Qed.

Ltac runf_to stop F10 F11 := do 80 (try (try freg F10; try freg F11; lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => ub_closed c; ub_if_lit
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?k) _ _ _ _) => ub_closed k;
tryif (let v := eval vm_compute in (k =? stop) in constr_eq v true) then fail else bstep end)).

Ltac cfp_u64_call P ptr rem lo data USP :=
lazymatch goal with H : bytes_at rsegs ?mx ptr data |- _ => let B1 := fresh "B1" in
pose proof H as B1; rewrite <- (firstn_skipn (Z.to_nat (Z.max (rem - 1) 0)) data) in B1; apply bytes_at_app in B1 as [B1 _] end;
fold_mkR;
let C64 := fresh "C64" in pose proof cii_u64_U_spec as C64; unfold cii_stmt in C64;
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) => eapply evt_cut; [eapply C64 with (P := P) (ptr := ptr) (rem := Z.max (rem - 1) 0) (lo := lo) (data := firstn (Z.to_nat (Z.max (rem - 1) 0)) data) | unfold fdp_post, fdp_W; rewrite USP; post_call segs mm] end;
[ unfold Uh14.fdp_pre; rewrite USP; do 9 (split; [first [reflexivity | assumption | (rewrite length_firstn; lia) | lia] |]); assumption
| first [rewrite unsigned_lit by lia; reflexivity | vm_compute; reflexivity]
| first [rewrite unsigned_lit by lia; reflexivity | vm_compute; reflexivity]
| idtac ].

#[using="Type"] Lemma cfp_P : cfp_stmt rsegs CFP_P CFP_STK_P IHI_P.
Proof.
unfold cfp_stmt, CFP_P, CFP_STK_P, IHI_P, fdp_preS. intros until data. intros (A0 & FDP & SRC & LEN & Hptr & ST & LO & HP & HD & MI) IHI F10 F11 FRM. subst a0.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (munch_refl (fdp_WS 64 (bv_unsigned sp) P) m) as MU. unfold fdp_WS in MU.
pose proof (wmono_refl rsegs m) as WM.
destruct (cfp_ro_P m MI) as (RO1 & RO2 & RO3).
carve_frame 48%nat ST.
runf_to 0x2161c F10 F11.
pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
pose proof cii_u8_U_spec as C8. unfold cii_stmt in C8.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) => eapply evt_cut; [eapply C8 with (P := P) (ptr := ptr) (rem := rem) (lo := lo) (data := data) | unfold fdp_post, fdp_W; rewrite USP; post_call segs mm] end.
1: unfold Uh14.fdp_pre; rewrite USP; do 9 (split; [first [reflexivity | assumption | lia] |]); assumption.
1,2: rewrite unsigned_lit by lia; reflexivity.
runf_to 0x217d0 F10 F11.
match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end;
runf_to 0x217d0 F10 F11; cfp_u64_call P ptr rem lo data USP; runf_to 0 F10 F11;
lazymatch goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -48) _, H' : stk rsegs ?mx lo _ |- _ => release_frame H H' (bv_unsigned sp) end;
assert (EQ9 : Z.max (Z.max (rem - 1) 0 - 8) 0 = Z.max (rem - 9) 0) by (clear; lia); rewrite EQ9 in *;
finish; try lia; try solve_fsaved.
Qed.
End CfpJoP.
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QfLs Q0Ek Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import UEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi Qsw7 QJjn QRUw.
Import UC8c.Mq0.
Import QBGG.
Import TopUbTac TopFdp.
Import ListNotations. Local Ltac QlEo.exec_pre i ::= QlEo.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Lemma payload_byte0 : forall m sb payload co c,
bytes_at rsegs m sb payload -> nth_error payload (Z.to_nat co) = Some c -> 0 <= co ->
ov_read_bytes rsegs m (Z_to_bv 64 (sb + co)) 1 = Some [c].
Proof.
intros m sb payload co c B Hn Hco.
pose proof (nth_error_Some_length Hn) as L.
pose proof (bytes_at_read rsegs m sb payload co 1 B Hco ltac:(lia)) as R.
replace (firstn 1 (skipn (Z.to_nat co) payload)) with [c] in R; [exact R|].
pose proof (@nth_error_split _ payload (Z.to_nat co) c Hn) as (l1 & l2 & E & Hl1). rewrite E at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Section FdpInlJo.

Definition fdp_at (spf : Z) (m : word -> option byte) (ptr rem : Z) (data : list byte) : Prop :=
rw_cells rsegs m (spf + 32) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] /\
bytes_at rsegs m ptr data /\ Z.of_nat (length data) = rem /\ 0 <= ptr /\ ptr + rem < 2^63.

#[using="Type"] Lemma fdp_last_byte : forall m ptr rem data,
bytes_at rsegs m ptr data -> Z.of_nat (length data) = rem -> 0 < rem ->
exists c, nth_error data (Z.to_nat (rem - 1)) = Some c /\ ov_read_bytes rsegs m (Z_to_bv 64 (ptr + (rem - 1))) 1 = Some [c].
Proof.
intros m ptr rem data B L Hr.
destruct (nth_error data (Z.to_nat (rem - 1))) as [c|] eqn:E.
- exists c. split; [reflexivity|]. eapply payload_byte0; [exact B | exact E | lia].
- exfalso. apply nth_error_None in E. lia.
Qed.

#[using="Type"] Lemma fdp_shrink : forall m m' spf ptr cur cur' data,
fdp_at spf m ptr cur data -> 0 <= cur' <= cur ->
rw_cells rsegs m' (spf + 32) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 cur')] ->
bytes_at rsegs m' ptr data ->
fdp_at spf m' ptr cur' (firstn (Z.to_nat cur') data).
Proof.
intros m m' spf ptr cur cur' data (FR & B & L & P0 & P1) Hc FR' B'.
split; [exact FR'|].
pose proof B' as B1. rewrite <- (firstn_skipn (Z.to_nat cur') data) in B1. apply bytes_at_app in B1 as [B1 _].
split; [exact B1|]. split; [rewrite length_firstn; lia | lia].
Qed.

#[using="Type"] Lemma fdp_firstn_min : forall spf m ptr c1 c2 data,
fdp_at spf m ptr c1 (firstn (Z.to_nat c1) (firstn (Z.to_nat c2) data)) -> c1 <= c2 ->
fdp_at spf m ptr c1 (firstn (Z.to_nat c1) data).
Proof.
intros spf m ptr c1 c2 data FD Hc. rewrite firstn_firstn in FD.
replace (Nat.min (Z.to_nat c1) (Z.to_nat c2)) with (Z.to_nat c1) in FD by lia. exact FD.
Qed.

#[using="Type"] Lemma cbool_P : forall (x1 gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spf ptr rem : Z) (data : list byte) (Q : machine_state -> Prop),
fdp_at spf m ptr rem data -> 0 < ptr -> ptr + rem <= spf -> mem_inv rsegs m -> 0 <= spf -> spf + 64 < 2^63 ->
(forall m' (rem' : Z) (a0' a1' a2' a3' : word),
fdp_at spf m' ptr rem' (firstn (Z.to_nat rem') data) -> rem' = Z.max (rem - 1) 0 -> bv_unsigned a1' <= 1 ->
munch [(spf + 40, spf + 48)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
evt rsegs Q (MS (mkR x1 (wz spf) gp (wz 0x77c00) t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x211ec) fc None m' (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR x1 (wz spf) gp (wz 0x77c00) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x211b4) fc None m (seg_rom rsegs)).
Proof.
intros until Q. intros FD Hptr DJ MI SP0 SP1 K.
pose proof FD as (FR & B & L & P0 & P1).
pose proof (munch_refl [(spf + 40, spf + 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
bstep. bstep.
destruct (Z.eq_dec rem 0) as [-> | NZ].
- if_truex.
eapply (K m 0); [ | lia | rewrite unsigned_lit by lia; lia | exact MU | exact WM | exact MI].
rewrite Z2Nat.inj_0, firstn_O. split; [exact FR|]. split; [| split; [reflexivity | lia]].
destruct B as (B0 & B1 & _). split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn in Hi. lia.
- if_falsex. bstep. step. if_falsex.
destruct (fdp_last_byte _ ptr rem data B L ltac:(lia)) as (c & Hc & RDC).
replace (ptr + (rem - 1)) with (ptr + (rem + -1)) in RDC by lia.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
bstep. bstep. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (K mc (rem - 1)); [ | lia | | exact MU | exact WM | exact MI] end.
+ eapply fdp_shrink; [exact FD | lia | | exact B]. replace (rem - 1) with (rem + -1) by lia. exact FR.
+ assert (HL : 0 <= Z.land (bv_unsigned (zxb c)) 1 <= 1).
{ split; [apply Z.land_nonneg; right; lia|]. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound (bv_unsigned (zxb c)) (2^1)). lia. }
rewrite unsigned_lit by lia. lia.
Qed.
End FdpInlJo.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh14. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxXT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxXT.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Import ListNotations. Local Ltac QlEo.exec_pre i ::= QlEo.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac runto stop := do 120 (try (lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => ub_closed c; ub_if_lit
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?k) _ _ _ _) => ub_closed k;
tryif (let v := eval vm_compute in (k =? stop) in constr_eq v true) then fail else bstep end)).
Ltac bst := ub_skip; repeat (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_falsex; ub_skip end); step.

Section Cells.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_pair : forall m A x y,
rw_cells segs m A [C1 x] -> rw_cells segs m (A + 1) [C1 y] -> rw_cells segs m A [C1 x; C1 y].
Proof. intros m A x y H1 H2. apply (proj2 (rw_cells_app segs m A [C1 x] [C1 y])). split; [exact H1 | exact H2]. Qed.

#[using="Type"] Lemma rw_cells_unpair : forall m A x y,
rw_cells segs m A [C1 x; C1 y] -> rw_cells segs m A [C1 x] /\ rw_cells segs m (A + 1) [C1 y].
Proof. intros m A x y H. apply (proj1 (rw_cells_app segs m A [C1 x] [C1 y])) in H. exact H. Qed.

#[using="Type"] Lemma rw_cells_CB_snoc : forall m A n s b,
rw_cells segs m A [CB n s] -> rw_cells segs m (A + Z.of_nat n) [C1 b] -> rw_cells segs m A [CB (S n) (s ++ [b])].
Proof.
intros m A n s b H1 H2.
assert (L : length s = n) by (destruct H1 as [[[Hwf _] _] _]; exact Hwf).
assert (H : rw_cells segs m A ([CB n s] ++ [C1 b])).
{ apply (proj2 (rw_cells_app segs m A [CB n s] [C1 b])). cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact H1 | exact H2]. }
eapply rw_cells_recast; [exact H | cbn; rewrite length_app; cbn; lia | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

#[using="Type"] Lemma rw_cells_CB_head : forall m A n b bs,
rw_cells segs m A [CB (S n) (b :: bs)] -> rw_cells segs m A [C1 b] /\ rw_cells segs m (A + 1) [CB n bs].
Proof.
intros m A n b bs H.
destruct (rw_cells_CB_cut segs m A (S n) (b :: bs) 1 H ltac:(lia)) as [H1 H2].
cbn [firstn skipn] in H1, H2. change (Z.of_nat 1) with 1 in H2. replace (S n - 1)%nat with n in H2 by lia.
split; [| exact H2].
eapply rw_cells_recast; [exact H1 | cbn; split; exact I | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma obj_join : forall m S n (szb j : byte) s rest,
0 <= n <= 21 -> bv_unsigned szb = 2 * n ->
rw_cells segs m S [C1 szb] ->
rw_cells segs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells segs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells segs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells segs m S [C1 (Z_to_bv 8 (2 * n)); CB 23 (s ++ b0 :: j :: rest)].
Proof.
intros m S n szb j s rest Hn Hsz SZ DATA WIN REST.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
pose proof (rw_cells_bound segs _ _ _ REST) as B. cbn [cells_size csize Nat.add] in B.
assert (H : rw_cells segs m S ([C1 szb] ++ ([CB (Z.to_nat n) s] ++ ([C1 b0; C1 j] ++ [CB (Z.to_nat (21 - n)) rest])))).
{ apply (proj2 (rw_cells_app segs m S _ _)). split; [exact SZ|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact DATA|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. replace (S + 1 + n) with (S + n + 1) by lia.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact WIN|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 2) with 2.
replace (S + n + 1 + 2) with (S + n + 3) by lia. exact REST. }
eapply rw_cells_recast; [exact H | | |].
- cbn [cells_wf cell_wf csize length]. rewrite length_app. cbn [length].
repeat split; try exact I; try reflexivity. lia.
- cbn. rewrite <- app_assoc. cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2 ^ 8).
pose proof (bv_unsigned_in_range 8 szb) as R. unfold bv_modulus in R. cbn in R. rewrite Z.mod_small; lia.
- cbn. lia.
Qed.
End Cells.

Lemma first_nul_split : forall (pre post : list byte),
exists str rest, pre ++ b0 :: post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ b0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ b0 :: post) = b0 :: (pre ++ b0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ b0 :: post) = b :: (str ++ b0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

Lemma lor7_eq23 : forall n, 16 <= n <= 23 -> Z.lor n 7 = 23.
Proof.
intros n Hn.
assert (H : forallb (fun k => Z.lor (16 + Z.of_nat k) 7 =? 23) (seq 0 8) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat (n - 16)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq in H. replace (16 + (n - 16)) with n in H by lia. exact H.
Qed.
Lemma lor7_bound : forall n, 0 <= n <= 15 -> 7 <= Z.lor n 7 <= 15.
Proof.
intros n Hn.
assert (H : forallb (fun k => andb (7 <=? Z.lor (Z.of_nat k) 7) (Z.lor (Z.of_nat k) 7 <=? 15)) (seq 0 16) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat n) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Tactic Notation "call_pushb" constr(Sv) constr(nv) constr(lov) constr(szbv) constr(xv) constr(yv) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) => name_sp sp k
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => name_sp sp k
end;
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply pushb_spec with (S := Sv) (n := nv) (lo := lov) (szb := szbv) (x := xv) (y := yv)
| unfold pushb_post, pushb_W; post_call segs mm] end;
unname_sp.

Section CrlsP.
Notation FRAME := 128 (only parsing).

#[using="Type"] Lemma crls_done :
forall (sp ra s0 s1 s2 s3 s4 s5 : word)
(x1 gp tp t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
(S P ptr rem lo maxlen n k : Z) (szb j : byte) (s rest data j8 : list byte),
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - FRAME ->
bv_unsigned szb = 2 * n -> 0 <= n <= maxlen -> maxlen <= 20 ->
rw_cells rsegs m S [C1 szb] ->
rw_cells rsegs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells rsegs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells rsegs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k <= rem ->
rw_cells rsegs m P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
bytes_at rsegs m ptr data ->
munch (crls_W FRAME (bv_unsigned sp) S P) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
bv_unsigned sp <= S ->
evt rsegs (crls_post rsegs FRAME maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 S) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21394) fc None m (seg_rom rsegs)).
Proof.
intros until j8. intros FR ST LO Hsz Hn Hmax SZ DATA WIN REST Hk FDP SRC MU WM MI HS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
unfold crls_W in MU.
step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite land1_even.
step. if_true.
step. rewrite (unsigned_lit (2 * n)) by lia. rewrite shiftr1_double by lia.
step. rewrite (unsigned_lit n) by lia.
step.
destruct (Z_lt_dec n 16) as [Hn16 | Hn16].
-
pose proof (lor7_bound n ltac:(lia)) as L7.
step. if_truex.
step. step. if_truex.
step. step. if_true.
step. if_false.
step.
do 9 step.
lazymatch goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
pose proof (obj_join rsegs m S n szb j s rest ltac:(lia) Hsz SZ DATA WIN REST) as OBJ.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
destruct (first_nul_split s (j :: rest)) as (str & rest' & E & NONUL & Hlen).
rewrite E in OBJ.
finish.
all: try exact OBJ.
all: try exact FDP.
all: try lia.
exact NONUL.
-
pose proof (lor7_eq23 n ltac:(lia)) as L7.
step. rewrite L7. if_falsex. step.
step. step. if_truex.
step. step. if_true.
step. if_false.
step.
do 9 step.
lazymatch goal with H : rw_cells rsegs ?mx (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2 end.
release_frame FR2 ST2 (bv_unsigned sp).
pose proof (obj_join rsegs m S n szb j s rest ltac:(lia) Hsz SZ DATA WIN REST) as OBJ.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
destruct (first_nul_split s (j :: rest)) as (str & rest' & E & NONUL & Hlen).
rewrite E in OBJ.
finish.
all: try exact OBJ.
all: try exact FDP.
all: try lia.
exact NONUL.
Qed.

#[using="Type"] Lemma crls_loop :
forall (fuel : nat) (sp ra s0 s1 s2 s3 s4 s5 : word)
(x1 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
(S P ptr rem lo maxlen n k i : Z) (szb j : byte) (s rest data j8 : list byte) (xa0 : word),
rem - k <= Z.of_nat fuel ->
xa0 = Z_to_bv 64 (rem - k) ->
rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - FRAME ->
bv_unsigned szb = 2 * n -> 0 <= n <= i - 1 -> 1 <= i <= maxlen -> maxlen <= 20 ->
rw_cells rsegs m S [C1 szb] ->
rw_cells rsegs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells rsegs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells rsegs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k < rem ->
rw_cells rsegs m P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
bytes_at rsegs m ptr data -> Z.of_nat (length data) = rem ->
munch (crls_W FRAME (bv_unsigned sp) S P) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
bv_unsigned sp <= S -> S + 24 <= P -> ptr + rem <= bv_unsigned sp - FRAME -> 0 < ptr ->
evt rsegs (crls_post rsegs FRAME maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 maxlen) xa0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21338) fc None m (seg_rom rsegs)).
Proof.
induction fuel as [|fuel IH]; intros until xa0; intros Hfuel -> FR ST LO Hsz Hn Hi Hmax SZ DATA WIN REST Hk FDP SRC LEN MU WM MI HS HP HD Hpt.
{ exfalso. lia. }
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.

assert (PUSHK : forall (k' : Z) (mc : word -> option byte) (c : byte) (xa0 xa2 xa3 xa4 : word),
k < k' <= rem ->
rw_cells rsegs mc (bv_unsigned sp + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs mc lo (bv_unsigned sp + -64) ->
rw_cells rsegs mc S [C1 szb] -> rw_cells rsegs mc (S + 1) [CB (Z.to_nat n) s] ->
rw_cells rsegs mc (S + n + 1) [C1 b0; C1 j] -> rw_cells rsegs mc (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells rsegs mc P [C8 (Z_to_bv 64 (ptr + k')); C8 (Z_to_bv 64 (rem - k'))] ->
bytes_at rsegs mc ptr data ->
munch (crls_W FRAME (bv_unsigned sp) S P) m0 mc -> wmono rsegs m0 mc -> mem_inv rsegs mc ->
evt rsegs (crls_post rsegs FRAME maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 maxlen) xa0 (Z_to_bv 64 (bv_unsigned c)) xa2 xa3 xa4 a5 a6 a7
(Z_to_bv 64 P) (Z_to_bv 64 i) (Z_to_bv 64 (-1)) (Z_to_bv 64 92) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2137c) fc None mc (seg_rom rsegs))).
{ intros k' mc c xa0 xa2 xa3 xa4 Hk' FRc STc SZc DATAc WINc RESTc FDPc SRCc MUc WMc MIc.
clear FR ST SZ DATA WIN REST FDP SRC MU WM MI.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
unfold crls_W in MUc.
bstep. bstep.
call_pushb S n lo szb b0 j.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
| |- bv_unsigned _ = 2 * _ => assumption
| |- rw_cells _ _ _ [C1 _] => assumption
| |- rw_cells _ _ _ [C1 _; C1 _] => assumption
| |- stk _ _ _ _ => assumption
| |- mem_inv _ _ => assumption
| |- _ => lia
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
lazymatch goal with H : rw_cells rsegs m2 S [C1 ?sz] |- _ => rename H into SZ2 end.
lazymatch goal with H : rw_cells rsegs m2 (S + n + 1) _ |- _ => rename H into WIN2 end.
lazymatch goal with H : rw_cells rsegs m2 (S + 1) _ |- _ => rename H into DATA2 end.
lazymatch goal with H : rw_cells rsegs m2 (S + n + 3) _ |- _ => rename H into REST2 end.
lazymatch goal with H : rw_cells rsegs m2 P _ |- _ => rename H into FDP2 end.
lazymatch goal with H : rw_cells rsegs m2 (bv_unsigned sp + -64) _ |- _ => rename H into FR2 end.
lazymatch goal with H : stk rsegs m2 lo _ |- _ => rename H into ST2 end.
lazymatch goal with H : bytes_at rsegs m2 ptr data |- _ => rename H into SRC2 end.
lazymatch goal with H : munch _ m0 m2 |- _ => rename H into MU2 end.
lazymatch goal with H : wmono rsegs m0 m2 |- _ => rename H into WM2 end.
lazymatch goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
lazymatch goal with H : bv_unsigned ?szb' = 2 * (n + 1) |- _ => rename H into Hsz2 end.
destruct (rw_cells_unpair _ _ _ _ _ WIN2) as [Hcb Hnul]. clear WIN2.
replace (S + n + 1) with (S + 1 + Z.of_nat (Z.to_nat n)) in Hcb by lia.
pose proof (rw_cells_CB_snoc _ _ _ _ _ _ DATA2 Hcb) as DATA3. clear DATA2 Hcb.
replace (Datatypes.S (Z.to_nat n)) with (Z.to_nat (n + 1)) in DATA3 by lia.
destruct rest as [|j' rest']; [cbn in Lr; exfalso; lia|].
replace (Z.to_nat (21 - n)) with (Datatypes.S (Z.to_nat (21 - (n + 1)))) in REST2 by lia.
destruct (rw_cells_CB_head _ _ _ _ _ _ REST2) as [Hj' REST3]. clear REST2.
replace (S + n + 1 + 1) with (S + (n + 1) + 1) in Hnul by lia.
replace (S + n + 3) with (S + (n + 1) + 1 + 1) in Hj' by lia.
pose proof (rw_cells_pair _ _ _ _ _ Hnul Hj') as WIN3. clear Hnul Hj'.
replace (S + n + 3 + 1) with (S + (n + 1) + 3) in REST3 by lia.
fold (crls_W FRAME (bv_unsigned sp) S P) in MU2.

bstep.
destruct (Z_lt_dec i maxlen) as [LT | GE].
2:{ if_truex.
eapply crls_done; [exact FR2 | exact ST2 | | exact Hsz2 | | | exact SZ2 | exact DATA3 | exact WIN3 | exact REST3 | | exact FDP2 | exact SRC2 | exact MU2 | exact WM2 | exact MI2 | ]; lia. }
if_falsex.
unfold crls_W in MU2.
bstep. bstep.
bstep.
destruct (Z.eq_dec (rem - k') 0) as [Z0 | NZ].
- if_falsex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU2.
eapply crls_done; [exact FR2 | exact ST2 | | exact Hsz2 | | | exact SZ2 | exact DATA3 | exact WIN3 | exact REST3 | | exact FDP2 | exact SRC2 | exact MU2 | exact WM2 | exact MI2 | ]; lia.
- if_truex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU2.
eapply (IH sp ra s0 s1 s2 s3 s4 s5); [ | reflexivity | exact FR2 | exact ST2 | | exact Hsz2 | | | | exact SZ2 | exact DATA3 | exact WIN3 | exact REST3 | | exact FDP2 | exact SRC2 | exact LEN | exact MU2 | exact WM2 | exact MI2 | | | | ]; lia. }

destruct (nth_error data (Z.to_nat k)) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as B1R. unfold bv_modulus in B1R. cbn in B1R.
unfold crls_W in MU.
pose proof (u8ro_read rsegs m ptr data k b1 _ SRC Hb1 ltac:(lia) eq_refl) as RD1.
bst. clear RD1. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)).
bstep. bstep. bstep. bstep.
bstep.
destruct (Z.eq_dec (bv_unsigned b1) 92) as [E92 | N92].
2:{
if_truex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 1) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 1)) with (rem - k + -1) by lia. replace (ptr + (k + 1)) with (ptr + k + 1) by lia. exact FDP. }
if_falsex.
bstep.
destruct (Z.eq_dec (rem - k - 1) 0) as [R0 | R1].
{
if_truex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 1) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 1)) with (rem - k + -1) by lia. replace (ptr + (k + 1)) with (ptr + k + 1) by lia. exact FDP. }
if_falsex.

destruct (nth_error data (Z.to_nat (k + 1))) as [b2|] eqn:Hb2; [| exfalso; apply nth_error_None in Hb2; lia].
pose proof (bv_unsigned_in_range 8 b2) as B2R. unfold bv_modulus in B2R. cbn in B2R.
pose proof (u8ro_read rsegs _ ptr data (k + 1) b2 _ SRC Hb2 ltac:(lia) eq_refl) as RD2.
replace (ptr + (k + 1)) with (ptr + k + 1) in RD2 by lia.
bstep. clear RD2. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)).
bstep. bstep. bstep. bstep.
bstep.
destruct (Z.eq_dec (bv_unsigned b2) 92) as [F92 | M92].
-
if_falsex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (PUSHK (k + 2) mx b1); [lia | exact FR | exact ST | exact SZ | exact DATA | exact WIN | exact REST | | exact SRC | exact MU | exact WM | exact MI] end.
replace (rem - (k + 2)) with (rem - k + -2) by lia. replace (ptr + (k + 2)) with (ptr + k + 2) by lia. exact FDP.
-
if_truex. fold (crls_W FRAME (bv_unsigned sp) S P) in MU.
eapply crls_done with (k := k + 2);
[exact FR | exact ST | | exact Hsz | | | exact SZ | exact DATA | exact WIN | exact REST |
| replace (ptr + (k + 2)) with (ptr + k + 2) by lia; replace (rem - (k + 2)) with (rem - k + -2) by lia; exact FDP
| exact SRC | exact MU | exact WM | exact MI | ]; lia.
Qed.

#[using="Type"] Lemma crls_spec_P : crls_stmt rsegs CRLS_P CRLS_FRAME_P.
Proof.
unfold crls_stmt, CRLS_P, CRLS_FRAME_P. intros until data. intros A0 A1 A2 Hmax OBJ FDP SRC LEN Hptr ST LO HS HP HD MI. subst a0 a1 a2.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize Nat.add] in OB.
pose proof (munch_refl (crls_W 128 (bv_unsigned sp) S P) m) as MU. unfold crls_W in MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 64%nat ST.
runto 0x21304. bstepz. bstepz. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
lazymatch goal with H : rw_cells rsegs m1 S _ |- _ => rename H into OBJ3 end.

assert (OBJz : rw_cells rsegs m1 S ([C1 b0] ++ ([CB 0 []] ++ ([C1 b0; C1 b0] ++ [CB 21 (repeat b0 21)])))).
{ eapply rw_cells_recast; [exact OBJ3 | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity]. }
clear OBJ3.
apply (proj1 (rw_cells_app rsegs m1 S _ _)) in OBJz as [SZ0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. change (Z.of_nat 1) with 1 in OBJz.
apply (proj1 (rw_cells_app rsegs m1 _ _ _)) in OBJz as [DATA0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. rewrite Z.add_0_r in OBJz.
apply (proj1 (rw_cells_app rsegs m1 _ _ _)) in OBJz as [WIN0 REST0]. cbn [cells_size csize Nat.add] in REST0. change (Z.of_nat 2) with 2 in REST0.
replace (S + 1) with (S + 0 + 1) in WIN0 by lia. replace (S + 1 + 2) with (S + 0 + 3) in REST0 by lia.

assert (J : forall r : Z, 0 <= r <= maxlen ->
evt rsegs (crls_post rsegs 128 maxlen ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S P ptr rem lo data m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 maxlen)
(Z_to_bv 64 S) (Z_to_bv 64 r) (Z_to_bv 64 maxlen) a3 a4 a5 a6 a7 (Z_to_bv 64 P) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21318) fc None m1 (seg_rom rsegs))).
2:{ bstep.
destruct (Z_lt_dec rem maxlen) as [LT | GE].
- if_truex. apply J. lia.
- if_falsex. bstep. apply J. lia. }
intros r Hr.
bstep. bstep.
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?spv + ?kk))) _)) _ _ _ _ _ _) => name_sp spv kk
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?spv + ?kk)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => name_sp spv kk
end.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply reserve_spec with (S := S) (n := 0) (r := r) (szb := b0) (rest := @nil cell) | unfold reserve_post; post_call segs mm] end.
all: unname_sp.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
| |- bv_unsigned _ = 2 * _ => reflexivity
| |- rw_cells _ _ _ (C1 _ :: _) => exact SZ0
| |- mem_inv _ _ => assumption
| |- _ => lia
end.
runto 0. if_falsex. runto 0.
destruct (Z.eq_dec rem 0) as [R0 | R1].
- if_truex. fold (crls_W 128 (bv_unsigned sp) S P) in MU.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) _ |- _ => rename H into FR end.
eapply crls_done with (k := 0) (n := 0) (szb := b0);
[exact FR | exact ST | | reflexivity | | | exact SZ0 | exact DATA0 | exact WIN0 | exact REST0 |
| rewrite Z.add_0_r, Z.sub_0_r; exact FDP | exact SRC | exact MU | exact WM | assumption | ]; lia.
- if_falsex. runto 0x21338. fold (crls_W 128 (bv_unsigned sp) S P) in MU.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) _ |- _ => rename H into FR end.
eapply (crls_loop (Z.to_nat rem) sp ra s0 s1 s2 s3 s4 s5) with (k := 0) (n := 0) (i := 1) (szb := b0);
[ | f_equal; lia | exact FR | exact ST | | reflexivity | | | | exact SZ0 | exact DATA0 | exact WIN0 | exact REST0 |
| rewrite Z.add_0_r, Z.sub_0_r; exact FDP | exact SRC | exact LEN | exact MU | exact WM | assumption | | | | ]; lia.
Qed.
End CrlsP.
