(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02 YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End c.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Ltac msteps_done :=
lazymatch goal with
| |- msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
first [ apply mst_refl
| replace q with p by (symmetry; bveq); apply mst_refl ]
end.
Ltac gr :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition NUL : byte := Z_to_bv 8 0.
Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma nth_app_nul_in : forall (s : list byte) j, (j < length s)%nat -> In (nth j (s ++ [NUL]) NUL) s.
Proof. intros s j Hj. rewrite app_nth1 by lia. apply nth_In. lia. Qed.
Lemma nth_app_nul_last : forall s : list byte, nth (length s) (s ++ [NUL]) NUL = NUL.
Proof. intros s. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma step_op_at : forall segs regs pc mem rom w op rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
alu64 op (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_op_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
End d.
Ltac stepov F D vv tac :=
chain_step;
[ reflexivity
| eapply step_op_at with (v := vv);
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Ltac steplbu F D tac :=
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepbt F D tac :=
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepbf F D tac :=
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepret F D :=
chain_step;
[ reflexivity
| eapply step_jalr_x0; [ exact F | reflexivity | exact D | gr; reflexivity ]
| step_simpl; imm_norm ].
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0.
Proof. reflexivity. Qed.
Lemma eqb_w_true : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a = b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_eq. exact Hab. Qed.
Lemma eqb_w_false : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a <> b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_neq. exact Hab. Qed.
Lemma ltu_w : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma F_15280 : fetch_word src0segs (0x152dc%bv : word) = Some (0x0004b503%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15280 : decode_any (0x0004b503%bv : bv 32) = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15284 : fetch_word src0segs (0x152e0%bv : word) = Some (0x00848493%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15284 : decode_any (0x00848493%bv : bv 32) = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15288 : fetch_word src0segs (0x152e4%bv : word) = Some (0xfe051ce3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15288 : decode_any (0xfe051ce3%bv : bv 32) = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1532c : fetch_word src0segs (0x15388%bv : word) = Some (0x00140593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1532c : decode_any (0x00140593%bv : bv 32) = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15330 : fetch_word src0segs (0x1538c%bv : word) = Some (0x00853023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15330 : decode_any (0x00853023%bv : bv 32) = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15334 : fetch_word src0segs (0x15390%bv : word) = Some (0x02f00613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15334 : decode_any (0x02f00613%bv : bv 32) = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15338 : fetch_word src0segs (0x15394%bv : word) = Some (0x00c0006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15338 : decode_any (0x00c0006f%bv : bv 32) = Some (Jal 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1533c : fetch_word src0segs (0x15398%bv : word) = Some (0x00b53023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1533c : decode_any (0x00b53023%bv : bv 32) = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15340 : fetch_word src0segs (0x1539c%bv : word) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15340 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15344 : fetch_word src0segs (0x153a0%bv : word) = Some (0xfff5c683%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15344 : decode_any (0xfff5c683%bv : bv 32) = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15348 : fetch_word src0segs (0x153a4%bv : word) = Some (0xfec68ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15348 : decode_any (0xfec68ae3%bv : bv 32) = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1534c : fetch_word src0segs (0x153a8%bv : word) = Some (0xfe069ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1534c : decode_any (0xfe069ae3%bv : bv 32) = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma word_of_bytes8 : forall segs mem a bs,
rdn segs mem a 8 = Some bs ->
bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
intros segs mem a bs H.
pose proof (rdn_length _ _ _ _ _ H) as Hl.
pose proof (bytes_le_to_Z_range bs Hl).
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma src0_envp_count : forall n regs mem rom (e : word),
getr regs 9 = e ->
(forall i, (i < n)%nat -> exists bs,
rdn src0segs mem (Z_to_bv 64 (bv_unsigned e + 8 * Z.of_nat i)) 8 = Some bs
/\ bytes_le_to_Z bs <> 0) ->
(exists bs, rdn src0segs mem (Z_to_bv 64 (bv_unsigned e + 8 * Z.of_nat n)) 8 = Some bs
/\ bytes_le_to_Z bs = 0) ->
bv_unsigned e + 8 * Z.of_nat n + 8 < 2^64 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x152dc) mem rom)
(mkst regs' (Z_to_bv 64 0x152e8) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ getr regs' 9 = Z_to_bv 64 (bv_unsigned e + 8 * Z.of_nat n + 8)
/\ (forall r : reg, r <> 9%bv -> r <> 10%bv -> getr regs' r = getr regs r).
Proof.
induction n as [|n IH]; intros regs mem rom e H9 Hnz Hz Hnw.
- destruct Hz as (bs & Hrd & Hbs).
pose proof (u64_range e) as He. subst e.
eexists. split.
+ norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_ld; [exact F_15280 | reflexivity | exact D_15280 | | ].
- imm_norm. rewrite v_addi_0.
rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 9)). change (Z.of_nat 0%nat) with 0 in Hrd.
rewrite Z.mul_0_r, Z.add_0_r in Hrd. exact Hrd.
- eapply word_of_bytes8. exact Hrd. }
step_simpl.
stepi F_15284 D_15284.
chain_step; [reflexivity| | ].
{ eapply step_branch_ft_gen; [exact F_15288 | reflexivity | exact D_15288 | ].
getr_resolve. rewrite Hbs. reflexivity. }
step_simpl. msteps_done.
+ split; [getr_resolve; rewrite Hbs; reflexivity|].
split; [getr_resolve; change (Z.of_nat 0%nat) with 0; imm_norm; unfold v_addi; f_equal; lia|].
intros r H9' H10'. rewrite !getr_other by assumption. reflexivity.
- pose proof (u64_range e) as He.
destruct (Hnz 0%nat ltac:(lia)) as (bs0 & Hrd0 & Hbs0).
rewrite Z.mul_0_r, Z.add_0_r, Z_to_bv_bv_unsigned in Hrd0.
pose proof (rdn_length _ _ _ _ _ Hrd0) as Hl0.
pose proof (bytes_le_to_Z_range bs0 Hl0) as Hr0.
set (e' := Z_to_bv 64 (bv_unsigned e + 8)).
assert (He' : bv_unsigned e' = bv_unsigned e + 8) by (subst e'; apply u_Z2bv; lia).
set (regs1 := regupd (regupd regs 10 (Z_to_bv 64 (bytes_le_to_Z bs0))) 9 e').
destruct (IH regs1 mem rom e') as (regs' & Hms & H10 & H9' & Hfr).
+ subst regs1. getr_resolve. reflexivity.
+ intros i Hi. rewrite He'.
replace (bv_unsigned e + 8 + 8 * Z.of_nat i) with (bv_unsigned e + 8 * Z.of_nat (S i)) by lia.
apply Hnz. lia.
+ rewrite He'.
replace (bv_unsigned e + 8 + 8 * Z.of_nat n) with (bv_unsigned e + 8 * Z.of_nat (S n)) by lia.
exact Hz.
+ rewrite He'. lia.
+ exists regs'. split; [|split; [exact H10|split]].
* eapply msteps_trans; [|exact Hms].
subst e. norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_ld; [exact F_15280 | reflexivity | exact D_15280 | | ].
- imm_norm. rewrite v_addi_0. exact Hrd0.
- symmetry. apply u_Z2bv; lia. }
step_simpl.
stepiv F_15284 D_15284 e' ltac:(subst e'; getr_resolve; imm_norm; reflexivity).
chain_step; [reflexivity| | ].
{ eapply step_branch_tk_gen; [exact F_15288 | reflexivity | exact D_15288 | ].
getr_resolve. cbn [branch_taken]. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
rewrite !u_Z2bv by lia. exact Hbs0. }
step_simpl. subst regs1. msteps_done.
* rewrite H9', He'. f_equal. lia.
* intros r Hr9 Hr10. rewrite (Hfr r Hr9 Hr10). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Definition SLASH : byte := Z_to_bv 8 47.
Definition PROGNAME : Z := 0x4fd30.
Fixpoint after_slash (s : list byte) (i acc : nat) : nat :=
match s with
| [] => acc
| b :: s' => after_slash s' (S i) (if bv_eqb b SLASH then S i else acc)
end.
Definition progname_off (s : list byte) : nat := after_slash s 0 0.
Lemma after_slash_app : forall s1 s2 i acc,
after_slash (s1 ++ s2) i acc = after_slash s2 (i + length s1) (after_slash s1 i acc).
Proof.
induction s1 as [|b s1 IH]; intros s2 i acc; cbn [after_slash app length].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH. f_equal. lia.
Qed.
Lemma after_slash_firstn_S : forall s i, (i < length s)%nat ->
after_slash (firstn (S i) s) 0 0
= (if bv_eqb (nth i s NUL) SLASH then S i else after_slash (firstn i s) 0 0).
Proof.
intros s i Hi.
rewrite <- (firstn_skipn i s) at 1.
rewrite firstn_app, firstn_firstn, Nat.min_r by lia.
rewrite length_firstn, Nat.min_l by lia.
replace (S i - i)%nat with 1%nat by lia.
rewrite after_slash_app, length_firstn, Nat.min_l by lia.
destruct (skipn i s) as [|b r] eqn:E.
- exfalso. pose proof (f_equal (@length byte) E) as HL. rewrite length_skipn in HL. cbn in HL. lia.
- cbn [firstn after_slash].
assert (Hb : b = nth i s NUL).
{ rewrite <- (firstn_skipn i s), app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l, Nat.sub_diag, E by lia. reflexivity. }
rewrite Hb, Nat.add_0_l. destruct (bv_eqb (nth i s NUL) SLASH); reflexivity.
Qed.
Lemma progname_store_ok : forall m, store_ok src0segs m (Z_to_bv 64 PROGNAME) 8 = true.
Proof. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.
Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs NUL).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; cbn [length] in *; [lia|].
cbn [wbytes].
destruct rest as [|b' rest'].
- cbn [wbytes length] in *.
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with 0%nat by lia. reflexivity.
- cbn [length] in *.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
+ rewrite wbytes_below by (cbn [length]; rewrite ?Hu1; lia).
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
rewrite Heq, Z.sub_diag. reflexivity.
+ rewrite IH by (cbn [length]; rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma wbytes_overwrite : forall m (a : word) (x y : list byte),
length x = length y ->
bv_unsigned a + Z.of_nat (length y) <= 2^64 ->
wbytes (wbytes m a x) a y = wbytes m a y.
Proof.
intros m a x y Hl Hnw. apply functional_extensionality. intros z.
pose proof (u64_range z) as Hz.
destruct (Z_lt_dec (bv_unsigned z) (bv_unsigned a)) as [Hlt|Hge].
{ rewrite !wbytes_below by lia. reflexivity. }
destruct (Z_lt_dec (bv_unsigned z) (bv_unsigned a + Z.of_nat (length y))) as [Hin|Hout].
{ rewrite !wbytes_inside by lia. reflexivity. }
rewrite !wbytes_above by lia. reflexivity.
Qed.
Section g.
Variable s : list byte.
Variable pn : word.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hfit : bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64.
Hypothesis Hdisj : PROGNAME + 8 <= bv_unsigned pn
\/ bv_unsigned pn + Z.of_nat (length s) + 1 <= PROGNAME.
Definition str_at (mem : word -> option byte) : Prop :=
forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Definition pnv (i : nat) : word :=
Z_to_bv 64 (bv_unsigned pn + Z.of_nat (after_slash (firstn i s) 0 0)).
Definition pmem (mem : word -> option byte) (i : nat) : word -> option byte :=
wbytes mem (Z_to_bv 64 PROGNAME) (word_to_le_bytes 8 (pnv i)).
Lemma PROGNAME_u : bv_unsigned (Z_to_bv 64 PROGNAME) = PROGNAME.
Proof. reflexivity. Qed.
Lemma pmem_read : forall mem i j, str_at mem -> (j <= length s)%nat ->
rdn src0segs (pmem mem i) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Proof.
intros mem i j Hstr Hj. unfold pmem.
pose proof (u64_range pn).
rewrite rdn_wbytes_out.
- apply Hstr. exact Hj.
- rewrite PROGNAME_u, length_N_to_le_bytes, u_Z2bv by lia. unfold PROGNAME in *. cbn [Z.of_nat]. lia.
- rewrite u_Z2bv by lia. cbn [Z.of_nat]. lia.
- rewrite PROGNAME_u, length_N_to_le_bytes. unfold PROGNAME. cbn. lia.
Qed.
Lemma scan_loop : forall k regs mem rom i,
(k = length s - i)%nat -> (i <= length s)%nat ->
getr regs 10 = Z_to_bv 64 PROGNAME ->
getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat i + 1) ->
getr regs 12 = Z_to_bv 64 47 ->
str_at mem ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x153a0) (pmem mem i) rom)
(mkst regs' (Z_to_bv 64 0x153ac) (pmem mem (length s)) rom)
/\ getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1)
/\ getr regs' 13 = Z_to_bv 64 0
/\ (forall r : reg, r <> 11%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs mem rom i Hk Hi H10 H11 H12 Hstr.
-
assert (Hil : i = length s) by lia. subst i.
pose proof (u64_range pn) as Hpn.
eexists. split.
+ norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_lbu; [exact F_15344 | reflexivity | exact D_15344 | ].
rewrite H11. imm_norm. rewrite v_addi_m1 by (rewrite u_Z2bv by lia; lia).
rewrite u_Z2bv by lia.
replace (bv_unsigned pn + Z.of_nat (length s) + 1 - 1) with (bv_unsigned pn + Z.of_nat (length s)) by lia.
apply pmem_read; [exact Hstr| lia]. }
step_simpl. rewrite nth_app_nul_last.
chain_step; [reflexivity| | ].
{ eapply step_branch_ft_gen; [exact F_15348 | reflexivity | exact D_15348 | ].
gr. rewrite H12. vm_compute. reflexivity. }
step_simpl.
chain_step; [reflexivity| | ].
{ eapply step_branch_ft_gen; [exact F_1534c | reflexivity | exact D_1534c | ].
gr. vm_compute. reflexivity. }
step_simpl. msteps_done.
+ split; [rewrite getr_other by reg_neq_tac; exact H11|].
split; [gr; reflexivity|].
intros r H11' H13'. rewrite !getr_other by assumption. reflexivity.
-
assert (Hil : (i < length s)%nat) by lia.
pose proof (u64_range pn) as Hpn.
set (b := nth i (s ++ [NUL]) NUL).
assert (Hb : b <> NUL).
{ intros Hc. apply Hnul. rewrite <- Hc. apply nth_app_nul_in. exact Hil. }
assert (Hbs : b = nth i s NUL) by (unfold b; rewrite app_nth1 by lia; reflexivity).
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
assert (Hload : msteps src0segs (mkst regs (Z_to_bv 64 0x153a0) (pmem mem i) rom)
(mkst regs1 (Z_to_bv 64 0x153a4) (pmem mem i) rom)).
{ norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_lbu; [exact F_15344 | reflexivity | exact D_15344 | ].
rewrite H11. imm_norm. rewrite v_addi_m1 by (rewrite u_Z2bv by lia; lia).
rewrite u_Z2bv by lia.
replace (bv_unsigned pn + Z.of_nat i + 1 - 1) with (bv_unsigned pn + Z.of_nat i) by lia.
apply pmem_read; [exact Hstr| lia]. }
step_simpl. subst regs1 b. msteps_done. }
set (regs2 := regupd regs1 11 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S i) + 1))).
destruct (IH regs2 mem rom (S i)) as (regs' & Hms & H11' & H13' & Hfr); try lia.
{ subst regs2 regs1. gr. exact H10. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. exact H12. }
{ exact Hstr. }
assert (Hpnv : pnv (S i) = if bv_eqb b SLASH then Z_to_bv 64 (bv_unsigned pn + Z.of_nat i + 1) else pnv i).
{ unfold pnv. rewrite after_slash_firstn_S, <- Hbs by exact Hil.
destruct (bv_eqb b SLASH); [f_equal; lia| reflexivity]. }
assert (Hiter : msteps src0segs (mkst regs1 (Z_to_bv 64 0x153a4) (pmem mem i) rom)
(mkst regs2 (Z_to_bv 64 0x153a0) (pmem mem (S i)) rom)).
{ destruct (bv_eqb b SLASH) eqn:Eb.
-
assert (EbS : b = SLASH) by (apply bv_eqb_eq; exact Eb).
norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_branch_tk_gen; [exact F_15348 | reflexivity | exact D_15348 | ].
subst regs1. gr. rewrite H12, EbS. vm_compute. reflexivity. }
step_simpl.
chain_step; [reflexivity | | ].
{ eapply step_sd_at with (a := Z_to_bv 64 PROGNAME) (v := Z_to_bv 64 (bv_unsigned pn + Z.of_nat i + 1));
[ exact F_1533c | reflexivity | exact D_1533c | | | ].
- subst regs1; gr. rewrite H10. imm_norm. apply v_addi_0.
- subst regs1; gr. exact H11.
- apply progname_store_ok. }
step_simpl.
unfold pmem at 1. rewrite wbytes_overwrite
by (rewrite ?length_N_to_le_bytes; first [reflexivity | rewrite PROGNAME_u; unfold PROGNAME; cbn; lia]).
rewrite <- Hpnv. fold (pmem mem (S i)).
stepiv F_15340 D_15340 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S i) + 1))
ltac:(subst regs1; gr; rewrite H11; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
subst regs2. msteps_done.
-
norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_branch_ft_gen; [exact F_15348 | reflexivity | exact D_15348 | ].
subst regs1. gr. rewrite H12. cbn [branch_taken]. unfold bv_eqb in Eb |- *.
rewrite u_zext8. change (bv_unsigned SLASH) with 47 in Eb.
change (bv_unsigned (Z_to_bv 64 47)) with 47. exact Eb. }
step_simpl.
chain_step; [reflexivity| | ].
{ eapply step_branch_tk_gen; [exact F_1534c | reflexivity | exact D_1534c | ].
subst regs1. gr. cbn [branch_taken]. apply negb_true_iff. unfold bv_eqb.
rewrite u_zext8. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq.
apply byte_nz_u. exact Hb. }
step_simpl.
stepiv F_15340 D_15340 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S i) + 1))
ltac:(subst regs1; gr; rewrite H11; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
unfold pmem. rewrite Hpnv. subst regs2. msteps_done. }
exists regs'. split; [|split; [exact H11'|split; [exact H13'|]]].
+ eapply msteps_trans; [exact Hload|]. eapply msteps_trans; [exact Hiter| exact Hms].
+ intros r Hr11 Hr13. rewrite (Hfr r Hr11 Hr13). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma progname_scan_sec : forall regs mem rom,
getr regs 8 = pn ->
getr regs 10 = Z_to_bv 64 PROGNAME ->
str_at mem ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x15388) mem rom)
(mkst regs' (Z_to_bv 64 0x153ac)
(wbytes mem (Z_to_bv 64 PROGNAME)
(word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (progname_off s))))) rom)
/\ getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1)
/\ getr regs' 12 = Z_to_bv 64 47
/\ getr regs' 13 = Z_to_bv 64 0
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
intros regs mem rom H8 H10 Hstr.
pose proof (u64_range pn) as Hpn.
set (regs1 := regupd (regupd regs 11 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1))) 12 (Z_to_bv 64 47)).
destruct (scan_loop (length s) regs1 mem rom 0) as (regs' & Hms & H11' & H13' & Hfr); try lia.
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. reflexivity. }
{ exact Hstr. }
exists regs'. split.
- eapply msteps_trans; [|].
2:{ replace (progname_off s) with (after_slash (firstn (length s) s) 0 0)
by (rewrite firstn_all; reflexivity).
fold (pnv (length s)). fold (pmem mem (length s)). exact Hms. }
norm_pc.
stepiv F_1532c D_1532c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1))
ltac:(gr; rewrite H8; imm_norm; unfold v_addi; f_equal; lia).
chain_step; [reflexivity | | ].
{ eapply step_sd_at with (a := Z_to_bv 64 PROGNAME) (v := pnv 0);
[ exact F_15330 | reflexivity | exact D_15330 | | | ].
- gr. rewrite H10. imm_norm. apply v_addi_0.
- gr. rewrite H8. unfold pnv. cbn [firstn after_slash Z.of_nat]. rewrite Z.add_0_r.
symmetry. apply Z_to_bv_bv_unsigned.
- apply progname_store_ok. }
step_simpl. fold (pmem mem 0).
stepiv F_15334 D_15334 (Z_to_bv 64 47) ltac:(gr; reflexivity).
stepj F_15338 D_15338.
subst regs1. msteps_done.
- split; [exact H11'|]. split; [rewrite Hfr by reg_neq_tac; subst regs1; gr; reflexivity|].
split; [exact H13'|].
intros r Hr11 Hr12 Hr13. rewrite (Hfr r Hr11 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
End g.
Theorem src0_progname_scan :
forall (s : list byte) (pn : word) (mem rom : word -> option byte) regs,
~ In NUL s ->
bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64 ->
(PROGNAME + 8 <= bv_unsigned pn \/ bv_unsigned pn + Z.of_nat (length s) + 1 <= PROGNAME) ->
getr regs 8 = pn ->
getr regs 10 = Z_to_bv 64 PROGNAME ->
(forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x15388) mem rom)
(mkst regs' (Z_to_bv 64 0x153ac)
(wbytes mem (Z_to_bv 64 PROGNAME)
(word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (progname_off s))))) rom)
/\ getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1)
/\ getr regs' 12 = Z_to_bv 64 47
/\ getr regs' 13 = Z_to_bv 64 0
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof. intros. eapply progname_scan_sec; eassumption. Qed.
End f.
