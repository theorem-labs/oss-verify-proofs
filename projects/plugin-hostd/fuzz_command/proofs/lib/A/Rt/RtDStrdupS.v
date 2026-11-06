(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the inline range check of plugin-hostd/fuzz_command's strdup entry (0x4cd38-0x4cd64 and the exact check 0x4cf4c-0x4cf7c), in the plain msteps form lib/A/Rt/RtSIstrlen.v gives internal_strlen. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0e YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0a YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32 YN3h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry reaches 0x4cd38 with a0 = the length internal_strlen gave, a1 = the shadow base 0x7fff8000 and
   s1 = the string. It then reads the two 8-aligned shadow words of the range; if their or is zero the range is
   clean and the entry goes on at 0x4cd64, and if it is not, 0x4cf4c tests the granules one at a time and reaches
   the same 0x4cd64 when every one of them is clean. The premises below are what [aread_ok]'s range_addressable
   and shadow_hull_vis give for a range of at most 64 bytes, so both ways end at 0x4cd64 and the entry never
   calls the range check with a size the range check's own contract does not take. *)
Definition SD_SB : Z := 0x7fff8000.
Definition sds_ranges : list (Z * nat) := [(0x4cd38, 12%nat); (0x4cf4c, 13%nat)].
Definition tbl_sds : ctable := Eval vm_compute in build_ranges sds_ranges TEmpty.
Lemma tbl_sds_eq : tbl_sds = build_ranges sds_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_sds). Qed.
Lemma tbl_sds_ok : table_ok tfibsegs tbl_sds.
Proof. rewrite tbl_sds_eq. apply build_ranges_ok; [unfold sds_ranges; repeat constructor; cbn; discriminate | apply table_ok_empty]. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit_sds : forall (p : word) (w : bv 32),
clookup tbl_sds (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_sds_ok. exact H.
Qed.
End a.
Ltac ftac := apply fetch_lit_sds; vm_compute; reflexivity.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_d38 : fetch_word tfibsegs (Z_to_bv 64 0x4cd38) = Some (0x00950633%bv : bv 32). Proof. ftac. Qed.
Lemma D_d38 : decode_any (0x00950633%bv : bv 32) = Some (Op ALU_ADD 12 10 9, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d3c : fetch_word tfibsegs (Z_to_bv 64 0x4cd3c) = Some (0x0034d513%bv : bv 32). Proof. ftac. Qed.
Lemma D_d3c : decode_any (0x0034d513%bv : bv 32) = Some (ShiftImm ALU_SRL 10 9 3, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d40 : fetch_word tfibsegs (Z_to_bv 64 0x4cd40) = Some (0x00365693%bv : bv 32). Proof. ftac. Qed.
Lemma D_d40 : decode_any (0x00365693%bv : bv 32) = Some (ShiftImm ALU_SRL 13 12 3, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d44 : fetch_word tfibsegs (Z_to_bv 64 0x4cd44) = Some (0x00a58533%bv : bv 32). Proof. ftac. Qed.
Lemma D_d44 : decode_any (0x00a58533%bv : bv 32) = Some (Op ALU_ADD 10 11 10, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d48 : fetch_word tfibsegs (Z_to_bv 64 0x4cd48) = Some (0x00d585b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_d48 : decode_any (0x00d585b3%bv : bv 32) = Some (Op ALU_ADD 11 11 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d4c : fetch_word tfibsegs (Z_to_bv 64 0x4cd4c) = Some (0xff857693%bv : bv 32). Proof. ftac. Qed.
Lemma D_d4c : decode_any (0xff857693%bv : bv 32) = Some (OpImm ALU_AND 13 10 4088, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d50 : fetch_word tfibsegs (Z_to_bv 64 0x4cd50) = Some (0xff85f713%bv : bv 32). Proof. ftac. Qed.
Lemma D_d50 : decode_any (0xff85f713%bv : bv 32) = Some (OpImm ALU_AND 14 11 4088, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d54 : fetch_word tfibsegs (Z_to_bv 64 0x4cd54) = Some (0x0006b683%bv : bv 32). Proof. ftac. Qed.
Lemma D_d54 : decode_any (0x0006b683%bv : bv 32) = Some (Load SZ8 true 13 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d58 : fetch_word tfibsegs (Z_to_bv 64 0x4cd58) = Some (0x00073703%bv : bv 32). Proof. ftac. Qed.
Lemma D_d58 : decode_any (0x00073703%bv : bv 32) = Some (Load SZ8 true 14 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d5c : fetch_word tfibsegs (Z_to_bv 64 0x4cd5c) = Some (0x00d766b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_d5c : decode_any (0x00d766b3%bv : bv 32) = Some (Op ALU_OR 13 14 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_d60 : fetch_word tfibsegs (Z_to_bv 64 0x4cd60) = Some (0x1e069663%bv : bv 32). Proof. ftac. Qed.
Lemma D_d60 : decode_any (0x1e069663%bv : bv 32) = Some (Branch BC_NE 13 0 492, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f4c : fetch_word tfibsegs (Z_to_bv 64 0x4cf4c) = Some (0x00058683%bv : bv 32). Proof. ftac. Qed.
Lemma D_f4c : decode_any (0x00058683%bv : bv 32) = Some (Load SZ1 true 13 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f50 : fetch_word tfibsegs (Z_to_bv 64 0x4cf50) = Some (0x00767613%bv : bv 32). Proof. ftac. Qed.
Lemma D_f50 : decode_any (0x00767613%bv : bv 32) = Some (OpImm ALU_AND 12 12 7, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f54 : fetch_word tfibsegs (Z_to_bv 64 0x4cf54) = Some (0x00d03733%bv : bv 32). Proof. ftac. Qed.
Lemma D_f54 : decode_any (0x00d03733%bv : bv 32) = Some (Op ALU_SLTU 14 0 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f58 : fetch_word tfibsegs (Z_to_bv 64 0x4cf58) = Some (0x00d62633%bv : bv 32). Proof. ftac. Qed.
Lemma D_f58 : decode_any (0x00d62633%bv : bv 32) = Some (Op ALU_SLT 12 12 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f5c : fetch_word tfibsegs (Z_to_bv 64 0x4cf5c) = Some (0x00164613%bv : bv 32). Proof. ftac. Qed.
Lemma D_f5c : decode_any (0x00164613%bv : bv 32) = Some (OpImm ALU_XOR 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f60 : fetch_word tfibsegs (Z_to_bv 64 0x4cf60) = Some (0x00c77633%bv : bv 32). Proof. ftac. Qed.
Lemma D_f60 : decode_any (0x00c77633%bv : bv 32) = Some (Op ALU_AND 12 14 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f64 : fetch_word tfibsegs (Z_to_bv 64 0x4cf64) = Some (0x00b57a63%bv : bv 32). Proof. ftac. Qed.
Lemma D_f64 : decode_any (0x00b57a63%bv : bv 32) = Some (Branch BC_GEU 10 11 20, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f68 : fetch_word tfibsegs (Z_to_bv 64 0x4cf68) = Some (0x00054683%bv : bv 32). Proof. ftac. Qed.
Lemma D_f68 : decode_any (0x00054683%bv : bv 32) = Some (Load SZ1 false 13 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f6c : fetch_word tfibsegs (Z_to_bv 64 0x4cf6c) = Some (0x00150513%bv : bv 32). Proof. ftac. Qed.
Lemma D_f6c : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f70 : fetch_word tfibsegs (Z_to_bv 64 0x4cf70) = Some (0x00c6e633%bv : bv 32). Proof. ftac. Qed.
Lemma D_f70 : decode_any (0x00c6e633%bv : bv 32) = Some (Op ALU_OR 12 13 12, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f74 : fetch_word tfibsegs (Z_to_bv 64 0x4cf74) = Some (0xfeb51ae3%bv : bv 32). Proof. ftac. Qed.
Lemma D_f74 : decode_any (0xfeb51ae3%bv : bv 32) = Some (Branch BC_NE 10 11 8180, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f78 : fetch_word tfibsegs (Z_to_bv 64 0x4cf78) = Some (0x0ff67513%bv : bv 32). Proof. ftac. Qed.
Lemma D_f78 : decode_any (0x0ff67513%bv : bv 32) = Some (OpImm ALU_AND 10 12 255, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_f7c : fetch_word tfibsegs (Z_to_bv 64 0x4cf7c) = Some (0xde0504e3%bv : bv 32). Proof. ftac. Qed.
Lemma D_f7c : decode_any (0xde0504e3%bv : bv 32) = Some (Branch BC_EQ 10 0 7656, 4%Z). Proof. vm_refl_bv. Qed.

Lemma land7_mod : forall z, 0 <= z -> Z.land z 7 = z mod 8.
Proof. intros z Hz. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma andm8_val : forall z, 0 <= z < 2 ^ 64 -> v_andi (Z_to_bv 64 z) (-8) = Z_to_bv 64 (z - z mod 8).
Proof.
intros z Hz. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3). rewrite land_neg_pow2_u64 by lia. reflexivity.
Qed.
Lemma srli3_val : forall z, 0 <= z < 2 ^ 64 -> v_srli (Z_to_bv 64 z) 3 = Z_to_bv 64 (z / 8).
Proof.
intros z Hz.
assert (Hd : 0 <= z / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_eq. rewrite (v_srli_div (Z_to_bv 64 z) 3 ltac:(lia)), !u_Z2bv by lia.
change (2 ^ 3) with 8. reflexivity.
Qed.
Lemma lor7_small : forall z, 0 <= z < 256 -> Z.land z 255 = z.
Proof. intros z Hz. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma v_sltu_lit2 : forall a c, 0 <= a < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 c) = Z_to_bv 64 (if a <? c then 1 else 0).
Proof. intros a c Ha Hc. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. destruct (a <? c); reflexivity. Qed.
Lemma v_slt_lit2 : forall a c, 0 <= a < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
v_slt (Z_to_bv 64 a) (Z_to_bv 64 c) = Z_to_bv 64 (if a <? c then 1 else 0).
Proof.
intros a c Ha Hc. unfold v_slt, c_lts, bv_lts.
rewrite !bv_signed_small by (rewrite u_Z2bv by lia; lia). rewrite !u_Z2bv by lia.
destruct (a <? c); reflexivity.
Qed.
Lemma v_and_lit2 : forall a c, 0 <= a < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
v_and (Z_to_bv 64 a) (Z_to_bv 64 c) = Z_to_bv 64 (Z.land a c).
Proof. intros a c Ha Hc. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma v_or_lit2 : forall a c, 0 <= a < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
v_or (Z_to_bv 64 a) (Z_to_bv 64 c) = Z_to_bv 64 (Z.lor a c).
Proof. intros a c Ha Hc. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma v_xori_01 : forall z, z = 0 \/ z = 1 -> v_xori (Z_to_bv 64 z) 1 = Z_to_bv 64 (1 - z).
Proof.
intros z Hz. unfold v_xori. rewrite u_Z2bv by (destruct Hz as [->| ->]; lia).
replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
destruct Hz as [->| ->]; reflexivity.
Qed.
End b.

Ltac svx F0 D vv tac := let F := litF F0 in stepiv F D vv tac.
Ltac sdov F0 D vv tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_op_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Ltac sdbt F0 D tac := let F := litF F0 in
chain_step; [ reflexivity | eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | tac ] | step_simpl ].
Ltac sdbf F0 D tac := let F := litF F0 in
chain_step; [ reflexivity | eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | tac ] | step_simpl ].
Ltac sdlbu F0 D tac := let F := litF F0 in
chain_step; [ reflexivity | eapply step_lbu; [ exact F | reflexivity | exact D | tac ] | step_simpl ].
Ltac sdlb F0 D tac := let F := litF F0 in
chain_step; [ reflexivity | eapply step_lb; [ exact F | reflexivity | exact D | tac ] | step_simpl ].
Ltac sdld F0 D bbs vv tac1 tac2 := let F := litF F0 in
chain_step; [ reflexivity | eapply step_ld with (bs := bbs) (v := vv); [ exact F | reflexivity | exact D | tac1 | tac2 ] | step_simpl ].
Ltac addr_tac := gr; rwH; imm_norm; rewrite ?v_addi_lit; rewrite ?Z.add_0_r.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (x len : Z).
Variables (m rom : word -> option byte).
Hypothesis Hx : 0 < x.
Hypothesis Hlen : 0 <= len < 64.
Hypothesis Hxn : x + len + 1 <= 2 ^ 63.

Definition g0 : Z := x / 8.
Definition g1 : Z := (x + len) / 8.
Definition A0 : Z := SD_SB + g0.
Definition A1 : Z := SD_SB + g1.
Definition cnt : nat := Z.to_nat (g1 - g0).

Hypothesis GZ : forall g, g0 <= g < g1 ->
rdn tfibsegs m (Z_to_bv 64 (SD_SB + g)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis GLAST : exists b : byte, rdn tfibsegs m (Z_to_bv 64 A1) 1%nat = Some [b] /\
(bv_unsigned b = 0 \/ ((x + len) mod 8 < bv_unsigned b < 8)).
Hypothesis HW0 : exists bs, rdn tfibsegs m (Z_to_bv 64 (A0 - A0 mod 8)) 8%nat = Some bs /\ length bs = 8%nat.
Hypothesis HW1 : exists bs, rdn tfibsegs m (Z_to_bv 64 (A1 - A1 mod 8)) 8%nat = Some bs /\ length bs = 8%nat.

Lemma cnt_val : Z.of_nat cnt = g1 - g0.
Proof.
unfold cnt, g1, g0. rewrite Z2Nat.id; [reflexivity|].
assert (x / 8 <= (x + len) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma g_facts : 0 <= g0 /\ g0 <= g1 /\ g1 - g0 <= 8 /\ A1 - A0 = g1 - g0 /\
SD_SB <= A0 /\ A0 <= A1 /\ A1 + 8 < 2 ^ 64 /\ 0 <= A0 - A0 mod 8 /\ A0 - A0 mod 8 + 8 < 2 ^ 64 /\
0 <= A1 - A1 mod 8 /\ A1 - A1 mod 8 + 8 < 2 ^ 64.
Proof.
unfold A0, A1, g0, g1, SD_SB.
assert (M0 : x = 8 * (x / 8) + x mod 8) by (apply Z.div_mod; lia).
assert (M1 : x + len = 8 * ((x + len) / 8) + (x + len) mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (x + len) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147483648 + x / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147483648 + (x + len) / 8) 8 ltac:(lia)).
repeat split; lia.
Qed.

Definition keepS (r : reg) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.
Definition finS (regs : bvmap 5 word) (pc : word) : Prop :=
exists regs' (pcf : word),
msteps tfibsegs (mkst regs pc m rom) (mkst regs' pcf m rom) /\ bv_unsigned pcf = 0x4cd64
/\ forall r, keepS r -> getr regs' r = getr regs r.
Lemma finS_steps : forall regs pc regs2 pc2,
msteps tfibsegs (mkst regs pc m rom) (mkst regs2 pc2 m rom) ->
(forall r, keepS r -> getr regs2 r = getr regs r) ->
finS regs2 pc2 -> finS regs pc.
Proof.
intros regs pc regs2 pc2 Hms Hfr (regs' & pcf & Hms' & Hpc & Hfr').
exists regs', pcf. split; [eapply msteps_trans; [exact Hms | exact Hms']|].
split; [exact Hpc|].
intros r Hr. rewrite (Hfr' r Hr). apply Hfr. exact Hr.
Qed.
Lemma finS_pc : forall regs (pc pc' : word), bv_unsigned pc = bv_unsigned pc' -> finS regs pc' -> finS regs pc.
Proof. intros regs pc pc' H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Lemma finS_here : forall regs (pc : word), bv_unsigned pc = 0x4cd64 -> finS regs pc.
Proof. intros regs pc H. exists regs, pc. split; [apply mst_refl|]. split; [exact H | intros r _; reflexivity]. Qed.
Ltac frameS :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keepS in Hr; destruct Hr as (?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_atS z L := apply (finS_pc _ _ (Z_to_bv 64 z)); [ vm_compute; reflexivity | apply L ].

(* 0x4cf78: the answer byte is zero, so the entry goes on at 0x4cd64. *)
Lemma sds_tail : forall regs, getr regs 12 = Z_to_bv 64 0 -> finS regs (Z_to_bv 64 0x4cf78).
Proof.
intros regs H12.
eapply finS_steps.
- norm_pc.
svx F_f78 D_f78 (Z_to_bv 64 0) ltac:(gr; rwH; imm_norm; rewrite v_andi_lit by lia; reflexivity).
sdbt F_f7c D_f7c ltac:(gr; rwH; rewrite branch_eq; apply Z.eqb_eq; reflexivity).
apply mst_refl.
- frameS.
- apply finS_here. vm_compute. reflexivity.
Qed.

(* 0x4cf68: the loop over the granules of the range, each of them clean. *)
Lemma sds_loop : forall k i regs,
(i + k = cnt)%nat -> (i < cnt)%nat ->
getr regs 10 = Z_to_bv 64 (A0 + Z.of_nat i) ->
getr regs 11 = Z_to_bv 64 A1 ->
getr regs 12 = Z_to_bv 64 0 ->
finS regs (Z_to_bv 64 0x4cf68).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
induction k as [|k IH]; intros i regs Hik Hi H10 H11 H12; [lia|].
assert (HgB : g0 <= g0 + Z.of_nat i < g1) by lia.
assert (HA : A0 + Z.of_nat i = SD_SB + (g0 + Z.of_nat i)) by (unfold A0, SD_SB, g0; lia).
eapply finS_steps.
- norm_pc.
sdlbu F_f68 D_f68 ltac:(addr_tac; rewrite HA; apply GZ; lia).
svx F_f6c D_f6c (Z_to_bv 64 (A0 + Z.of_nat i + 1)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; reflexivity).
sdov F_f70 D_f70 (Z_to_bv 64 0) ltac:(gr; rwH; rewrite alu_or; unfold v_or;
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) with 0; rewrite Z.lor_0_l;
f_equal; rewrite Z_to_bv_unsigned; reflexivity).
apply mst_refl.
- frameS.
- destruct (Nat.eq_dec (S i) cnt) as [He|Hne].
+ eapply finS_steps.
* norm_pc.
sdbf F_f74 D_f74 ltac:(gr; rwH; rewrite branch_ne; apply negb_false_iff; apply Z.eqb_eq;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
* frameS.
* fin_atS 0x4cf78 sds_tail. gr. reflexivity.
+ eapply finS_steps.
* norm_pc.
sdbt F_f74 D_f74 ltac:(gr; rwH; rewrite branch_ne; apply negb_true_iff; apply Z.eqb_neq;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
* frameS.
* fin_atS 0x4cf68 (IH (S i)); try lia; gr; try reflexivity; try assumption.
replace (A0 + Z.of_nat (S i)) with (A0 + Z.of_nat i + 1) by lia. reflexivity.
Qed.

(* 0x4cf4c: the exact check. The last granule's shadow byte allows the last byte of the range, and every granule
   the loop walks is clean, so the answer is zero. *)
Lemma sds_exact : forall regs,
getr regs 10 = Z_to_bv 64 A0 ->
getr regs 11 = Z_to_bv 64 A1 ->
getr regs 12 = Z_to_bv 64 (x + len) ->
finS regs (Z_to_bv 64 0x4cf4c).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
intros regs H10 H11 H12. destruct GLAST as (b & Hb & Hbv).
pose proof (Z.mod_pos_bound (x + len) 8 ltac:(lia)) as Hm8.
pose proof (u8_range b) as Hbr.
eapply finS_steps.
- norm_pc.
sdlb F_f4c D_f4c ltac:(addr_tac; exact Hb).
svx F_f50 D_f50 (Z_to_bv 64 ((x + len) mod 8))
ltac:(gr; rwH; imm_norm; rewrite v_andi_lit by lia; rewrite land7_mod by lia; reflexivity).
apply mst_refl.
- frameS.
-
assert (Hb8 : bv_unsigned b < 128) by (destruct Hbv as [Hz|[Hlo Hhi]]; lia).
assert (Hlb : v_lb b = Z_to_bv 64 (bv_unsigned b)).
{ unfold v_lb. f_equal.
rewrite <- (Z_to_bv_bv_unsigned 8 b) at 1. rewrite Z_to_bv_signed.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 8) with 256 by reflexivity. replace (256 / 2) with 128 by reflexivity.
rewrite Z.mod_small by lia. lia. }
eapply finS_steps.
+ norm_pc.
sdov F_f54 D_f54 (Z_to_bv 64 (if 0 <? bv_unsigned b then 1 else 0))
ltac:(gr; rwH; rewrite Hlb; rewrite alu_sltu; rewrite v_sltu_lit2 by lia; reflexivity).
sdov F_f58 D_f58 (Z_to_bv 64 (if (x + len) mod 8 <? bv_unsigned b then 1 else 0))
ltac:(gr; rwH; rewrite Hlb; rewrite alu_slt; rewrite v_slt_lit2 by lia; reflexivity).
svx F_f5c D_f5c (Z_to_bv 64 (if (x + len) mod 8 <? bv_unsigned b then 0 else 1))
ltac:(gr; rwH; imm_norm;
rewrite v_xori_01 by (destruct ((x + len) mod 8 <? bv_unsigned b); [right | left]; reflexivity);
destruct ((x + len) mod 8 <? bv_unsigned b); reflexivity).
sdov F_f60 D_f60 (Z_to_bv 64 0)
ltac:(gr; rwH; rewrite alu_and;
rewrite v_and_lit2 by (destruct (0 <? bv_unsigned b); destruct ((x + len) mod 8 <? bv_unsigned b); lia);
destruct Hbv as [Hz|[Hlt Hhi]];
[ replace (0 <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia);
f_equal; destruct ((x + len) mod 8 <? bv_unsigned b); reflexivity
| replace ((x + len) mod 8 <? bv_unsigned b) with true by (symmetry; apply Z.ltb_lt; lia);
f_equal; destruct (0 <? bv_unsigned b); reflexivity ]).
apply mst_refl.
+ frameS.
+ destruct (Nat.eq_dec cnt 0) as [Hc0|Hcn].
* eapply finS_steps.
-- norm_pc.
sdbt F_f64 D_f64 ltac:(gr; rwH; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
-- frameS.
-- fin_atS 0x4cf78 sds_tail. gr. reflexivity.
* eapply finS_steps.
-- norm_pc.
sdbf F_f64 D_f64 ltac:(gr; rwH; rewrite branch_geu; apply negb_false_iff; apply Z.ltb_lt;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
-- frameS.
-- fin_atS 0x4cf68 (sds_loop cnt 0%nat); try lia; gr; try reflexivity; try assumption.
replace (A0 + Z.of_nat 0) with A0 by lia. assumption.
Qed.

(* 0x4cd38: the whole check, both ways out of the word test at 0x4cd60. *)
Theorem sds_block : forall regs,
getr regs 10 = Z_to_bv 64 len ->
getr regs 11 = Z_to_bv 64 SD_SB ->
getr regs 9 = Z_to_bv 64 x ->
finS regs (Z_to_bv 64 0x4cd38).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
intros regs H10 H11 H9.
destruct HW0 as (bs0 & Hbs0 & Lbs0). destruct HW1 as (bs1 & Hbs1 & Lbs1).
pose proof (bytes_le_to_Z_range bs0 Lbs0) as R0. pose proof (bytes_le_to_Z_range bs1 Lbs1) as R1.
set (v0 := Z_to_bv 64 (bytes_le_to_Z bs0)). set (v1 := Z_to_bv 64 (bytes_le_to_Z bs1)).
eapply finS_steps.
- norm_pc.
sdov F_d38 D_d38 (Z_to_bv 64 (len + x)) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
svx F_d3c D_d3c (Z_to_bv 64 g0) ltac:(gr; rwH; unfold g0; apply srli3_val; lia).
svx F_d40 D_d40 (Z_to_bv 64 g1) ltac:(gr; rwH; unfold g1; replace (x + len) with (len + x) by lia; apply srli3_val; lia).
sdov F_d44 D_d44 (Z_to_bv 64 A0) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
sdov F_d48 D_d48 (Z_to_bv 64 A1) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
svx F_d4c D_d4c (Z_to_bv 64 (A0 - A0 mod 8)) ltac:(gr; rwH; imm_norm; apply andm8_val; lia).
svx F_d50 D_d50 (Z_to_bv 64 (A1 - A1 mod 8)) ltac:(gr; rwH; imm_norm; apply andm8_val; lia).
sdld F_d54 D_d54 bs0 v0 ltac:(addr_tac; exact Hbs0) ltac:(unfold v0; rewrite u_Z2bv by lia; reflexivity).
sdld F_d58 D_d58 bs1 v1 ltac:(addr_tac; exact Hbs1) ltac:(unfold v1; rewrite u_Z2bv by lia; reflexivity).
sdov F_d5c D_d5c (Z_to_bv 64 (Z.lor (bytes_le_to_Z bs1) (bytes_le_to_Z bs0)))
ltac:(gr; rwH; rewrite alu_or; unfold v0, v1; rewrite v_or_lit2 by lia; reflexivity).
apply mst_refl.
- frameS.
- pose proof (Z_lor_range (bytes_le_to_Z bs1) (bytes_le_to_Z bs0) ltac:(lia) ltac:(lia)) as RL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z bs1) (bytes_le_to_Z bs0)) 0) as [Hz|Hnz].
+ eapply finS_steps.
* norm_pc.
sdbf F_d60 D_d60 ltac:(gr; rewrite branch_ne; apply negb_false_iff; apply Z.eqb_eq;
rewrite !u_Z2bv by lia; exact Hz).
apply mst_refl.
* frameS.
* apply finS_here. vm_compute. reflexivity.
+ eapply finS_steps.
* norm_pc.
sdbt F_d60 D_d60 ltac:(gr; rewrite branch_ne; apply negb_true_iff; apply Z.eqb_neq;
rewrite !u_Z2bv by lia; exact Hnz).
apply mst_refl.
* frameS.
* fin_atS 0x4cf4c sds_exact; gr; try reflexivity; try assumption.
replace (x + len) with (len + x) by lia. reflexivity.
Qed.

End c.
