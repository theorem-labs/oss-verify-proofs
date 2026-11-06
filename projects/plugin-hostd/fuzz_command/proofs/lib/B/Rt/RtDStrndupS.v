(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the inline range check of plugin-hostd/fuzz_command's strdup entry (0x4cd38-0x4cd64 and the exact check 0x4cf4c-0x4cf7c), in the plain msteps form lib/A/Rt/RtSIstrlen.v gives internal_strlen. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDStrdupS.v, with its module paths, module names, addresses and numbers changed; 58 of its 290 lines of code are new or changed and 116 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w YK0e YK0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0a YO0c YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32 YN3h YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDStrndupTbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The inline read check of plugin-hostd/fuzz_command's strndup entry on its ASan+UBSan image (fuzz_command.asan-ubsan;
   the walk of lib/A/Rt/RtDStrndupS.v moved by the name-keyed A-to-B address map, and the auipc value at 0x4585c,
   0x4585c + (0x60 << 12) = 0xa585c, read from this image's code) for a size of 1 to 64 bytes (0x4585c-0x45894,
   and the exact check 0x45970-0x459a0), stepped one instruction at a time. The entry checks the [mm] bytes from x,
   mm = min(n, k + 1) (s4), against the shadow: it loads the shadow offset through the GOT word 0xa5f50 (its value is
   the shadow cell 0xb0c38, whose value is 0x7fff8000), or-s the two 8-aligned shadow words around the first and the
   last granule, and if they are not both zero tests the granules one at a time. Every way out that a clean range
   takes ends at 0x45898. The premises are what a live block's shadow (AR_shadow_law) gives for a range inside it.
   [len] below is mm - 1, the offset of the last byte checked. *)
Definition SN_SB : Z := 0x7fff8000.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Definition A0 : Z := SN_SB + g0.
Definition A1 : Z := SN_SB + g1.
Definition cnt : nat := Z.to_nat (g1 - g0).

Hypothesis HG1 : word_mem tfibsegs m 0xa5f50 0xb0c38.
Hypothesis HG2 : word_mem tfibsegs m 0xb0c38 SN_SB.
Hypothesis GZ : forall g, g0 <= g < g1 ->
rdn tfibsegs m (Z_to_bv 64 (SN_SB + g)) 1%nat = Some [Z_to_bv 8 0].
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
SN_SB <= A0 /\ A0 <= A1 /\ A1 + 8 < 2 ^ 64 /\ 0 <= A0 - A0 mod 8 /\ A0 - A0 mod 8 + 8 < 2 ^ 64 /\
0 <= A1 - A1 mod 8 /\ A1 - A1 mod 8 + 8 < 2 ^ 64.
Proof.
unfold A0, A1, g0, g1, SN_SB.
assert (M0 : x = 8 * (x / 8) + x mod 8) by (apply Z.div_mod; lia).
assert (M1 : x + len = 8 * ((x + len) / 8) + (x + len) mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (x + len) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (2147450880 + (x + len) / 8) 8 ltac:(lia)).
repeat split; lia.
Qed.

Definition keepS (r : bv 5) : Prop := r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.
Definition finS (regs : bvmap 5 word) (pc : word) : Prop :=
exists regs' (pcf : word),
msteps tfibsegs (mkst regs pc m rom) (mkst regs' pcf m rom) /\ bv_unsigned pcf = 0x45898
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
Lemma finS_here : forall regs (pc : word), bv_unsigned pc = 0x45898 -> finS regs pc.
Proof. intros regs pc H. exists regs, pc. split; [apply mst_refl|]. split; [exact H | intros r _; reflexivity]. Qed.
Ltac frameS :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keepS in Hr; destruct Hr as (?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_atS z L := apply (finS_pc _ _ (Z_to_bv 64 z)); [ vm_compute; reflexivity | apply L ].

(* 0x4599c: the answer byte is zero, so the entry goes on at 0x45898. *)
Lemma snc_tail : forall regs, getr regs 12 = Z_to_bv 64 0 -> finS regs (Z_to_bv 64 0x4599c).
Proof.
intros regs H12.
eapply finS_steps.
- norm_pc.
svx S_45950 DS_45950 (Z_to_bv 64 0) ltac:(gr; rwH; imm_norm; rewrite v_andi_lit by lia; reflexivity).
sdbt S_45954 DS_45954 ltac:(gr; rwH; rewrite branch_eq; apply Z.eqb_eq; reflexivity).
apply mst_refl.
- frameS.
- apply finS_here. vm_compute. reflexivity.
Qed.

(* 0x4598c: the loop over the granules of the range, each of them clean. *)
Lemma snc_loop : forall k i regs,
(i + k = cnt)%nat -> (i < cnt)%nat ->
getr regs 10 = Z_to_bv 64 (A0 + Z.of_nat i) ->
getr regs 11 = Z_to_bv 64 A1 ->
getr regs 12 = Z_to_bv 64 0 ->
finS regs (Z_to_bv 64 0x4598c).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
induction k as [|k IH]; intros i regs Hik Hi H10 H11 H12; [lia|].
assert (HgB : g0 <= g0 + Z.of_nat i < g1) by lia.
assert (HA : A0 + Z.of_nat i = SN_SB + (g0 + Z.of_nat i)) by (unfold A0, SN_SB, g0; lia).
eapply finS_steps.
- norm_pc.
sdlbu S_45940 DS_45940 ltac:(addr_tac; rewrite HA; apply GZ; lia).
svx S_45944 DS_45944 (Z_to_bv 64 (A0 + Z.of_nat i + 1)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; reflexivity).
sdov S_45948 DS_45948 (Z_to_bv 64 0) ltac:(gr; rwH; rewrite alu_or; unfold v_or;
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0)))) with 0; rewrite Z.lor_0_l;
f_equal; rewrite Z_to_bv_unsigned; reflexivity).
apply mst_refl.
- frameS.
- destruct (Nat.eq_dec (S i) cnt) as [He|Hne].
+ eapply finS_steps.
* norm_pc.
sdbf S_4594c DS_4594c ltac:(gr; rwH; rewrite branch_ne; apply negb_false_iff; apply Z.eqb_eq;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
* frameS.
* fin_atS 0x4599c snc_tail. gr. reflexivity.
+ eapply finS_steps.
* norm_pc.
sdbt S_4594c DS_4594c ltac:(gr; rwH; rewrite branch_ne; apply negb_true_iff; apply Z.eqb_neq;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
* frameS.
* fin_atS 0x4598c (IH (S i)); try lia; gr; try reflexivity; try assumption.
replace (A0 + Z.of_nat (S i)) with (A0 + Z.of_nat i + 1) by lia. reflexivity.
Qed.

(* 0x45970: the exact check. The last granule's shadow byte allows the last byte of the range, and every granule
   the loop walks is clean, so the answer is zero. *)
Lemma snc_exact : forall regs,
getr regs 10 = Z_to_bv 64 A0 ->
getr regs 11 = Z_to_bv 64 A1 ->
getr regs 12 = Z_to_bv 64 (x + len) ->
finS regs (Z_to_bv 64 0x45970).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
intros regs H10 H11 H12. destruct GLAST as (b & Hb & Hbv).
pose proof (Z.mod_pos_bound (x + len) 8 ltac:(lia)) as Hm8.
pose proof (u8_range b) as Hbr.
eapply finS_steps.
- norm_pc.
sdlb S_45924 DS_45924 ltac:(addr_tac; exact Hb).
svx S_45928 DS_45928 (Z_to_bv 64 ((x + len) mod 8))
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
sdov S_4592c DS_4592c (Z_to_bv 64 (if 0 <? bv_unsigned b then 1 else 0))
ltac:(gr; rwH; rewrite Hlb; rewrite alu_sltu; rewrite v_sltu_lit2 by lia; reflexivity).
sdov S_45930 DS_45930 (Z_to_bv 64 (if (x + len) mod 8 <? bv_unsigned b then 1 else 0))
ltac:(gr; rwH; rewrite Hlb; rewrite alu_slt; rewrite v_slt_lit2 by lia; reflexivity).
svx S_45934 DS_45934 (Z_to_bv 64 (if (x + len) mod 8 <? bv_unsigned b then 0 else 1))
ltac:(gr; rwH; imm_norm;
rewrite v_xori_01 by (destruct ((x + len) mod 8 <? bv_unsigned b); [right | left]; reflexivity);
destruct ((x + len) mod 8 <? bv_unsigned b); reflexivity).
sdov S_45938 DS_45938 (Z_to_bv 64 0)
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
sdbt S_4593c DS_4593c ltac:(gr; rwH; rewrite branch_geu; apply negb_true_iff; apply Z.ltb_ge;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
-- frameS.
-- fin_atS 0x4599c snc_tail. gr. reflexivity.
* eapply finS_steps.
-- norm_pc.
sdbf S_4593c DS_4593c ltac:(gr; rwH; rewrite branch_geu; apply negb_false_iff; apply Z.ltb_lt;
rewrite !u_Z2bv by lia; lia).
apply mst_refl.
-- frameS.
-- fin_atS 0x4598c (snc_loop cnt 0%nat); try lia; gr; try reflexivity; try assumption.
replace (A0 + Z.of_nat 0) with A0 by lia. assumption.
Qed.

(* 0x4585c: the whole check, both ways out of the word test at 0x45894. s1 = x, s4 = len + 1. *)
Theorem snc_block : forall regs,
getr regs 9 = Z_to_bv 64 x ->
getr regs 20 = Z_to_bv 64 (len + 1) ->
finS regs (Z_to_bv 64 0x4585c).
Proof.
pose proof g_facts as (P0 & P1 & P2 & PD & P4 & P5 & P6 & P7 & P8 & P9 & P10). pose proof cnt_val as P3.
intros regs H9 H20.
destruct HW0 as (bs0 & Hbs0 & Lbs0). destruct HW1 as (bs1 & Hbs1 & Lbs1).
destruct (word_mem_ld tfibsegs m 0xa5f50 0xb0c38 HG1 ltac:(lia) ltac:(lia)) as (bg1 & Hg1 & Vg1).
destruct (word_mem_ld tfibsegs m 0xb0c38 SN_SB HG2 ltac:(lia) ltac:(lia)) as (bg2 & Hg2 & Vg2).
pose proof (bytes_le_to_Z_range bs0 Lbs0) as R0. pose proof (bytes_le_to_Z_range bs1 Lbs1) as R1.
set (v0 := Z_to_bv 64 (bytes_le_to_Z bs0)). set (v1 := Z_to_bv 64 (bytes_le_to_Z bs1)).
eapply finS_steps.
- norm_pc.
svx S_45810 DS_45810 (Z_to_bv 64 0xa585c) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
sdld S_45814 DS_45814 bg1 (Z_to_bv 64 0xb0c38) ltac:(addr_tac; exact Hg1) ltac:(exact Vg1).
sdov S_45818 DS_45818 (Z_to_bv 64 (x + (len + 1))) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
sdld S_4581c DS_4581c bg2 (Z_to_bv 64 SN_SB) ltac:(addr_tac; exact Hg2) ltac:(exact Vg2).
svx S_45820 DS_45820 (Z_to_bv 64 g0) ltac:(gr; rwH; unfold g0; apply srli3_val; lia).
svx S_45824 DS_45824 (Z_to_bv 64 (x + len)) ltac:(gr; rwH; imm_norm; rewrite v_addi_lit; f_equal; lia).
svx S_45828 DS_45828 (Z_to_bv 64 g1) ltac:(gr; rwH; unfold g1; apply srli3_val; lia).
sdov S_4582c DS_4582c (Z_to_bv 64 A0) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
sdov S_45830 DS_45830 (Z_to_bv 64 A1) ltac:(gr; rwH; rewrite alu_add; apply v_add_lit).
svx S_45834 DS_45834 (Z_to_bv 64 (A0 - A0 mod 8)) ltac:(gr; rwH; imm_norm; apply andm8_val; lia).
svx S_45838 DS_45838 (Z_to_bv 64 (A1 - A1 mod 8)) ltac:(gr; rwH; imm_norm; apply andm8_val; lia).
sdld S_4583c DS_4583c bs0 v0 ltac:(addr_tac; exact Hbs0) ltac:(unfold v0; rewrite u_Z2bv by lia; reflexivity).
sdld S_45840 DS_45840 bs1 v1 ltac:(addr_tac; exact Hbs1) ltac:(unfold v1; rewrite u_Z2bv by lia; reflexivity).
sdov S_45844 DS_45844 (Z_to_bv 64 (Z.lor (bytes_le_to_Z bs1) (bytes_le_to_Z bs0)))
ltac:(gr; rwH; apply bv_eq; rewrite AX2S.u_or64; unfold v0, v1; rewrite !u_Z2bv by lia;
rewrite u_Z2bv by (pose proof (Z_lor_range (bytes_le_to_Z bs1) (bytes_le_to_Z bs0) ltac:(lia) ltac:(lia)); lia); reflexivity).
apply mst_refl.
- frameS.
- pose proof (Z_lor_range (bytes_le_to_Z bs1) (bytes_le_to_Z bs0) ltac:(lia) ltac:(lia)) as RL.
destruct (Z.eq_dec (Z.lor (bytes_le_to_Z bs1) (bytes_le_to_Z bs0)) 0) as [Hz|Hnz].
+ eapply finS_steps.
* norm_pc.
sdbf S_45848 DS_45848 ltac:(gr; rewrite branch_ne; apply negb_false_iff; apply Z.eqb_eq;
rewrite !u_Z2bv by lia; exact Hz).
apply mst_refl.
* frameS.
* apply finS_here. vm_compute. reflexivity.
+ eapply finS_steps.
* norm_pc.
sdbt S_45848 DS_45848 ltac:(gr; rewrite branch_ne; apply negb_true_iff; apply Z.eqb_neq;
rewrite !u_Z2bv by lia; exact Hnz).
apply mst_refl.
* frameS.
* fin_atS 0x45970 snc_exact; gr; try reflexivity.
Qed.

End c.
