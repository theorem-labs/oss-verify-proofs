(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox QsV0 QsRG Qnhz Qrxj QSjk Qn1e QiVh QRjH QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3.
Import QBxa.Mq0.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
(x8 : word) : machine_state :=
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}.

#[using="Type"] Lemma step_ecall_epend : forall segs regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step segs (mkst regs pc mem rom)
= MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

#[using="Type"] Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg). Proof. apply bv_eq. reflexivity. Qed.
#[using="Type"] Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
#[using="Type"] Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

#[using="Type"] Lemma ms_read_byte_epend : forall segs regs pc mem x8,
ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof. reflexivity. Qed.

#[using="Type"] Lemma adv_set_epend : forall regs pc mem rom x8 v,
advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
= mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.

#[using="Type"] Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

#[using="Type"] Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.

#[using="Type"] Lemma rz_sys : forall segs regs pc mem rom model w T,
m_halted model = None ->
m_vm_lazy model = [] ->
fetch_word segs pc = Some w -> is_ecall w = true ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma rz_exit_lit : forall segs regs pc mem rom model code,
m_halted model = None -> is_exit_no (getr regs 17) ->
getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
(t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros segs regs pc mem rom model code Hh Hx8 Ha0 Hc.
rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply rz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.
End FPGEN1.

End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QBxa.Mq0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma alu_add_Z : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. change (alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 a + Z_to_bv 64 b)%bv.
rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma alu_and3_Z : forall a, 0 <= a ->
alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (a mod 4).
Proof.
intros a Ha. apply bv_eq.
change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 3)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 3)).
rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia.
change (2 ^ 2) with 4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bt_eq0_Z : forall a, 0 <= a < 2 ^ 64 ->
branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 0) = (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma bt_ne0_Z : forall a, 0 <= a < 2 ^ 64 ->
branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 0) = negb (a =? 0).
Proof. intros a Ha. cbn [branch_taken]. unfold bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma bt_and3 : forall c (w k : Z) (t : bool), 0 <= w + k ->
match c with BC_EQ => ((w + k) mod 4 =? 0) = t | BC_NE => negb ((w + k) mod 4 =? 0) = t | _ => False end ->
branch_taken c (alu64 ALU_AND (alu64 ALU_ADD (Z_to_bv 64 w) (Z_to_bv 64 k)) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
intros c w k t Hw Hc. rewrite alu_add_Z, alu_and3_Z by lia.
pose proof (Z.mod_pos_bound (w + k) 4 ltac:(lia)).
destruct c; try contradiction.
- rewrite bt_eq0_Z by lia. exact Hc.
- rewrite bt_ne0_Z by lia. exact Hc.
Qed.

Lemma bt_and3_0 : forall c (w : Z) (t : bool), 0 <= w ->
match c with BC_EQ => (w mod 4 =? 0) = t | BC_NE => negb (w mod 4 =? 0) = t | _ => False end ->
branch_taken c (alu64 ALU_AND (Z_to_bv 64 w) (Z_to_bv 64 3)) (Z_to_bv 64 0) = t.
Proof.
intros c w t Hw Hc. rewrite alu_and3_Z by lia.
pose proof (Z.mod_pos_bound w 4 ltac:(lia)).
destruct c; try contradiction.
- rewrite bt_eq0_Z by lia. exact Hc.
- rewrite bt_ne0_Z by lia. exact Hc.
Qed.

Lemma rdn_2 : forall segs m (a : word) b0 b1,
(bv_unsigned a + 2 <= 2 ^ 64)%Z ->
rdn segs m a 1 = Some [b0] -> rdn segs m (Z_to_bv 64 (bv_unsigned a + 1)) 1 = Some [b1] ->
rdn segs m a 2 = Some [b0; b1].
Proof.
intros segs m a b0 b1 Hnw H0 H1. cbn [rdn] in *.
destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [x|]; [|discriminate].
injection H0 as ->.
replace (a + 1)%bv with (Z_to_bv 64 (bv_unsigned a + 1)).
2:{ apply bv_eq. rewrite u64_lit by (pose proof (u64_range a); lia). symmetry. apply u_add1. lia. }
destruct (match m (Z_to_bv 64 (bv_unsigned a + 1)) with Some b => Some b | None => seg_rom segs _ end) as [y|];
[|discriminate].
injection H1 as ->. reflexivity.
Qed.

Lemma lin_neg1_val : forall (x : word) c,
alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c) = Z_to_bv 64 (c - bv_unsigned x).
Proof.
intros x c. apply bv_eq.
change (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) x) (Z_to_bv 64 c))
with ((Z_to_bv 64 (-1) * x) + Z_to_bv 64 c)%bv.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite <- Z.add_mod by lia.
replace ((2 ^ 64 - 1) * bv_unsigned x + c) with ((c - bv_unsigned x) + bv_unsigned x * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma bt_geu_Z : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
intros a b Hab Ha. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma bt_geu_Z_false : forall a b, 0 <= a < b -> b < 2 ^ 64 ->
branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
intros a b Hab Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia.
apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.

Lemma bt_ltu_Z : forall a b (t : bool), 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
(a <? b) = t -> branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = t.
Proof. intros a b t Ha Hb Ht. cbn [branch_taken]. unfold bv_ltu. rewrite !u64_lit by lia. exact Ht. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4_shift : forall w k r, w mod 4 = r -> (w + k) mod 4 = (r + k) mod 4.
Proof. intros w k r H. rewrite <- Zplus_mod_idemp_l, H. reflexivity. Qed.

Lemma even_mod4 : forall w, w mod 2 = 0 -> w mod 4 = 0 \/ w mod 4 = 2.
Proof. intros w H. lia. Qed.

Lemma mod4_cases : forall w, w mod 4 = 0 \/ w mod 4 = 1 \/ w mod 4 = 2 \/ w mod 4 = 3.
Proof. intros w. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG QRjH QBxa.Mq5.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Lemma t_alt2_comm : forall A B : TSet, t_eq (t_alt2 A B) (t_alt2 B A).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_idem_eq : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) A.
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

Lemma t_alt2_idem_eq_r : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) B.
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_congr_l : forall A A' B : TSet, t_eq A A' -> t_eq (t_alt2 A B) (t_alt2 A' B).
Proof. intros A A' B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

Lemma t_alt2_congr_r : forall A B B' : TSet, t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A B').
Proof. intros A B B' H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

Lemma t_alt3_as_alt2 : forall A B C : TSet,
t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.

Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof.
intros T H0 tr. unfold t_alt2, t_nil. split.
- intros [-> | H]; [exact H0 | exact H].
- intros H. right. exact H.
Qed.

Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof.
intros T H0 tr. unfold t_alt2, t_nil. split.
- intros [H | ->]; [exact H | exact H0].
- intros H. left. exact H.
Qed.

Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof. intros A B H. unfold t_alt2. left. exact H. Qed.

Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
- intros [[Hp | (tr' & -> & ->)] | H].
+ left. exact Hp.
+ right. exists []. split; [reflexivity | exact H0].
+ exact H.
- intros H. right. exact H.
Qed.

Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

Lemma W_nil : forall ch, W ch [] = [].
Proof. reflexivity. Qed.

Lemma t_emit_W_app : forall ch (a b : list byte) (T : TSet),
t_eq (t_emit (W ch a) (t_emit (W ch b) T)) (t_emit (W ch (a ++ b)) T).
Proof.
intros ch a b T. rewrite W_app. apply t_eq_sym.

intros tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
* left. exact Hp.
* right. exists b'. split; [reflexivity | left; exact Hp].
+ right. exists (W ch b ++ tr'). split; [rewrite app_assoc; reflexivity|].
right. exists tr'. auto.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_alt_W_wall : forall ch (bs : list byte) (K : TSet),
K [] -> (1 <= length bs)%nat ->
t_eq (t_alt (fun i : wr_index bs =>
t_emit (W ch (firstn (proj1_sig i) bs)) (t_emit (W ch (skipn (proj1_sig i) bs)) K)))
(t_emit (W ch bs) K).
Proof. intros ch bs K HK Hnb. unfold W. apply t_alt_wall; assumption. Qed.

Lemma t_emit_W_nil : forall ch (T : TSet), T [] -> t_eq (t_emit (W ch []) T) T.
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.

Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
intros e A B tr. unfold t_emit, t_alt2. split.
- intros [Hp | (tr' & -> & [HA | HB])].
+ left. left. exact Hp.
+ left. right. exists tr'. auto.
+ right. right. exists tr'. auto.
- intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
+ left. exact Hp.
+ right. exists tr'. auto.
+ left. exact Hp.
+ right. exists tr'. auto.
Qed.

Lemma exit_code_and_255 : forall c, (0 <= c < 256)%Z ->
bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = exit_code c.
Proof.
intros c Hc. unfold exit_code. apply bv_eq.
rewrite bv_and_unsigned, !Z_to_bv_unsigned.
rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma t_die_unfold : forall msg fs, t_die msg fs = t_emit (W 2 msg) (t_exit (exit_code 2) fs).
Proof. reflexivity. Qed.

Lemma exit_leaf_eq : forall c fs, (0 <= c < 256)%Z ->
t_eq (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs)) (t_exit (exit_code c) fs).
Proof.
intros c fs Hc. rewrite exit_code_and_255 by exact Hc. apply t_emit_W_nil. apply t_exit_has_nil.
Qed.
End Mq2.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 QBxa.Mq2.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma getr_empty : forall r : reg, getr bvmap_empty r = Z_to_bv 64 0.
Proof.
intro r. unfold getr. destruct (bv_eqb r 0); [reflexivity|].
unfold reg_get, bvmap_get, bvmap_empty.
destruct (bv_key r); cbn [tget]; apply bv_eq; reflexivity.
Qed.
End FPGEN1.

Local Open Scope Z_scope.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma land_align_mask : forall a k, 0 <= a < 2^64 -> 0 <= k <= 64 -> a mod 2^k = 0 ->
Z.land a (2^64 - 2^k) = a.
Proof.
intros a k Ha Hk Hmod.
replace (2^64 - 2^k) with (Z.ldiff (Z.ones 64) (Z.ones k)).
2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod a (2^k) ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma v_andi_m16_aligned : forall x : word,
bv_unsigned x mod 16 = 0 -> v_andi x (-16) = x.
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-16)) with (2^64 - 2^4).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

#[using="Type"] Lemma v_andi_m8_aligned : forall x : word,
bv_unsigned x mod 8 = 0 -> v_andi x (-8) = x.
Proof.
intros x Hm. unfold v_andi. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 (-8)) with (2^64 - 2^3).
pose proof (u64_range x).
rewrite land_align_mask by (first [lia | exact Hm]).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

#[using="Type"] Lemma land_low_zero : forall a k, 0 <= a -> 0 <= k -> a mod 2^k = 0 -> Z.land a (Z.ones k) = 0.
Proof. intros a k Ha Hk Hm. rewrite Z.land_ones by lia. exact Hm. Qed.

#[using="Type"] Lemma v_andi_3_aligned : forall x : word,
bv_unsigned x mod 4 = 0 -> v_andi x 3 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). apply land_low_zero; [apply u64_range | lia | exact Hm].
Qed.

#[using="Type"] Lemma land_4_aligned8 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 4 = 0.
Proof.
intros a Ha Hm.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
change 4 with (2^2). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 2 i); [|apply andb_false_r].
subst i.
replace a with ((a / 8) * 2^3) by lia.
rewrite Z.mul_pow2_bits by lia. change (2 - 3) with (-1).
rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

#[using="Type"] Lemma v_andi_4_aligned8 : forall x : word,
bv_unsigned x mod 8 = 0 -> v_andi x 4 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi. f_equal.
change (bv_wrap 64 4) with 4. apply land_4_aligned8; [apply u64_range | exact Hm].
Qed.

#[using="Type"] Lemma v_andi_1_of01 : forall z, (z = 0 \/ z = 1) ->
v_andi (Z_to_bv 64 z) 1 = Z_to_bv 64 z.
Proof.
intros z [-> | ->]; apply bv_eq; reflexivity.
Qed.

#[using="Type"] Lemma mod4_mod_pow2 : forall t k, 2 <= k -> (t mod 2^k) mod 4 = t mod 4.
Proof.
intros t k Hk. apply Z.mod_mod_divide.
exists (2^(k-2)). change 4 with (2^2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma negw_and3_aligned : forall x : word,
bv_unsigned x mod 4 = 0 -> v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 0.
Proof.
intros x Hm. unfold v_andi, v_subw. f_equal.
change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
unfold bv_swrap. rewrite bv_wrap64_mod.
change (bv_half_modulus 32) with (2^31).
unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2^2) with 4.
rewrite mod4_mod_pow2 by lia.
rewrite <- Zminus_mod_idemp_l.
rewrite mod4_mod_pow2 by lia.
replace ((0 - bv_unsigned x + 2^31) mod 4) with 0.
2:{ replace (0 - bv_unsigned x + 2^31) with (2^31 - bv_unsigned x) by lia.
rewrite <- Zminus_mod_idemp_r, Hm. reflexivity. }
reflexivity.
Qed.

#[using="Type"] Lemma firstn_Z_to_le_bytes : forall k n z, (k <= n)%nat ->
firstn k (Z_to_le_bytes n z) = Z_to_le_bytes k z.
Proof.
induction k as [|k IH]; intros n z Hk; [reflexivity|].
destruct n as [|n]; [lia|]. cbn [Z_to_le_bytes firstn]. rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma firstn_word_to_le_bytes : forall k n (v : word), (k <= n)%nat ->
firstn k (word_to_le_bytes n v) = word_to_le_bytes k v.
Proof. intros. unfold word_to_le_bytes. apply firstn_Z_to_le_bytes. assumption. Qed.

#[using="Type"] Lemma rdn_low_bytes : forall segs m (a v : word) k, (k <= 8)%nat ->
rdn segs m a 8 = Some (word_to_le_bytes 8 v) ->
rdn segs m a k = Some (word_to_le_bytes k v).
Proof.
intros segs m a v k Hk H.
rewrite (rdn_firstn segs m 8 a _ k H Hk). f_equal. apply firstn_word_to_le_bytes. exact Hk.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_4_small : forall v : word, bv_unsigned v < 2^32 ->
bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32).
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

#[using="Type"] Lemma v_lw_small : forall v : word, bv_unsigned v < 2^31 -> v_lw v = v.
Proof.
intros v Hv. unfold v_lw. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (u64_range v).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

#[using="Type"] Lemma v_add_lit_r : forall (x : word) (k : Z), 0 <= k < 2^64 ->
v_add x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. reflexivity. Qed.

#[using="Type"] Lemma v_add_lit_l : forall (x : word) (k : Z), 0 <= k < 2^64 ->
v_add (Z_to_bv 64 k) x = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros x k Hk. unfold v_add. rewrite (u_Z2bv k) by lia. f_equal. lia. Qed.

#[using="Type"] Lemma v_slli_lit : forall z sh, 0 <= z -> 0 <= sh -> z * 2^sh < 2^64 ->
v_slli (Z_to_bv 64 z) sh = Z_to_bv 64 (z * 2^sh).
Proof.
intros z sh Hz Hsh Hb. unfold v_slli. f_equal.
rewrite Z.shiftl_mul_pow2 by lia. rewrite u_Z2bv by nia. reflexivity.
Qed.

#[using="Type"] Lemma in_sub_bv : forall (l1 l2 : list reg) (r : reg),
forallb (fun x => existsb (fun y => bv_eqb x y) l2) l1 = true -> In r l1 -> In r l2.
Proof.
induction l1 as [|x l1 IH]; intros l2 r H Hin; [contradiction|].
cbn [forallb] in H. apply andb_true_iff in H as [Hx Hl1].
destruct Hin as [<-|Hin]; [|apply IH; assumption].
clear IH Hl1. induction l2 as [|y l2 IH2]; [discriminate|].
cbn [existsb] in Hx. apply orb_true_iff in Hx as [Hxy|Hx].
- left. symmetry. apply bv_eq. unfold bv_eqb in Hxy. apply Z.eqb_eq in Hxy. exact Hxy.
- right. apply IH2. exact Hx.
Qed.

#[using="Type"] Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof. intros a z H. symmetry. apply Z_to_bv_u_eq. exact H. Qed.
End FPGEN2.

End Mq3.
From Stdlib Require FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0 QBxa.Mq2.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Fixpoint zstores (m : word -> option byte) (d : word) (ws : list (Z * nat)) : word -> option byte :=
match ws with
| [] => m
| (o, n) :: ws' => zstores (wbytes m (Z_to_bv 64 (bv_unsigned d + o)) (zeros n)) d ws'
end.

Definition covers_off (i : Z) (on : Z * nat) : bool :=
(fst on <=? i) && (i <? fst on + Z.of_nat (snd on)).

Definition ws_inb (ws : list (Z * nat)) (N : Z) : bool :=
forallb (fun on => (0 <=? fst on) && (fst on + Z.of_nat (snd on) <=? N)) ws.

Fixpoint iota_Z (i : Z) (k : nat) : list Z :=
match k with O => [] | S k' => i :: iota_Z (i + 1) k' end.

Definition ws_cover (ws : list (Z * nat)) (N : nat) : bool :=
forallb (fun i => existsb (covers_off i) ws) (iota_Z 0 N).

#[using="Type"] Lemma forallb_In : forall {A} (f : A -> bool) l x, forallb f l = true -> In x l -> f x = true.
Proof.
induction l as [|y l IH]; intros x H Hin; [contradiction|].
cbn in H. apply andb_true_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

#[using="Type"] Lemma iota_Z_In : forall k i z, i <= z < i + Z.of_nat k -> In z (iota_Z i k).
Proof.
induction k as [|k IH]; intros i z Hz; [lia|].
cbn. destruct (Z.eq_dec i z); [left; assumption | right]. apply IH. lia.
Qed.

#[using="Type"] Lemma existsb_false_forall : forall {A} (f : A -> bool) l,
existsb f l = false -> forall x, In x l -> f x = false.
Proof.
induction l as [|y l IH]; intros H x Hin; [contradiction|].
cbn in H. apply orb_false_iff in H as [Hy Hl].
destruct Hin as [<-|Hin]; [exact Hy | apply IH; assumption].
Qed.

#[using="Type"] Lemma existsb_true_exists : forall {A} (f : A -> bool) l,
existsb f l = true -> exists x, In x l /\ f x = true.
Proof.
induction l as [|y l IH]; intros H; [discriminate|].
cbn in H. apply orb_true_iff in H as [Hy|Hl].
- exists y. split; [left; reflexivity | exact Hy].
- destruct (IH Hl) as [x [Hin Hx]]. exists x. split; [right; exact Hin | exact Hx].
Qed.

#[using="Type"] Lemma length_zeros : forall n, length (zeros n) = n.
Proof. intro n. apply repeat_length. Qed.

#[using="Type"] Lemma nth_zeros : forall n k, nth k (zeros n) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. intros n k. unfold zeros. apply nth_repeat. Qed.

#[using="Type"] Lemma rdn_wbytes_zeros_in : forall segs m (d a : word) (N n : nat),
bv_unsigned d + Z.of_nat N < 2^64 ->
bv_unsigned d <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned d + Z.of_nat N ->
rdn segs (wbytes m d (zeros N)) a n = Some (zeros n).
Proof.
intros segs m d a N n Hnw Hlo Hhi. unfold zeros at 2. apply rdn_const; [lia|].
intros x Hx. rewrite wbytes_inside by (rewrite length_zeros; lia).
f_equal. apply nth_zeros.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_zeros : forall n, bytes_le_to_Z (zeros n) = 0.
Proof.
induction n as [|n IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z].
fold (zeros n). rewrite IH. reflexivity.
Qed.

Section Cover.
Variable d : word.
Variable N : Z.
Hypothesis Hnw : bv_unsigned d + N < 2^64.

#[using="Hnw"] Lemma zstores_miss : forall ws m (x : word),
ws_inb ws N = true ->
(forall on, In on ws -> covers_off (bv_unsigned x - bv_unsigned d) on = false) ->
zstores m d ws x = m x.
Proof.
induction ws as [|[o n] ws IH]; intros m x Hinb Hno; [reflexivity|].
cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
apply Z.leb_le in Ho. apply Z.leb_le in Hn.
rewrite IH; [| exact Hinb | intros on Hin; apply Hno; right; exact Hin].
pose proof (Hno (o, n) (or_introl eq_refl)) as Hc. cbn [covers_off fst snd] in Hc.
pose proof (u64_range x). pose proof (u64_range d).
apply wbytes_outside.
- rewrite length_zeros. rewrite u_Z2bv by lia. lia.
- rewrite length_zeros. rewrite u_Z2bv by lia.
apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc];
cbn [fst snd] in Hc; lia.
Qed.

#[using="Hnw"] Lemma zstores_hit : forall ws m (x : word),
ws_inb ws N = true ->
(exists on, In on ws /\ covers_off (bv_unsigned x - bv_unsigned d) on = true) ->
zstores m d ws x = Some (Z_to_bv 8 0).
Proof.
induction ws as [|[o n] ws IH]; intros m x Hinb Hex.
{ destruct Hex as [on [[] _]]. }
cbn [zstores]. cbn [ws_inb forallb fst snd] in Hinb.
apply andb_true_iff in Hinb as [Hon Hinb]. apply andb_true_iff in Hon as [Ho Hn].
apply Z.leb_le in Ho. apply Z.leb_le in Hn.
destruct (existsb (covers_off (bv_unsigned x - bv_unsigned d)) ws) eqn:E.
- apply IH; [exact Hinb|]. apply existsb_true_exists. exact E.
- rewrite zstores_miss; [| exact Hinb | apply existsb_false_forall; exact E].
destruct Hex as [on [[<-|Hin] Hc]].
2:{ rewrite (existsb_false_forall _ _ E on Hin) in Hc. discriminate. }
cbn [covers_off fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2. cbn [fst snd] in Hc1, Hc2.
pose proof (u64_range x). pose proof (u64_range d).
rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia).
f_equal. apply nth_zeros.
Qed.

#[using="Hnw"] Lemma zstores_cover : forall ws m (n : nat),
Z.of_nat n = N ->
ws_inb ws N = true ->
ws_cover ws n = true ->
zstores m d ws = wbytes m d (zeros n).
Proof.
intros ws m n HnN Hinb Hcov. apply functional_extensionality. intro x.
pose proof (u64_range x). pose proof (u64_range d).
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d)) as [Hlt|Hge].
{ rewrite wbytes_outside by (rewrite length_zeros; lia).
apply zstores_miss; [exact Hinb|]. intros [o k] Hin.
pose proof (forallb_In _ _ _ Hinb Hin) as Hb. cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1.
cbn [covers_off fst snd]. apply andb_false_iff. left. apply Z.leb_gt. cbn [fst snd]. lia. }
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + N)) as [Hin|Hout].
- rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros.
apply zstores_hit; [exact Hinb|].
pose proof (forallb_In _ _ _ Hcov (iota_Z_In n 0 (bv_unsigned x - bv_unsigned d) ltac:(lia))) as He.
apply existsb_true_exists in He. exact He.
- rewrite wbytes_outside by (rewrite length_zeros; lia).
apply zstores_miss; [exact Hinb|]. intros [o k] Hin'.
pose proof (forallb_In _ _ _ Hinb Hin') as Hb. cbn [fst snd] in Hb.
apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
cbn [covers_off fst snd]. apply andb_false_iff. right. apply Z.ltb_ge. cbn [fst snd]. lia.
Qed.
End Cover.
End FPGEN1.

End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.

Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition kill_free (T : TSet) : Prop :=
forall tr, T tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Definition evs_kill_free (evs : list event) : Prop :=
forall sig fs, ~ In (KillEv sig fs) evs.

Lemma evs_kill_free_nil : evs_kill_free [].
Proof. intros sig fs H. exact H. Qed.

Lemma evs_kill_free_cons : forall e evs,
(forall sig fs, e <> KillEv sig fs) -> evs_kill_free evs -> evs_kill_free (e :: evs).
Proof.
intros e evs He Hevs sig fs [H | H]; [exact (He sig fs H) | exact (Hevs sig fs H)].
Qed.

Lemma evs_kill_free_app : forall a b,
evs_kill_free a -> evs_kill_free b -> evs_kill_free (a ++ b).
Proof.
intros a b Ha Hb sig fs H. apply in_app_or in H.
destruct H as [H | H]; [exact (Ha sig fs H) | exact (Hb sig fs H)].
Qed.

Lemma evs_kill_free_writes : forall ch (buf : list byte),
evs_kill_free (map (WriteEv ch) buf).
Proof.
intros ch buf sig fs H. apply in_map_iff in H. destruct H as (b & Hb & _). discriminate Hb.
Qed.

Lemma evs_kill_free_reads : forall ch (buf : list byte),
evs_kill_free (map (ReadEv ch) buf).
Proof.
intros ch buf sig fs H. apply in_map_iff in H. destruct H as (b & Hb & _). discriminate Hb.
Qed.

Lemma evs_kill_free_exit : forall code fs, evs_kill_free [ExitEv code fs].
Proof. intros code fs sig fs' [H | H]; [discriminate H | exact H]. Qed.

Lemma in_firstn_in : forall (A : Type) n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
intros A. induction n as [|n IH]; intros [|e l] x Hin; cbn in Hin; try contradiction.
destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH _ _ Hin)].
Qed.

Lemma evs_kill_free_firstn : forall n evs,
evs_kill_free evs -> evs_kill_free (firstn n evs).
Proof.
intros n evs H sig fs Hin. exact (H sig fs (in_firstn_in _ _ _ _ Hin)).
Qed.

Lemma is_prefix_in : forall (tr evs : list event) x,
is_prefix tr evs -> In x tr -> In x evs.
Proof.
induction tr as [|a tr IH]; intros evs x Hp Hin; [destruct Hin|].
destruct evs as [|b evs]; [cbn in Hp; contradiction|].
cbn in Hp. destruct Hp as [-> Hp].
destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH _ _ Hp Hin)].
Qed.

Lemma kill_free_nil : kill_free t_nil.
Proof. intros tr -> sig fs H. exact H. Qed.

Lemma kill_free_emit : forall evs T,
evs_kill_free evs -> kill_free T -> kill_free (t_emit evs T).
Proof.
intros evs T Hevs HT tr Htr sig fs Hin.
destruct Htr as [Hp | (tr' & -> & Htr')].
- exact (Hevs sig fs (is_prefix_in _ _ _ Hp Hin)).
- apply in_app_or in Hin. destruct Hin as [Hin | Hin];
[exact (Hevs sig fs Hin) | exact (HT tr' Htr' sig fs Hin)].
Qed.

Lemma kill_free_alt : forall (I : Type) (f : I -> TSet),
(forall i, kill_free (f i)) -> kill_free (t_alt f).
Proof. intros I f Hf tr (i & Hi). exact (Hf i tr Hi). Qed.

Lemma kill_free_alt2 : forall A B,
kill_free A -> kill_free B -> kill_free (t_alt2 A B).
Proof. intros A B HA HB tr [H | H]; [exact (HA tr H) | exact (HB tr H)]. Qed.

Lemma kill_free_exit : forall code fs, kill_free (t_exit code fs).
Proof. intros code fs. apply kill_free_emit; [apply evs_kill_free_exit | apply kill_free_nil]. Qed.

Lemma kill_free_write_ch : forall ch buf T,
kill_free T -> kill_free (t_write_ch ch buf T).
Proof.
intros ch buf T HT. unfold t_write_ch. apply kill_free_alt. intros i.
apply kill_free_emit; [| exact HT]. rewrite <- firstn_map. apply evs_kill_free_firstn, evs_kill_free_writes.
Qed.

Lemma kill_free_writes_pick : forall bufs T,
kill_free T -> kill_free (t_writes_pick bufs T).
Proof.
induction bufs as [|b bufs IH]; intros T HT; [exact HT|].
cbn. apply kill_free_write_ch, IH, HT.
Qed.

Lemma kill_free_writes_ch : forall ch bufs T,
kill_free T -> kill_free (t_writes_ch ch bufs T).
Proof.
induction bufs as [|b bufs IH]; intros T HT; [exact HT|].
cbn. apply kill_free_emit; [apply evs_kill_free_writes | apply IH, HT].
Qed.

Lemma kill_free_writes : forall bufs T,
kill_free T -> kill_free (t_writes bufs T).
Proof. intros. apply kill_free_writes_ch. assumption. Qed.

Lemma kill_free_t_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq HT tr Htr. apply HT. apply (proj2 (Heq tr)), Htr. Qed.

Lemma realizes_not_killed : forall segs pc ph sp brk0 mb rnd lim inp T,
realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
kill_free T ->
~ dies_by_signal (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp T Hrz Hkf (tr & sig & fs & Htr & Hin).
apply (realizes_traces_iff segs pc ph sp brk0 mb rnd lim inp T tr Hrz) in Htr.
exact (Hkf tr Htr sig fs Hin).
Qed.

Lemma realizes_error_free_unkilled : forall segs pc ph sp brk0 mb rnd lim inp T,
realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
kill_free T ->
error_free_unkilled (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros. split; [eapply realizes_error_free; eassumption | eapply realizes_not_killed; eassumption].
Qed.
