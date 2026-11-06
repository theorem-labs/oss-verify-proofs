(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0.

Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section Scaffold.

Variable segs : list Segment.

Variable ph : PhdrInfo.

Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.

Variable rnd : EntryDraw.

Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

#[using="Hsp_lo"] Lemma sp_lo_num : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. exact Hsp_lo. Qed.

#[using="Hsp_hi"] Lemma sp_hi_num : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Definition argcN : word := len_word av.

#[using="Hva"] Lemma u_argcN : bv_unsigned argcN = Z.of_nat (length av).
Proof.
pose proof (valid_argv_len av Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.

#[using="Hva Hve Hsp_hi"] Lemma bsb_nw :
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
Qed.

Definition envp_ptr : word :=
Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).

#[using="Hva Hsp_lo Hsp_hi"] Lemma envp_ptr_eq :
v_addi (v_add (Z_to_bv 64 (bv_unsigned sp + 8)) (v_slli argcN 3)) 8 = envp_ptr.
Proof.
pose proof sp_hi_num. pose proof sp_lo_num.
pose proof (valid_argv_len av Hva) as Hlen.
apply bv_eq. unfold envp_ptr, v_addi.
rewrite !Z_to_bv_unsigned.
rewrite v_add_small
by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
rewrite u_argcN; lia).
rewrite u_Z2bv by lia.
rewrite v_slli_3 by (rewrite u_argcN; lia).
rewrite u_argcN.
f_equal; lia.
Qed.

Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.

#[using="Type"] Lemma rdn_wmem_stack : forall (a : word) n,
(bv_unsigned sp <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn segs wmem a n
= rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) a n.
Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.

#[using="Hva Hve Hsp_hi"] Lemma read_argc_w :
rdn segs wmem sp 8%nat = Some (word_le8 argcN).
Proof.
pose proof sp_hi_num.
rewrite rdn_wmem_stack by lia.
apply read_argc. exact bsb_nw.
Qed.

#[using="Hva Hve Hsp_hi"] Lemma argv_ptr_bounds_at : forall k, (k < length av)%nat ->
(bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
(bv_unsigned (cat_argv_ptr sp av ev k)
+ Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
intros k Hk. apply argv_ptr_bounds; try assumption.
pose proof sp_hi_num. unfold argv_layout_slack. lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma read_argv_ptr_w : forall k, (k < length av)%nat ->
rdn segs wmem (sp + nat_to_word (8 + 8 * k)) 8%nat
= Some (word_le8 (cat_argv_ptr sp av ev k)).
Proof.
intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
pose proof (valid_argv_len av Hva) as Hal.
rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
Qed.

End Scaffold.
End FPGEN1.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition mkst_r (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (r : word)
: machine_state :=
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := None; ms_resv := Some r; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}.

#[using="Type"] Lemma mkst_r_svc : forall regs pc mem rom r, ms_svc_pending (mkst_r regs pc mem rom r) = None.
Proof. reflexivity. Qed.
End FPGEN1.

Ltac atomic_pipeline Hfetch Hecall Hdecode :=
unfold mkst_r;
step_pipeline Hfetch Hecall Hdecode;
cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
rewrite ?bv_eqb0_is_x0.

Ltac norm_pc_r :=
try lazymatch goal with
| |- QsRG.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
end.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma step_lr_w : forall segs regs pc mem rom w aq rl rd rs bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr AW aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod 4 = 0)%Z ->
rdn segs mem (getr regs rs) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
(v_addi pc 4) mem rom (getr regs rs)).
Proof.
intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite ov_rdn, Hread. cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_lr_d : forall segs regs pc mem rom w aq rl rd rs bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lr AD aq rl rd rs, 4%Z) ->
(bv_unsigned (getr regs rs) mod 8 = 0)%Z ->
rdn segs mem (getr regs rs) 8%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom (getr regs rs)).
Proof.
intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite ov_rdn, Hread. cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_sc_w_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc AW aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod 4 = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) 4%nat = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
subst r. rewrite Z.eqb_refl. cbv beta iota.
rewrite Hok. cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_sc_d_ok : forall segs regs pc mem rom w aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc AD aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod 8 = 0)%Z ->
r = getr regs rs1 ->
RiscvSemantics.store_ok segs mem (getr regs rs1) 8%nat = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
(wbytes mem (getr regs rs1) (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
subst r. rewrite Z.eqb_refl. cbv beta iota.
rewrite Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4.
unfold regupd, word_to_le_bytes.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_sc_fail : forall segs regs pc mem rom w wd aq rl rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 Hfetch Hecall Hdecode Hal.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite b_npc4. unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_sc_mismatch : forall segs regs pc mem rom w wd aq rl rd rs1 rs2 r,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs1) mod amo_bytes wd = 0)%Z ->
(bv_unsigned r =? bv_unsigned (getr regs rs1))%Z = false ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 1)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hne.
atomic_pipeline Hfetch Hecall Hdecode.
change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
unfold amo_bytes in Hal. rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
rewrite Hne. cbv beta iota.
rewrite b_npc4. unfold regupd.
destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

#[using="Type"] Lemma step_branch_tk_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.

#[using="Type"] Lemma step_branch_ft_r : forall segs regs pc mem rom r w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_bne_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
c_eq (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_bne_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
c_eq (getr regs rs1) (getr regs rs2) = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

#[using="Type"] Lemma step_beq_tk_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
c_eq (getr regs rs1) (getr regs rs2) = true ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (btgt pc (bv_signed imm)) mem rom r).
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_tk_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

#[using="Type"] Lemma step_beq_ft_r : forall segs regs pc mem rom r w rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
c_eq (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r regs (v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
apply (step_branch_ft_r segs regs pc mem rom r w BC_EQ rs1 rs2 imm Hf He Hd). exact Hc.
Qed.

#[using="Type"] Lemma step_opimm_r : forall segs regs pc mem rom r w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w op rd rs imm Hfetch Hecall Hdecode.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.

#[using="Type"] Lemma step_op_r : forall segs regs pc mem rom r w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step segs (mkst_r regs pc mem rom r) =
MachineOk (mkst_r (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom r).
Proof.
intros segs regs pc mem rom r w op rd rs1 rs2 Hfetch Hecall Hdecode.
atomic_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0. unfold regupd.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
End FPGEN2.

End Mq1.

Module Mq2.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0.

Import ListNotations.
Open Scope bv_scope.

Module HZ.
Local Open Scope Z_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.

Fixpoint zdig (ds : list Z) : Z :=
match ds with [] => 0 | d :: r => d + 256 * zdig r end.

#[using="Type"] Lemma pow2_8i_pos : forall i : nat, 0 < 2^(8 * Z.of_nat i).
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.

#[using="Type"] Lemma zb_bound : forall x i, 0 <= zb x i < 256.
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma zb_0 : forall i, zb 0 i = 0.
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.

#[using="Type"] Lemma land_land_m : forall a b m, Z.land (Z.land a b) m = Z.land (Z.land a m) (Z.land b m).
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

#[using="Type"] Lemma land_lxor_m : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
intros. apply Z.bits_inj'. intros n Hn.
rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

#[using="Type"] Lemma lxor_lt64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
0 <= Z.lxor a b < 2^64.
Proof.
intros a b Ha Hb.
assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
split; [lia|].
assert (E : Z.lxor a b mod 2^64 = Z.lxor a b).
{ rewrite <- Z.land_ones by lia. rewrite land_lxor_m.
rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

#[using="Type"] Lemma zb_alt : forall x i, zb x i = Z.land (Z.shiftr x (8 * Z.of_nat i)) 255.
Proof.
intros x i. unfold zb.
rewrite Z.shiftr_div_pow2 by lia.
change 255 with (Z.ones 8).
rewrite Z.land_ones by lia. reflexivity.
Qed.

#[using="Type"] Lemma zb_land : forall u w i, zb (Z.land u w) i = Z.land (zb u i) (zb w i).
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.

#[using="Type"] Lemma zb_lxor : forall u w i, zb (Z.lxor u w) i = Z.lxor (zb u i) (zb w i).
Proof.
intros u w i. rewrite !zb_alt.
rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.

#[using="Type"] Lemma zdig_nonneg : forall ds, Forall (fun d => 0 <= d < 256) ds -> 0 <= zdig ds.
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds). lia.
Qed.

#[using="Type"] Lemma zdig_lt : forall ds, Forall (fun d => 0 <= d < 256) ds ->
zdig ds < 2^(8 * Z.of_nat (length ds)).
Proof.
induction ds as [|d ds IH]; intro H; cbn [zdig length].
- cbn. lia.
- apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
specialize (IH Hds).
replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

#[using="Type"] Lemma zb_zdig : forall ds, Forall (fun d => 0 <= d < 256) ds ->
forall i, (i < length ds)%nat -> zb (zdig ds) i = nth i ds 0.
Proof.
induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
pose proof (zdig_nonneg ds Hds) as Hnn.
destruct i as [|i]; cbn [nth].
- cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
rewrite Z.div_1_r.
replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
- cbn [length] in Hi.
rewrite <- (IH Hds i ltac:(lia)).
cbn [zdig]. unfold zb.
replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
rewrite Z.div_add_l by lia.
rewrite (Z.div_small d 256) by lia. lia.
Qed.

#[using="Type"] Lemma zdig_recon8 : forall x, 0 <= x < 2^64 ->
x = zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7].
Proof.
intros x Hx. cbn [zdig]. unfold zb.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
change (2^0) with 1. rewrite Z.div_1_r.
change (2^8) with 256.
change (2^16) with (256*256).
change (2^24) with (256*256*256).
change (2^32) with (256*256*256*256).
change (2^40) with (256*256*256*256*256).
change (2^48) with (256*256*256*256*256*256).
change (2^56) with (256*256*256*256*256*256*256).
rewrite <- !Z.div_div by lia.
pose proof (Z.div_mod x 256 ltac:(lia)).
pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
{ rewrite !Z.div_div by lia. apply Z.div_small. lia. }
lia.
Qed.

#[using="Type"] Lemma zb_eq0 : forall x, 0 <= x < 2^64 ->
(forall i, (i < 8)%nat -> zb x i = 0) -> x = 0.
Proof.
intros x Hx H. rewrite (zdig_recon8 x Hx).
rewrite !H by lia. cbn [zdig]. lia.
Qed.

#[using="Type"] Lemma zb_neq0 : forall x i, zb x i <> 0 -> x <> 0.
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.

#[using="Type"] Lemma zb_split : forall lo hi i,
0 <= lo < 2^(8 * Z.of_nat i) -> 0 <= hi ->
zb (lo + 2^(8 * Z.of_nat i) * hi) i = hi mod 256.
Proof.
intros lo hi i Hlo Hhi. unfold zb.
rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
rewrite (Z.div_small lo) by lia. reflexivity.
Qed.

#[using="Type"] Lemma zb_mod64 : forall y i, (i < 8)%nat -> 0 <= y < 2^65 ->
zb (y mod 2^64) i = zb y i.
Proof.
intros y i Hi Hy.
destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
- rewrite Z.mod_small by lia. reflexivity.
- assert (Hm : y mod 2^64 = y - 2^64).
{ replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Hm. unfold zb.
pose proof (pow2_8i_pos i) as Hk.
assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
{ replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
apply Z.divide_factor_l. }
destruct Hdiv as [q Hq].
replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
by (rewrite Hd, Hq; lia).
rewrite Z.div_add by lia.
replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition ONESNEG : Z := 18374403900871474943.
Definition HIGHS   : Z := 9259542123273814144.
Definition ALLONES : Z := 18446744073709551615.

Definition Tz (x : Z) : Z :=
Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.

#[using="Type"] Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
intros a b Hb.
rewrite Z.land_comm.
pose proof (Z.sub_land_same_l b a) as H.
assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
lia.
Qed.

#[using="Type"] Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof. intros a b Ha. rewrite Z.land_comm. apply land_le_r. exact Ha. Qed.

#[using="Type"] Lemma Tz_range : forall x, 0 <= Tz x < 2^64.
Proof.
intro x. unfold Tz. split.
- apply Z.land_nonneg. right. unfold HIGHS. lia.
- pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.
End FPGEN1.

Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma zb_ALLONES : forall i, (i < 8)%nat -> zb ALLONES i = 255.
Proof. intros i Hi. by8 i. Qed.

#[using="Type"] Lemma zb_HIGHS : forall i, (i < 8)%nat -> zb HIGHS i = 128.
Proof. intros i Hi. by8 i. Qed.

#[using="Type"] Lemma Tz_byte : forall x i, (i < 8)%nat ->
zb (Tz x) i
= Z.land (Z.land (zb ((x + ONESNEG) mod 2^64) i) (Z.lxor (zb x i) 255)) 128.
Proof.
intros x i Hi. unfold Tz.
rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma byte_nozero : forall c, 1 <= c <= 255 ->
Z.land (Z.land (c - 1) (Z.lxor c 255)) 128 = 0.
Proof.
intros c Hc.
assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
assert (Hall : forallb (fun n =>
Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
(seq 1 255) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall _ Hin).
apply Z.eqb_eq in Hall.
replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.

#[using="Type"] Lemma Tz_nozero : forall x, 0 <= x < 2^64 ->
(forall i, (i < 8)%nat -> zb x i <> 0) -> Tz x = 0.
Proof.
intros x Hx Hnz.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
pose proof (zdig_recon8 x Hx) as Hrec.
set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
{ unfold ds'. repeat constructor; lia. }
assert (Hlt' : 0 <= zdig ds' < 2^64).
{ split; [apply zdig_nonneg; exact Hds'|].
pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
cbn [length] in H'. exact H'. }
assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
{ rewrite Hrec at 1.
replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
+ ONESNEG)
with (zdig ds' + 1 * 2^64)
by (unfold ds', ONESNEG; cbn [zdig]; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
apply zb_eq0; [apply Tz_range|].
intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.

#[using="Type"] Lemma zb_split_255 : forall v lo Q i p,
p = 2^(8 * Z.of_nat i) -> v = lo + p * (255 + 256 * Q) ->
0 <= lo < p -> 0 <= Q -> zb v i = 255.
Proof.
intros v lo Q i p Hp Hv Hlo HQ. subst p v.
rewrite zb_split by (try lia; assumption).
replace (255 + 256 * Q) with (255 + Q * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma sum_byte_255 : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
(forall j, (j < i)%nat -> zb x j <> 0) ->
zb (x + ONESNEG) i = 255.
Proof.
intros x i Hx Hi Hz Hlow.
pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
pose proof (zb_bound x 6). pose proof (zb_bound x 7).
pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
unfold ONESNEG.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
-
apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
[ vm_compute; reflexivity | lia | lia | lia ].
-
pose proof (Hlow 0%nat ltac:(lia)).
pose proof (Hlow 1%nat ltac:(lia)).
pose proof (Hlow 2%nat ltac:(lia)).
pose proof (Hlow 3%nat ltac:(lia)).
pose proof (Hlow 4%nat ltac:(lia)).
pose proof (Hlow 5%nat ltac:(lia)).
pose proof (Hlow 6%nat ltac:(lia)).
apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
[ vm_compute; reflexivity | lia | lia | lia ].
Qed.

#[using="Type"] Lemma Tz_haszero : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
(forall j, (j < i)%nat -> zb x j <> 0) -> Tz x <> 0.
Proof.
intros x i Hx Hi Hz Hlow.
apply (zb_neq0 _ i).
rewrite Tz_byte by exact Hi.
rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
vm_compute. discriminate.
Qed.
End FPGEN2.

End HZ.
Section FPGEN3.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma lor_shiftl8 : forall a y : Z, (0 <= a < 256)%Z -> (0 <= y)%Z ->
Z.lor a (Z.shiftl y 8) = (a + 256 * y)%Z.
Proof.
intros a y Ha Hy.
assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb n 8) eqn:E.
- apply Z.ltb_lt in E.
rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
- apply Z.ltb_ge in E.
replace (Z.testbit a n) with false; [reflexivity|].
symmetry. apply Z.testbit_false; [lia|].
rewrite Z.div_small; [reflexivity|].
split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
rewrite <- Z.lxor_lor by exact Hland.
rewrite <- Z.add_nocarry_lxor by exact Hland.
rewrite Hs. lia.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_zdig : forall bs : list byte,
bytes_le_to_Z bs = HZ.zdig (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
apply lor_shiftl8; [apply u8_range|].
apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
intros x _. apply u8_range.
Qed.

#[using="Type"] Lemma zb_of_bytes : forall (bs : list byte) i, (i < length bs)%nat ->
HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
intros bs i Hi. rewrite bytes_le_to_Z_zdig.
rewrite HZ.zb_zdig
by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
| rewrite length_map; exact Hi ]).
rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.

#[using="Type"] Lemma bytes_le_to_Z_range : forall bs : list byte, length bs = 8%nat ->
(0 <= bytes_le_to_Z bs < 2^64)%Z.
Proof.
intros bs Hl. rewrite bytes_le_to_Z_zdig.
assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
split; [apply HZ.zdig_nonneg; exact HF|].
pose proof (HZ.zdig_lt _ HF) as H.
rewrite length_map, Hl in H. exact H.
Qed.

#[using="Type"] Lemma v_haszero : forall v : word,
bv_unsigned
(v_and (v_and (v_add v (Z_to_bv 64 18374403900871474943))
(v_xori v (-1)))
(Z_to_bv 64 9259542123273814144))
= HZ.Tz (bv_unsigned v).
Proof.
intro v. pose proof (u64_range v) as Hv.
unfold v_and, v_add, v_xori, HZ.Tz, HZ.ONESNEG, HZ.HIGHS, HZ.ALLONES.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small 18374403900871474943 (2^64)) by lia.
rewrite (Z.mod_small 9259542123273814144 (2^64)) by lia.
replace ((-1) mod 2^64)%Z with 18446744073709551615%Z
by (vm_compute; reflexivity).
assert (Hx : (0 <= Z.lxor (bv_unsigned v) 18446744073709551615 < 2^64)%Z)
by (apply HZ.lxor_lt64; lia).
rewrite (Z.mod_small (Z.lxor (bv_unsigned v) 18446744073709551615)) by exact Hx.
assert (Hm : (0 <= (bv_unsigned v + 18374403900871474943) mod 2^64 < 2^64)%Z)
by (apply Z.mod_pos_bound; lia).
assert (Hz : (0 <= Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) < 2^64)%Z).
{ split; [apply Z.land_nonneg; left; lia|].
pose proof (HZ.land_le_l ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615) ltac:(lia)). lia. }
rewrite (Z.mod_small
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
(2^64)) by exact Hz.
apply Z.mod_small. split.
- apply Z.land_nonneg. right. lia.
- pose proof (HZ.land_le_r
(Z.land ((bv_unsigned v + 18374403900871474943) mod 2^64)
(Z.lxor (bv_unsigned v) 18446744073709551615))
9259542123273814144 ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma total_arg_bytes_firstn_S : forall (l : list (list byte)) k,
(k < length l)%nat ->
total_arg_bytes_nat (firstn (S k) l)
= (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; cbn [firstn nth].
- cbv [total_arg_bytes_nat]. cbn [firstn fold_right].
rewrite firstn_O. cbn [fold_right]. lia.
- rewrite !total_arg_bytes_cons. cbn [length] in Hk.
rewrite (IH k ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma bsb_len_lower : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
(cat_struct_size a e + total_arg_bytes_nat a + 16
<= length (build_stack_bytes ph sp a e uid hw rnd))%nat.
Proof.
intros ph sp a e uid hw rnd.
unfold build_stack_bytes, cat_struct_size. cbv zeta.
rewrite (string_addrs_pair a). cbv beta iota.
rewrite (string_addrs_pair e). cbv beta iota.
rewrite !length_app, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings, !repeat_length, length_at_random_bytes.
lia.
Qed.

#[using="Type"] Lemma bsb_word_k : forall ph (sp : word) a e k m uid hw rnd, (k < length a)%nat ->
(m <= length (nth k a []))%nat ->
exists pre post,
build_stack_bytes ph sp a e uid hw rnd = pre ++ post
/\ length pre = (cat_struct_size a e + total_arg_bytes_nat (firstn k a) + m)%nat
/\ (8 <= length post)%nat.
Proof.
intros ph sp a e k m uid hw rnd Hk Hm.
destruct (bsb_byte_k ph sp a e k uid hw rnd Hk) as [pre0 [post0 [E Hlen0]]].
pose proof (bsb_len_lower ph sp a e uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) a) as Hmono.
pose proof (total_arg_bytes_firstn_S a k Hk) as Hstep.
set (s1 := (nth k a [] ++ [Z_to_bv 8 0])) in *.
assert (Hs1 : length s1 = (length (nth k a []) + 1)%nat)
by (unfold s1; rewrite length_app; cbn [length]; lia).
assert (Hpost0 : (16 <= length post0)%nat).
{ assert (Hl : length (build_stack_bytes ph sp a e uid hw rnd)
= (length pre0 + length s1 + length post0)%nat)
by (rewrite E, !length_app; lia).
lia. }
exists (pre0 ++ firstn m s1), (skipn m s1 ++ post0).
split; [|split].
- rewrite E, <- !app_assoc. f_equal.
rewrite app_assoc, firstn_skipn. reflexivity.
- rewrite length_app, Hlen0, firstn_length_le by lia. lia.
- rewrite length_app, length_skipn. lia.
Qed.

#[using="Type"] Lemma read_word_stack : forall ph segs (sp : word) a e k m uid hw rnd,
(k < length a)%nat -> (m <= length (nth k a []))%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) < 2^64)%Z ->
exists bs, length bs = 8%nat /\
rdn segs (stack_to_mem sp (entry_stack_image ph sp a e uid hw rnd))
(cat_argv_ptr sp a e k + nat_to_word m) 8%nat = Some bs.
Proof.
intros ph segs sp a e k m uid hw rnd Hk Hm Hnw.
destruct (bsb_word_k ph sp a e k m uid hw rnd Hk Hm) as [pre [post [E [Hlen Hpost]]]].
exists (firstn 8 post). split; [apply firstn_length_le; lia|].
replace (cat_argv_ptr sp a e k + nat_to_word m)
with (sp + nat_to_word (length pre)).
2:{ rewrite Hlen, (cat_argv_ptr_offset sp a e k Hk). unfold cat_string_base.
rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
apply (read_at_offset_image segs ph sp a e uid hw rnd
pre (firstn 8 post) (skipn 8 post) 8%nat).
- rewrite E. f_equal. symmetry. apply firstn_skipn.
- apply firstn_length_le. lia.
- exact Hnw.
Qed.

#[using="Type"] Lemma word_bytes_nth :
forall segs (mem : word -> option byte) (ptr : word) (s : list byte) m bs j,
rdn segs mem (ptr + nat_to_word m) 8%nat = Some bs ->
(forall i, (i <= length s)%nat ->
rdn segs mem (ptr + nat_to_word i) 1%nat = Some [byte_at s i]) ->
(j < 8)%nat -> (m + j <= length s)%nat ->
nth j bs (Z_to_bv 8 0) = byte_at s (m + j).
Proof.
intros segs mem ptr s m bs j Hr Hb Hj Hmj.
pose proof (rdn_nth segs mem 8%nat _ bs j Hr Hj) as H1.
rewrite nat_to_word_add_merge in H1.
rewrite (Hb (m + j)%nat Hmj) in H1.
congruence.
Qed.

Section ArgvWord.

Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.

Variable rnd : EntryDraw.

Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

#[using="Hsp_lo"] Lemma mstr_sp_lo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. exact Hsp_lo. Qed.

#[using="Hsp_hi"] Lemma mstr_sp_hi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

#[using="Hva Hve Hsp_hi"] Lemma mstr_bsb_nw :
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z.
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof mstr_sp_hi. lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma argv_ptr_room : forall k, (k < length av)%nat ->
(bv_unsigned (cat_argv_ptr sp av ev k)
+ Z.of_nat (length (nth k av [])) + 17
<= bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)))%Z.
Proof.
intros k Hk.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
pose proof mstr_bsb_nw as Hnw.
pose proof (bsb_len_lower ph sp av ev uid hw rnd) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk) as Hstep.
assert (Hptr : cat_argv_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
rewrite Hptr, word_add_nat, u_Z2bv by lia. lia.
Qed.

#[using="Hva Hve Hsp_hi"] Lemma mstr_argv_ptr_bounds : forall k, (k < length av)%nat ->
(bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
(bv_unsigned (cat_argv_ptr sp av ev k)
+ Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
intros k Hk. apply argv_ptr_bounds; try assumption.
pose proof mstr_sp_hi. unfold argv_layout_slack. lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma argv_word_readable : forall k m,
(k < length av)%nat -> (m <= length (nth k av []))%nat ->
exists bs, length bs = 8%nat /\
rdn segs (wrap_mem ph sp av ev uid hw rnd)
(cat_argv_ptr sp av ev k + nat_to_word m) 8%nat = Some bs.
Proof.
intros k m Hk Hm.
pose proof mstr_sp_lo. pose proof mstr_sp_hi.
destruct (mstr_argv_ptr_bounds k Hk) as [Hge Hup].
pose proof (argv_ptr_room k Hk) as Hroom.
pose proof mstr_bsb_nw as Hnw.
pose proof (u64_range (cat_argv_ptr sp av ev k)).
assert (Hu : bv_unsigned (cat_argv_ptr sp av ev k + nat_to_word m)
= (bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat m)%Z)
by (rewrite word_add_nat; apply u_Z2bv; lia).
destruct (read_word_stack ph segs sp av ev k m uid hw rnd Hk Hm Hnw) as [bs [Hl Hr]].
exists bs. split; [exact Hl|].
rewrite rdn_wrap_stack_above by (rewrite Hu; lia).
exact Hr.
Qed.

End ArgvWord.
End FPGEN3.

End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh Q5Zm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QsRG.Mq0 Qnhz.Mq0 QEVk.Mq0 QiVh.Mq0 QiVh Q5Zm.
Import ListNotations.
Local Open Scope Z_scope.

Definition mem_grows (m m' : word -> option byte) : Prop :=
forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

Lemma wview_grows : forall segs m m' x,
mem_grows m m' ->
wview segs m x <> None -> wview segs m' x <> None.
Proof.
intros segs m m' x Hg Hx. unfold wview in *.
destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
destruct (m x) as [b|] eqn:Hm.
- exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
- exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
mem_grows m m' ->
store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
cbn [store_ok] in *.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (wview segs m' a) as [b'|] eqn:Hv'.
- apply (IH m m'); assumption.
- exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [wbytes]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
intros zs m x Hx. unfold apply_zeros.
destruct zs as [|z zs']; [exact Hx|].
destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
intros m b l x Hx. unfold zmem.
destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
cbn [write_to_mem]. apply IH.
destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
induction ws as [|w ws' IH]; intros m x Hx.
- exact Hx.
- destruct w as [a bs]. cbn [apply_writes].
apply IH. apply write_to_mem_grows. exact Hx.
Qed.

Lemma store_ok_of_all : forall segs n m a,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
wview segs m x <> None) ->
store_ok segs m a n = true.
Proof.
intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
cbn [store_ok].
destruct (wview segs m a) as [b|] eqn:Hv.
2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }

destruct n as [|n']; [reflexivity|].
rewrite Nat2Z.inj_succ in Hnw.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
apply IH.
- rewrite Hu1. lia.
- intros x Hx. rewrite Hu1 in Hx. apply Hall.
rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma wrap_mem_window_defined : forall ph sp argv envp (x : word) uid hw rnd,
bv_unsigned sp - stack_max_size <= bv_unsigned x ->
bv_unsigned x < bv_unsigned sp ->
wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
[discriminate|].
rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
cbn. discriminate.
Qed.

Lemma store_ok_wrap_window : forall segs ph sp argv envp a n uid hw rnd,
bv_unsigned sp - stack_max_size <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true.
Proof.
intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

Lemma store_ok_zeros_hit : forall segs m zs a n,
zs <> [] ->
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
zeros_cover zs x = true) ->
store_ok segs (apply_zeros m zs) a n = true.
Proof.
intros segs m zs a n Hne Hnw Hcov.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, apply_zeros.
destruct zs as [|z zs']; [contradiction|].
rewrite (Hcov x Hx). discriminate.
Qed.

Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
store_ok segs (zmem m b l) a n = true.
Proof.
intros segs m b l a n Hnw Hlo Hhi.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview, zmem.
rewrite (proj2 (Z.leb_le _ _)) by lia.
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
cbn. discriminate.
Qed.

Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
(b l : word) : Prop :=
forall (a : word) (n : nat),
bv_unsigned b <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
store_ok segs m a n = true.

Lemma store_grant_zmem : forall segs m b l,
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
store_grant_ok segs (zmem m b l) b l.
Proof.
intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

Lemma store_grant_zmem_prefix : forall segs m b logical physical,
(bv_unsigned logical <= bv_unsigned physical)%Z ->
(bv_unsigned b + bv_unsigned physical <= 2 ^ 64)%Z ->
store_grant_ok segs (zmem m b physical) b logical.
Proof.
intros segs m b logical physical Hle Hnw a n Hlo Hhi.
apply store_ok_zmem; lia.
Qed.

Lemma store_grant_mono : forall segs m m' b l,
mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
intros segs m m' b l Hg H a n Hlo Hhi.
eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

Lemma store_ok_seg_writable : forall segs m a n,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
exists seg,
find_segment segs (bv_unsigned x) 1 = Some seg /\
seg_writable seg = true /\
segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned x - Z.of_N (seg_base seg))) <> None) ->
store_ok segs m a n = true.
Proof.
intros segs m a n Hnw Hall.
apply store_ok_of_all; [exact Hnw|].
intros x Hx. unfold wview.
destruct (m x) as [b|]; [discriminate|].
destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
rewrite Hfind, Hw. exact Hb.
Qed.

Lemma store_ok_wseg : forall segs m a n,
wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
cbn [wseg_ok] in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_true_iff in H as [H Hrec].
apply andb_true_iff in H as [Hwr Hbyte].
destruct (segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
[|discriminate].
cbn [store_ok]. unfold wview at 1.
destruct (m a) as [b0|]; [apply IH, Hrec|].
rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

Lemma store_ok_all : forall segs m n a,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
store_ok segs m a n = true ->
forall x : word,
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
wview segs m x <> None.
Proof.
intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
[cbn in Hx; lia|].
cbn [store_ok] in H.
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
rewrite Nat2Z.inj_succ in Hnw, Hx.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
{ assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Hv. discriminate. }

assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).

eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
store_ok segs m lo N = true ->
bv_unsigned lo <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
store_ok segs m a n = true.
Proof.
intros segs m lo a N n Hnw Hok Hl Hh.
apply store_ok_of_all; [lia|].
intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
bv_unsigned lo = base ->
base + Z.of_nat N = hi ->
hi <= 2 ^ 64 ->
wseg_ok segs lo N = true ->
base <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= hi ->
store_ok segs m a n = true.
Proof.
intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

Lemma store_ok_read_aux : forall segs m n (a : word),
store_ok segs m a n = true ->
exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
intros segs m n; induction n as [|n IH]; intros a H.
- exists []. reflexivity.
- cbn [store_ok] in H. cbn [read_bytes_aux].
destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : forall segs ms (buf cnt : word),
store_ok segs (ms_mem ms) buf (word_to_nat cnt) = true ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms buf cnt H.
rewrite read_bytes_map_eq. unfold ms_writable_byte.
apply store_ok_read_aux. exact H.
Qed.

Lemma of_nat_word_to_nat : forall w : word,
Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

Lemma store_grant_wbuf : forall segs ms (b l buf cnt : word),
store_grant_ok segs (ms_mem ms) b l ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms b l buf cnt Hg Hlo Hhi.
apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

Lemma heap_rg_wbuf : forall segs ms (b l buf cnt : word) (cur : Z),
store_grant_ok segs (ms_mem ms) b l ->
cur <= bv_unsigned b + bv_unsigned l - bv_unsigned b ->
covers (heap_rg b cur) buf (word_to_nat cnt) ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms b l buf cnt cur Hg Hcur Hc.
destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
rewrite of_nat_word_to_nat in Hhi.
eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.

Lemma zmem_wbuf : forall segs ms m (b l buf cnt : word),
mem_grows (zmem m b l) (ms_mem ms) ->
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
ms_mem ms = wbytes (zmem m b l) a bs ->
bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
bv_unsigned b <= bv_unsigned buf ->
bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
eapply zmem_wbuf;
[ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

Ltac store_ok_peel :=
repeat first
[ eapply store_ok_mono; [apply wbytes_grows|]
| eapply store_ok_mono; [apply write_to_mem_grows|]
| eapply store_ok_mono; [apply apply_zeros_grows|]
| eapply store_ok_mono; [apply apply_writes_grows|] ].

Ltac store_ok_base :=
first
[ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
| eapply store_ok_zeros_hit;
[ discriminate | u_norm; lia | intros; u_norm; lia ]
| apply store_ok_zmem; u_norm; lia ].

Ltac solve_store_ok :=
store_ok_peel;
first [ store_ok_base
| eapply store_ok_mono; [apply zmem_grows|];
store_ok_peel; store_ok_base ].

Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
first [ solve_store_ok
| store_ok_peel;
eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

Ltac solve_mem_grows :=
repeat first
[ solve [ eauto with store_ok_db ]
| apply mem_grows_refl
| eapply mem_grows_trans; [ | apply wbytes_grows ]
| eapply mem_grows_trans; [ | apply zmem_grows ]
| eapply mem_grows_trans; [ | apply write_to_mem_grows ]
| eapply mem_grows_trans; [ | apply apply_zeros_grows ]
| eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0.
Import ListNotations.
Open Scope bv_scope.

Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

Ltac getr_proof X r :=
lazymatch X with
| regupd ?Y ?rd ?v =>
match tt with
| _ => let chk := match tt with _ => constr_eq rd r end in
uconstr:(getr_same Y r v (reg_neq_of_eqb r (0%bv) (@eq_refl bool false)))
| _ => let p := getr_proof Y r in
uconstr:(eq_trans (getr_other Y rd v r (reg_neq_of_eqb r rd (@eq_refl bool false))) p)
end
| _ => uconstr:(@eq_refl word (getr X r))
end.

Ltac gres :=
repeat match goal with
| |- context [getr ?X ?r] =>
lazymatch X with regupd _ _ _ => idtac end;
let p := getr_proof X r in
let p' := constr:(p) in rewrite p'
end;
match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Ltac is_pos_lit p :=
lazymatch p with
| xH => idtac
| xO ?q => is_pos_lit q
| xI ?q => is_pos_lit q
end.
Ltac is_Z_lit z :=
lazymatch z with
| Z0 => idtac
| Zpos ?p => is_pos_lit p
| Zneg ?p => is_pos_lit p
end.

Ltac val_lit v :=
lazymatch v with
| Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
| @BV _ _ _ => fail
| _ => wlit_closed v
end.

Ltac vals_lit :=
repeat match goal with
| |- context [regupd _ _ ?v] => val_lit v
end.

Ltac vnorm :=
gres; imm_norm;
match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
vals_lit.

Ltac stepn F D :=
lazymatch type of D with
| decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
| _ => stepi F D; vnorm
end.

Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

Ltac stepb_tk F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
| decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
| decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
| decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
| decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
| decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
end;
[ exact F | reflexivity | exact D | gres; imm_norm; tac ]
| step_simpl; vnorm ].

Ltac cond_compute :=
idtac;
lazymatch goal with
| |- ?g => check_closed_term g; vm_compute; reflexivity
end.

Ltac stepb F D :=
first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

Ltac stepret F D k tac :=
stepjr F D k ltac:(gres; tac);
imm_norm;
try lazymatch goal with
| Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
| Hk : v_jalr k 0 = k |- _ => rewrite Hk
end;
try (wlit (v_jalr k 0)).

Ltac stepsd F D aa vv oktac :=
chain_step;
[ reflexivity
| eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
| gres; first [ reflexivity | assumption | symmetry; assumption ]
| oktac ]
| step_simpl ].

Ltac stepld F D vv rtac :=
chain_step;
[ reflexivity
| eapply step_ld with (v := vv);
[ exact F | reflexivity | exact D
| gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
| first [ apply bytes_le_to_Z_8 | reflexivity ] ]
| step_simpl; vnorm ].
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq1.

Import ListNotations.
Open Scope bv_scope.

Lemma is_prefix_app_r {A} : forall (l m a : list A),
is_prefix a l -> is_prefix a (l ++ m).
Proof.
induction l as [|x l IH]; intros m a H.
- destruct a; [apply is_prefix_nil | cbn in H; contradiction].
- destruct a as [|y a]; cbn in *; [exact I|].
destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
is_prefix b (l ++ a) ->
is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
induction l as [|x l IH]; intros a b H.
- right. exists b. split; [reflexivity | exact H].
- destruct b as [|y b]; cbn in H; [left; exact I|].
destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
+ left. cbn. split; [reflexivity | exact Hp].
+ right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

Definition t_nil : TSet := fun tr => tr = [].

Definition t_emit (evs : list event) (T : TSet) : TSet :=
fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
t_emit [ExitEv code fs] t_nil.

Definition wr_index (buf : list byte) : Type :=
{n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
: wr_index buf :=
exist _ (length buf) (conj Hnb (Nat.le_refl _)).

Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
t_alt (fun i : wr_index buf =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
intros T H0 tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)];
[apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
- intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_pick_cons : forall buf bufs T,
t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_cons : forall buf bufs T,
t_writes (buf :: bufs) T
= t_emit (map (WriteEv (Z_to_bv 64 1)) buf) (t_writes bufs T).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : forall ch buf bufs T,
t_writes_ch ch (buf :: bufs) T
= t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.

Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
t_writes_ch ch bufs (t_exit code fs) [].
Proof.
intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
apply t_emit_has_nil.
Qed.

Lemma t_writes_ch_exit_iff : forall ch bufs code fs tr,
t_writes_ch ch bufs (t_exit code fs) tr
<-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code fs]).
Proof.
intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
- cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
+ intro H. left. exact H.
- rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
unfold t_emit at 1. split.
+ intros [H | (tr' & -> & Hc)].
* apply is_prefix_app_r; exact H.
* apply is_prefix_app_mono. apply IH. exact Hc.
+ intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
* left; exact H.
* right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.

Lemma t_writes_exit_iff : forall bufs code fs tr,
t_writes bufs (t_exit code fs) tr
<-> is_prefix tr (wevents bufs ++ [ExitEv code fs]).
Proof.
intros bufs code fs tr. unfold t_writes.
rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.

Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
T [] -> (1 <= length rest)%nat ->
t_eq (t_alt (fun i : wr_index rest =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
(t_emit (map (WriteEv ch) rest) T).
Proof.
intros ch rest T HT Hnb tr. split.
- intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [Hp | (tr1 & -> & Hi)].
+ left. eapply is_prefix_trans; [exact Hp|].
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_r. apply is_prefix_refl.
+ destruct Hi as [Hp | (tr2 & -> & Ht)].
* left.
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_mono. exact Hp.
* right. exists tr2. split; [|exact Ht].
rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
- intros [Hp | (tr' & -> & Ht)].
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all. left. exact Hp.
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all, skipn_all. right.
exists tr'. split; [reflexivity|].
cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

Lemma t_writes_ch_pick_exit_iff : forall ch bufs code fs tr,
Forall (fun b => (1 <= length b)%nat) bufs ->
(fold_right (t_write_ch ch) (t_exit code fs) bufs tr
<-> exists full, wpick ch bufs full /\
is_prefix tr (full ++ [ExitEv code fs])).
Proof.
intros ch bufs code fs tr Hall; revert tr;
induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
- cbn [fold_right]. unfold t_exit, t_emit, t_nil.
split.
+ intros [H | (tr' & -> & ->)].
* exists []. split; [apply wp_nil | exact H].
* exists []. split; [apply wp_nil|].
rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
+ intros (full & Hw & Hp). inversion Hw; subst full.
left. exact Hp.
- cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
split.
+ intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [H | (tr' & -> & Hc)].
* exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
rewrite <- app_assoc.
eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
* apply IH in Hc. destruct Hc as (full & Hw & Hp).
exists (map (WriteEv ch) (firstn n buf) ++ full).
split; [apply wp_cons; assumption|].
rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
+ intros (full & Hw & Hp).
inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
rewrite <- app_assoc in Hp.
apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
* exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
exists tr'. split; [reflexivity|].
apply IH. exists tr0. split; assumption.
Qed.

Lemma t_writes_pick_exit_iff : forall bufs code fs tr,
Forall (fun b => (1 <= length b)%nat) bufs ->
(t_writes_pick bufs (t_exit code fs) tr
<-> exists full, wpick (Z_to_bv 64 1) bufs full /\
is_prefix tr (full ++ [ExitEv code fs])).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.

Lemma two_traces_t_alt2 : forall bf cf bs cs fs tr,
t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
<-> Qn1e.Mq1.two_traces bf cf bs cs fs tr.
Proof.
intros. unfold t_alt2, Qn1e.Mq1.two_traces.
rewrite !t_writes_exit_iff. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition node_ok (c : config) (I : Type)
(evs : I -> list event) (nx : I -> config) : Prop :=
(forall i, sstep_cfg segs (alloc_only_cfg false) c (evs i) (SNext (nx i)))
/\ (forall e st, sstep_cfg segs (alloc_only_cfg false) c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Inductive dpath : config -> config -> Prop :=
| dpath_refl : forall c, dpath c c
| dpath_step : forall c c1 c2,
node_ok c unit (fun _ => []) (fun _ => c1) ->
dpath c1 c2 ->
dpath c c2.

#[using="Type"] Lemma dpath_trans : forall c1 c2 c3, dpath c1 c2 -> dpath c2 c3 -> dpath c1 c3.
Proof.
intros c1 c2 c3 H12 H23; induction H12 as [c | c c' c'' Hn Hd IH]; [exact H23|].
eapply dpath_step; [exact Hn | apply IH; exact H23].
Qed.

#[using="Type"] Lemma dpath_star : forall c1 c2, dpath c1 c2 -> star_cfg segs (alloc_only_cfg false) c1 [] c2.
Proof.
intros c1 c2 H; induction H as [c | c c' c'' [Hc _] Hd IH]; [apply star_cfg_refl|].
change ([] : list event) with ([] ++ [] : list event).
eapply star_cfg_step; [apply (Hc tt) | exact IH].
Qed.

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok c I evs nx ->
(forall i, realizes (nx i) (T i)) ->
realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
m_halted (cfg_model c) <> None ->
realizes c t_nil
| rz_conseq : forall c T T',
realizes c T -> t_eq T T' -> realizes c T'
| rz_loop : forall (V : config -> Prop) (T : TSet) (c c_e : config),
V c ->
(forall c', V c' -> lbody V T c') ->
star_cfg segs (alloc_only_cfg false) c [] c_e ->
realizes c_e T ->
realizes c T
with lbody : (config -> Prop) -> TSet -> config -> Prop :=
| lb_exit : forall (V : config -> Prop) (T : TSet) c,
realizes c T -> lbody V T c
| lb_node : forall (V : config -> Prop) (T : TSet) c (I : Type) (nx : I -> config)
(k : I -> bool),
node_ok c I (fun _ => []) nx ->
(forall i, k i = true -> lbody V T (nx i)) ->
(forall i, k i = false -> V (nx i)) ->
lbody V T c.

Scheme realizes_mutind := Induction for realizes Sort Prop
with lbody_mutind := Induction for lbody Sort Prop.
Combined Scheme realizes_lbody_mutind from realizes_mutind, lbody_mutind.

#[using="Type"] Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
- exact IHe.
Qed.

#[using="Type"] Lemma realizes_pclosed : forall c T, realizes c T ->
forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
- eapply IHe; eauto.
Qed.

Inductive starn : nat -> config -> list event -> config -> Prop :=
| starn_refl : forall c, starn O c [] c
| starn_step : forall n c1 evs c2 tr c3,
sstep_cfg segs (alloc_only_cfg false) c1 evs (SNext c2) ->
starn n c2 tr c3 ->
starn (S n) c1 (evs ++ tr) c3.

#[using="Type"] Lemma star_starn : forall c tr c', star_cfg segs (alloc_only_cfg false) c tr c' -> exists n, starn n c tr c'.
Proof.
intros c tr c' H; induction H as [c | c1 evs c2 tr c3 Hss Hstar (n & IH)].
- exists O. apply starn_refl.
- exists (S n). eapply starn_step; eauto.
Qed.

#[using="Type"] Lemma starn_star : forall n c tr c', starn n c tr c' -> star_cfg segs (alloc_only_cfg false) c tr c'.
Proof.
intros n c tr c' H; induction H as [c | n c1 evs c2 tr c3 Hss Hstar IH].
- apply star_cfg_refl.
- eapply star_cfg_step; eauto.
Qed.

#[local] Definition P_lb_sound (V : config -> Prop) (T : TSet) (c : config) : Prop :=
forall n : nat,
T [] ->
(forall c'' m tr c', V c'' -> (m < n)%nat -> starn m c'' tr c' -> T tr) ->
forall m tr c', (m <= n)%nat -> starn m c tr c' -> T tr.

#[using="Type"] Lemma realizes_lbody_sound :
(forall c T, realizes c T -> forall n tr c', starn n c tr c' -> T tr)
/\ (forall V T c, lbody V T c -> P_lb_sound V T c).
Proof.
apply realizes_lbody_mutind.
-
intros c I evs nx T i0 Hnode Hcont IH n tr c' Hstar.
inversion Hstar as [|m c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
-
intros c Hh n tr c' Hstar.
destruct (star_halted_nil segs c tr c' Hh (star_cfg_sub segs _ _ _ _ (starn_star _ _ _ _ Hstar))) as [-> _]. reflexivity.
-
intros c T T' H IH Heq n tr c' Hstar. apply Heq. eapply IH; exact Hstar.
-
intros V T c c_e HV Hbody IHbody Hw He IHe n.
assert (HT0 : T []) by (apply (IHe O [] c_e); apply starn_refl).
enough (HQ : forall n c0, V c0 -> forall tr c', starn n c0 tr c' -> T tr)
by (intros tr c' Hs; exact (HQ n c HV tr c' Hs)).
clear n. intros n.
induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf).
intros c0 HV0 tr c' Hstar.
refine (IHbody c0 HV0 n HT0 _ n tr c' (Nat.le_refl n) Hstar).
intros c'' m tr2 c2 HV'' Hm Hs. exact (IHn m Hm c'' HV'' tr2 c2 Hs).
-
intros V T c H IH n _ _ m tr c' _ Hstar. eapply IH; exact Hstar.
-
intros V T c I nx k Hnode Hk IHk HV n HT0 Hlt m tr c' Hm Hstar.
inversion Hstar as [|m' c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exact HT0.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2. cbn [app].
destruct (k i) eqn:Hki.
* refine (IHk i Hki n HT0 Hlt m' tr2 c' _ Hstar2). lia.
* apply (Hlt (nx i) m' tr2 c' (HV i Hki)); [lia | exact Hstar2].
Qed.

#[using="Type"] Lemma realizes_star_only : forall c T, realizes c T ->
forall tr c', star_cfg segs (alloc_only_cfg false) c tr c' -> T tr.
Proof.
intros c T H tr c' Hstar. destruct (star_starn _ _ _ Hstar) as (n & Hn).
eapply (proj1 realizes_lbody_sound); eauto.
Qed.

#[using="Type"] Lemma star_cfg_one : forall c evs c',
sstep_cfg segs (alloc_only_cfg false) c evs (SNext c') -> star_cfg segs (alloc_only_cfg false) c evs c'.
Proof. intros c evs c' H. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact H | apply star_cfg_refl]. Qed.

#[using="Type"] Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
star_cfg segs (alloc_only_cfg false) c1 t1 c2 -> star_cfg segs (alloc_only_cfg false) c2 t2 c3 ->
star_cfg segs (alloc_only_cfg false) c1 (t1 ++ t2) c3.
Proof.
intros c1 t1 c2 t2 c3 H1; revert t2 c3.
induction H1 as [c | c1 evs c2 tr c3' Hss Hs IH]; intros t2 c4 H2; [exact H2|].
rewrite <- app_assoc. eapply star_cfg_step; [exact Hss | apply IH; exact H2].
Qed.

#[using="Type"] Lemma realizes_admits : forall c T, realizes c T ->
forall tr, T tr -> obs_trace_cfg segs (alloc_only_cfg false) c tr.
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq
| V T c c_e HV Hbody Hw He IHe];
intros tr HT.
- destruct Hnode as [Hcomp _].
destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
+ exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
+ destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
exists (evs i ++ tr''), c''.
split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
- unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
- apply IH. apply Heq. exact HT.
- destruct (IHe tr HT) as (tr'' & c'' & Hstar & Hp).
exists tr'', c''. split; [| exact Hp].
change tr'' with ([] ++ tr''). eapply star_cfg_trans; [exact Hw | exact Hstar].
Qed.

#[using="Type"] Theorem realizes_obs_iff : forall c T, realizes c T ->
forall tr, obs_trace_cfg segs (alloc_only_cfg false) c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
- apply realizes_admits; exact H.
Qed.

#[using="Type"] Lemma sstep_halted_none : forall c e st,
sstep_cfg segs (alloc_only_cfg false) c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Definition rz_path (c : config) : Prop :=
(exists T, realizes c T)
\/ (exists V T, (forall c', V c' -> lbody V T c') /\ lbody V T c).

#[using="Type"] Lemma realizes_lbody_step :
(forall c T, realizes c T -> forall e c', sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> rz_path c')
/\ (forall V T c, lbody V T c ->
(forall c', V c' -> lbody V T c') ->
forall e c', sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> rz_path c').
Proof.
apply realizes_lbody_mutind.
- intros c I evs nx T i0 Hnode Hcont IH e c' Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. left. exists (T i). apply Hcont.
- intros c Hh e c' Hss. exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
- intros c T T' H IH Heq e c' Hss. eapply IH; exact Hss.
- intros V T c c_e HV Hbody IHbody Hw He IHe e c' Hss.
eapply (IHbody c HV Hbody); exact Hss.
- intros V T c H IH _ e c' Hss. eapply IH; exact Hss.
- intros V T c I nx k Hnode Hk IHk HV Hbody e c' Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. right. exists V, T. split; [exact Hbody|].
destruct (k i) eqn:Hki.
+ apply Hk. exact Hki.
+ apply Hbody. apply HV. exact Hki.
Qed.

#[using="Type"] Lemma realizes_lbody_no_sserror :
(forall c T, realizes c T -> forall e, ~ sstep_cfg segs (alloc_only_cfg false) c e SError)
/\ (forall V T c, lbody V T c -> forall e, ~ sstep_cfg segs (alloc_only_cfg false) c e SError).
Proof.
apply realizes_lbody_mutind.
- intros c I evs nx T i0 Hnode Hcont IH e Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- intros c Hh e Hss. apply Hh. eapply sstep_halted_none; exact Hss.
- intros c T T' H IH Heq e Hss. eapply IH; exact Hss.
- intros V T c c_e HV Hbody IHbody Hw He IHe e Hss. eapply (IHbody c HV); exact Hss.
- intros V T c H IH e Hss. eapply IH; exact Hss.
- intros V T c I nx k Hnode Hk IHk HV e Hss.
destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
Qed.

#[using="Type"] Lemma realizes_step : forall c T e c',
realizes c T -> sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> rz_path c'.
Proof. intros c T e c' H Hss. eapply (proj1 realizes_lbody_step); eauto. Qed.

#[using="Type"] Lemma realizes_no_sserror : forall c T e,
realizes c T -> ~ sstep_cfg segs (alloc_only_cfg false) c e SError.
Proof. intros c T e H. eapply (proj1 realizes_lbody_no_sserror); eauto. Qed.

#[using="Type"] Lemma inv_no_reaches_error_cfg : forall (P : config -> Prop),
(forall c e c', P c -> sstep_cfg segs (alloc_only_cfg false) c e (SNext c') -> P c') ->
(forall c e, P c -> ~ sstep_cfg segs (alloc_only_cfg false) c e SError) ->
forall c0, P c0 -> ~ reaches_error_cfg segs (alloc_only_cfg false) c0.
Proof.
intros P Hstep Herr c0 H0 (tr & c & evs & Hs & He). revert H0 He.
induction Hs as [c | c1 evs1 c2 tr c3 Hss Hs IH]; intros H0 He.
- exact (Herr c evs H0 He).
- exact (IH (Hstep _ _ _ H0 Hss) He).
Qed.

#[using="Type"] Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs (alloc_only_cfg false) c.
Proof.
intros c T H.
apply (inv_no_reaches_error_cfg rz_path).
- intros c1 e c2 [(T1 & H1) | (V & T1 & Hb & Hl)] Hss.
+ eapply realizes_step; eauto.
+ eapply (proj2 realizes_lbody_step); eauto.
- intros c1 e [(T1 & H1) | (V & T1 & Hb & Hl)] Hss.
+ eapply realizes_no_sserror; eauto.
+ eapply (proj2 realizes_lbody_no_sserror); eauto.
- left. exists T; exact H.
Qed.

#[using="Type"] Theorem lbody_no_error : forall V T c,
(forall c', V c' -> lbody V T c') -> lbody V T c -> ~ reaches_error_cfg segs (alloc_only_cfg false) c.
Proof.
intros V T c Hb Hl.
apply (inv_no_reaches_error_cfg rz_path).
- intros c1 e c2 [(T1 & H1) | (V' & T1 & Hb' & Hl')] Hss.
+ eapply realizes_step; eauto.
+ eapply (proj2 realizes_lbody_step); eauto.
- intros c1 e [(T1 & H1) | (V' & T1 & Hb' & Hl')] Hss.
+ eapply realizes_no_sserror; eauto.
+ eapply (proj2 realizes_lbody_no_sserror); eauto.
- right. exists V, T. split; assumption.
Qed.
#[using="Type"] Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

#[using="Type"] Lemma rz_silent1 : forall c c' T,
node_ok c unit (fun _ => []) (fun _ => c') ->
realizes c' T ->
realizes c T.
Proof.
intros c c' T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

#[using="Type"] Lemma rz_dpath : forall c c' T, dpath c c' -> realizes c' T -> realizes c T.
Proof.
intros c c' T Hd; induction Hd as [c | c c1 c2 Hn Hd IH]; intros Hc; [exact Hc|].
eapply rz_silent1; [exact Hn | apply IH; exact Hc].
Qed.

Definition NClosed (R : config -> Prop) : Prop :=
forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok c I (fun _ => []) nx -> (forall i, R (nx i)) -> R c.

#[using="Type"] Lemma rz_silent : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok c I (fun _ => []) nx ->
(forall i, realizes (nx i) T) ->
realizes c T.
Proof.
intros c I nx i0 T Hnode Hc.
assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hc i0)).
apply (rz_conseq c (t_alt (fun i : I => t_emit [] T))).
- apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hc).
- intros tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

#[using="Type"] Lemma nclosed_realizes : forall T, NClosed (fun c => realizes c T).
Proof. intros T c I nx i0 Hnode Hc. exact (rz_silent c I nx i0 T Hnode Hc). Qed.

#[using="Type"] Lemma nclosed_lbody : forall V T, NClosed (lbody V T).
Proof.
intros V T c I nx i0 Hnode Hc.
apply (lb_node V T c I nx (fun _ => true) Hnode).
- intros i _. apply Hc.
- intros i H. discriminate H.
Qed.

#[using="Type"] Lemma nclosed_star : forall c_e, NClosed (fun c => star_cfg segs (alloc_only_cfg false) c [] c_e).
Proof.
intros c_e c I nx i0 [Hcomp _] Hc.
change ([] : list event) with ([] ++ [] : list event).
eapply star_cfg_step; [apply (Hcomp i0) | apply Hc].
Qed.

#[using="Type"] Lemma nclosed_silent1 : forall R c c', NClosed R ->
node_ok c unit (fun _ => []) (fun _ => c') -> R c' -> R c.
Proof. intros R c c' HR Hnode Hc. apply (HR c unit (fun _ => c') tt Hnode). intros []; exact Hc. Qed.

#[using="Type"] Lemma lb_silent1 : forall V T c c',
node_ok c unit (fun _ => []) (fun _ => c') -> lbody V T c' -> lbody V T c.
Proof. intros V T c c' Hn Hc. eapply nclosed_silent1; [apply nclosed_lbody | exact Hn | exact Hc]. Qed.

#[using="Type"] Lemma lb_back1 : forall V T c c',
node_ok c unit (fun _ => []) (fun _ => c') -> V c' -> lbody V T c.
Proof.
intros V T c c' Hn HV.
apply (lb_node V T c unit (fun _ => c') (fun _ => false) Hn).
- intros i H. discriminate H.
- intros [] _. exact HV.
Qed.

#[using="Type"] Lemma lb_dpath : forall V T c c', dpath c c' -> lbody V T c' -> lbody V T c.
Proof.
intros V T c c' Hd; induction Hd as [c | c c1 c2 Hn Hd IH]; intros Hc; [exact Hc|].
eapply lb_silent1; [exact Hn | apply IH; exact Hc].
Qed.

#[using="Type"] Lemma lb_node_sum : forall V T c (A B : Type) (nx : A + B -> config),
node_ok c (A + B) (fun _ => []) nx ->
(forall a, V (nx (inl a))) ->
(forall b, lbody V T (nx (inr b))) ->
lbody V T c.
Proof.
intros V T c A B nx Hnode HA HB.
apply (lb_node V T c (A + B) nx (fun i => match i with inl _ => false | inr _ => true end) Hnode).
- intros [a|b] H; [discriminate H | apply HB].
- intros [a|b] H; [apply HA | discriminate H].
Qed.

#[using="Type"] Lemma lbody_mono : forall (V V' : config -> Prop) T c,
(forall x, V x -> V' x) -> lbody V T c -> lbody V' T c.
Proof.
intros V V' T c HVV' H.
induction H as [V T c Hr | V T c I nx k Hnode Hk IHk HV] in |- *.
- apply lb_exit. exact Hr.
- apply (lb_node V' T c I nx k Hnode).
+ intros i Hi. apply IHk; [exact Hi | exact HVV'].
+ intros i Hi. apply HVV'. apply HV. exact Hi.
Qed.

#[using="Type"] Lemma rz_retry : forall c (A B : Type) (nx : A + B -> config) (T : TSet) (b0 : B),
node_ok c (A + B) (fun _ => []) nx ->
(forall a, dpath (nx (inl a)) c) ->
(forall b, realizes (nx (inr b)) T) ->
realizes c T.
Proof.
intros c A B nx T b0 Hnode Hback Hcont.
apply (rz_loop (fun c' => dpath c' c) T c (nx (inr b0))).
- apply dpath_refl.
- intros c' Hd. induction Hd as [c0 | c0 c1 c2 Hn Hd IH].
+ eapply lb_node_sum; [exact Hnode | exact Hback | intros b; apply lb_exit; apply Hcont].
+ eapply lb_silent1; [exact Hn | apply IH; assumption].
- destruct Hnode as [Hcomp _].
change ([] : list event) with ([] ++ [] : list event).
eapply star_cfg_step; [apply (Hcomp (inr b0)) | apply star_cfg_refl].
- apply Hcont.
Qed.

Inductive lbw (V : config -> Prop) (T : TSet) : bool -> config -> Prop :=
| lbw_exit : forall p c, realizes c T -> lbw V T p c
| lbw_node : forall p c (I : Type) (nx : I -> config) (k : I -> option bool),
node_ok c I (fun _ => []) nx ->
(forall i q, k i = Some q -> lbw V T q (nx i)) ->
(forall i, k i = None -> V (nx i)) ->
(p = true -> exists i, k i = Some true) ->
lbw V T p c.

#[using="Type"] Lemma lbw_lbody : forall V T p c, lbw V T p c -> lbody V T c.
Proof.
intros V T p c H; induction H as [p c Hr | p c I nx k Hnode Hk IHk HV Hw].
- apply lb_exit. exact Hr.
- apply (lb_node V T c I nx (fun i => match k i with Some _ => true | None => false end) Hnode).
+ intros i Hi. destruct (k i) as [q|] eqn:E; [| discriminate Hi]. eapply IHk. exact E.
+ intros i Hi. destruct (k i) as [q|] eqn:E; [discriminate Hi |]. apply HV. exact E.
Qed.

#[using="Type"] Lemma lbw_witness : forall V T p c, lbw V T p c -> p = true ->
exists c_e, star_cfg segs (alloc_only_cfg false) c [] c_e /\ realizes c_e T.
Proof.
intros V T p c H; induction H as [p c Hr | p c I nx k Hnode Hk IHk HV Hw]; intros Hp.
- exists c. split; [apply star_cfg_refl | exact Hr].
- destruct (Hw Hp) as (i & Hi).
destruct (IHk i true Hi eq_refl) as (c_e & Hs & He).
exists c_e. split; [| exact He].
destruct Hnode as [Hcomp _].
change ([] : list event) with ([] ++ [] : list event).
eapply star_cfg_step; [apply (Hcomp i) | exact Hs].
Qed.

#[using="Type"] Lemma lbw_weaken : forall V T p c, lbw V T p c -> lbw V T false c.
Proof.
intros V T p c H; induction H as [p c Hr | p c I nx k Hnode Hk IHk HV Hw].
- apply lbw_exit. exact Hr.
- apply (lbw_node V T false c I nx k Hnode Hk HV). intros H; discriminate H.
Qed.

#[using="Type"] Lemma rz_loop_w : forall (V : config -> Prop) (T : TSet) c,
V c ->
(forall c', V c' -> lbw V T true c') ->
realizes c T.
Proof.
intros V T c HV Hbody.
destruct (lbw_witness V T true c (Hbody c HV) eq_refl) as (c_e & Hs & He).
apply (rz_loop V T c c_e HV); [| exact Hs | exact He].
intros c' HV'. eapply lbw_lbody. apply Hbody. exact HV'.
Qed.

#[using="Type"] Lemma lbw_silent1 : forall V T p c c',
node_ok c unit (fun _ => []) (fun _ => c') -> lbw V T p c' -> lbw V T p c.
Proof.
intros V T p c c' Hn Hc.
apply (lbw_node V T p c unit (fun _ => c') (fun _ => Some p) Hn).
- intros [] q Hq. injection Hq as <-. exact Hc.
- intros [] H. discriminate H.
- intros ->. exists tt. reflexivity.
Qed.

#[using="Type"] Lemma lbw_back1 : forall V T c c',
node_ok c unit (fun _ => []) (fun _ => c') -> V c' -> lbw V T false c.
Proof.
intros V T c c' Hn HV.
apply (lbw_node V T false c unit (fun _ => c') (fun _ => None) Hn).
- intros [] q Hq. discriminate Hq.
- intros [] _. exact HV.
- intros H. discriminate H.
Qed.

#[using="Type"] Lemma nclosed_lbw : forall V T p, NClosed (lbw V T p).
Proof.
intros V T p c I nx i0 Hnode Hc.
apply (lbw_node V T p c I nx (fun _ => Some p) Hnode).
- intros i q Hq. injection Hq as <-. apply Hc.
- intros i H. discriminate H.
- intros ->. exists i0. reflexivity.
Qed.

#[using="Type"] Lemma rz_emit1 : forall c c' e T,
node_ok c unit (fun _ => e) (fun _ => c') ->
realizes c' T ->
realizes c (t_emit e T).
Proof.
intros c c' e T Hnode Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
intros []; exact Hc.
- apply t_alt_unit.
Qed.

#[using="Type"] Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok c (IA + IB) (fun _ => []) nx ->
(forall i, realizes (nx (inl i)) A) ->
(forall i, realizes (nx (inr i)) B) ->
realizes c (t_alt2 A B).
Proof.
intros c IA IB nx A B a0 b0 Hnode HA HB.
assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
apply (rz_conseq c
(t_alt (fun i : IA + IB =>
t_emit [] (match i with inl _ => A | inr _ => B end)))).
- apply (rz_node c (IA + IB) (fun _ => []) nx
(fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
intros [i|i]; [apply HA | apply HB].
- intro tr. unfold t_alt2. split.
+ intros [[i|i] Hi];
[ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
| right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
+ intros [H | H];
[ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
| exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

#[using="Type"] Lemma node_instr : forall ms model ms',
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
intros ms model ms' Hh Hlazy Hsvc Hstep. split.
- intros []. apply (sstep_cfg_instr segs (alloc_only_cfg false) ms model ms' model);
[assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros e st Hss.
destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep (sstep_cfg_sub segs _ _ _ _ Hss)) as [-> ->].
exists tt. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.

#[using="Type"] Lemma rz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
realizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- split.
+ intros []. cbn.
replace [ExitEv code (m_fs model)]
with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
apply (sstep_cfg_exit segs (alloc_only_cfg false) ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted code model) [] code);
[exact Hh | exact Hsvc
| apply (exit_dispatch_ok (sys_input segs ms x8) model);
rewrite in_sysno_sys_input; exact Hx8
| reflexivity
| apply m_killed_with_halted ].
+ intros e st Hss.
destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub segs _ _ _ _ Hss)) as [-> ->].
exists tt. split; reflexivity.
- apply rz_halt. cbn. discriminate.
Qed.

#[using="Type"] Lemma rz_munmap : forall ms model x8 T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
eapply rz_silent1; [| exact Hc]. split.
- intros []. apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
+ exact Hh.
+ exact Hsvc.
+ apply munmap_ok; assumption.
+ apply spurious_refusal_family_on. unfold injected_family_off.
rewrite in_sysno_sys_input, Hno. reflexivity.
+ rewrite munmap_model_halted; exact Hh.
+ apply materialize_model_accesses_no_lazy.
exact (munmap_model_no_lazy _ _ _ Hlazy).
- intros e st Hss.
destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs (sstep_cfg_sub segs _ _ _ _ Hss))
as [-> ->].
exists tt. split; reflexivity.
Qed.

End WithSegs.


Lemma exitline_realizes_aux : forall segs ms bufs code model,
to_wexit segs ms bufs code -> bufs = [] ->
m_halted model = None ->
m_vm_lazy model = [] ->
realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
intros segs ms bufs code model Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
[| discriminate Hbufs |]; intro Hlazy.
- eapply rz_exit; eassumption.
- eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : forall segs ms code model,
to_wexit segs ms [] code ->
m_halted model = None ->
m_vm_lazy model = [] ->
realizes segs (mkCfg ms model) (t_exit code (m_fs model)).
Proof.
intros segs ms code model Hte Hh Hlazy.
exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.

Definition t_outcomes (fs : Fs.Fs)
(U : (list (list byte) * word) -> Prop) : TSet :=
fun tr => exists o, U o /\ is_prefix tr (QiVh.outcome_trace fs o).

Lemma t_alt_emit_nil : forall (I : Type) (f : I -> TSet),
(forall i, f i []) -> t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f).
Proof.
intros I f H tr. split.
- intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
- intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.

Lemma t_outcomes_two_alt2 : forall fs bf cf bs cs,
t_eq (t_outcomes fs (QEVk.two_outcomes bf cf bs cs))
(t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))).
Proof.
intros fs bf cf bs cs tr.
unfold t_outcomes, QEVk.two_outcomes, QiVh.outcome_trace, t_alt2.
rewrite !t_writes_exit_iff. split.
- intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
- intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)]; cbn [fst snd]; auto.
Qed.

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

