(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import QHWH.
Import ListNotations.
Open Scope bv_scope.

Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
(bv_unsigned a + Z.of_nat n <= bv_unsigned lo
\/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

Definition accesses_outside_lazy
(accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
access_outside_range a n lo sz.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg4E. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqRD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqRD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QybZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QybZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.Mq1.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

Definition v_jalr (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

Lemma step_jal_link : forall segs regs pc mem rom w rd (imm : bv 21),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jal rd imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(btgt pc (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_addsext;
reflexivity.
Qed.

Lemma step_jalr : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(v_jalr (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.

Lemma step_sd_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4.
reflexivity.
Qed.

Lemma step_sd_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
RiscvSemantics.store_ok segs mem a 8%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.

Lemma step_addi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_addi (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_add_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_add (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sub_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_sub (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_lui_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_lui (Z.shiftl (bv_signed imm) 12) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_auipc_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_addiw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_addiw (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sltiu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_sltiu (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_xori (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mul_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_mul (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_andi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_andi (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_ori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
v_ori (getr regs rs) (bv_signed imm) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
bv_eqb rd 0 = false ->
v_slli (getr regs rs) (bv_unsigned sh) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
bv_eqb rd 0 = false ->
v_srli (getr regs rs) (bv_unsigned sh) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (QqRD.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srai_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
bv_eqb rd 0 = false ->
v_srai (getr regs rs) (bv_unsigned sh) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.

Lemma rdn_wbytes_hit : forall segs bs m (a : word),
(bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof.
intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
cbn [length] in Hnw |- *.
change (wbytes m a (b :: rest))
with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
set (m' := fun x : word => if bv_eqb x a then Some b else m x).
cbn [rdn].
destruct rest as [|b' rest'].
- cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
- assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
by (apply u_add1; cbn [length] in Hnw; lia).
assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
{ rewrite (wbytes_below (b' :: rest') m' (a+1) a);
[ unfold m'; rewrite bv_eqb_refl; reflexivity
| cbn [length] in *; lia
| pose proof (u64_range a); lia ]. }
rewrite Hread.
rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
reflexivity.
Qed.

Lemma rdn_wbytes_hit8 : forall segs m (a v : word),
(bv_unsigned a + 8 <= 2^64)%Z ->
rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8%nat = Some (word_to_le_bytes 8 v).
Proof.
intros segs m a v Hnw.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

Lemma bytes_le_to_Z_8 : forall v : word,
bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v.
Proof.
intro v. rewrite bytes_le_N.
change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
apply Z.mod_small. apply u64_range.
Qed.

Definition argv_layout_slack : Z := 4300000%Z.

Lemma step_jalr_x0 : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr 0 rs1 imm, 4%Z) ->
getr regs rs1 = tgt ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
rewrite Ht. reflexivity.
Qed.

Lemma step_jalr_link : forall segs regs pc mem rom w rd rs1 (imm : bv 12) tgt,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
bv_eqb rd 0 = false ->
getr regs rs1 = tgt ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
rewrite Ht, Hrd. reflexivity.
Qed.

Lemma getr_zero : forall regs, getr regs 0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

End WithFP1.
Ltac reg_neq_tac :=
let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

Section WithFP2.
Context {fx : FPState}.

End WithFP2.
Ltac getr_resolve :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero;
rewrite ?getr_nz by reg_neq_tac.

Section WithFP3.
Context {fx : FPState}.

End WithFP3.
Ltac regupd_resolve :=
repeat first [ rewrite regupd_same
| rewrite regupd_other by reg_neq_tac ].

Section WithFP4.
Context {fx : FPState}.

Goal forall regs (v : word), getr (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), getr (regupd regs 8 v) 0 = Z_to_bv 64 0.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), reg_get (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. regupd_resolve. reflexivity. Abort.

Definition v_divu (x y : word) : word :=
Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).

Lemma m_divu : forall a b : word, (bv_unsigned b <> 0)%Z ->
mul_div M_DIVU a b = v_divu a b.
Proof.
intros a b Hb.
change (mul_div M_DIVU a b)
with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
rewrite (proj2 (Z.eqb_neq _ _) Hb).
apply bv_eq. unfold v_divu.
rewrite bv_divu_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range a). pose proof (u64_range b).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned a); [|lia].
apply Z.div_le_upper_bound; nia.
Qed.

Lemma m_remu : forall a b : word, (bv_unsigned b <> 0)%Z ->
mul_div M_REMU a b = v_remu a b.
Proof.
intros a b Hb.
change (mul_div M_REMU a b)
with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
rewrite (proj2 (Z.eqb_neq _ _) Hb).
apply bv_eq. unfold v_remu.
rewrite bv_modu_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range a). pose proof (u64_range b).
pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
lia.
Qed.

Lemma step_divu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs2) <> 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
erewrite step_mul_gen by eassumption.
rewrite m_divu by exact Hnz. reflexivity.
Qed.

Lemma step_remu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs2) <> 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
erewrite step_mul_gen by eassumption.
rewrite m_remu by exact Hnz. reflexivity.
Qed.

Lemma step_sb : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 1 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
assert (Hsb : forall u : word,
Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
{ intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_wrap. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, Hsb, b_npc4.
reflexivity.
Qed.

Lemma N_to_le_bytes_1_small : forall v : word,
word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

Lemma Zmod_pow2_div8 : forall z m, (8 <= m)%Z ->
((z mod 2^m) / 2^8)%Z = ((z / 2^8) mod 2^(m-8))%Z.
Proof.
intros z m Hm.
rewrite <- !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'; intros i Hi.
rewrite !Z.shiftr_spec by lia.
destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite Z.shiftr_spec by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_wrap : forall n (m : N) z,
(8 * Z.of_nat n <= Z.of_N m)%Z ->
Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z.
Proof.
induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
f_equal.
- apply bv_eq. rewrite !Z_to_bv_unsigned.
apply bv_wrap_bv_wrap. lia.
- replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
+ apply IH. lia.
+ unfold bv_wrap, bv_modulus.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite Zmod_pow2_div8 by lia.
do 2 f_equal. lia.
Qed.

Lemma store_bytes_low16 : forall u : word,
Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u.
Proof.
intro u. unfold word_to_le_bytes.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply Z_to_le_bytes_wrap. lia.
Qed.

Lemma store_bytes_low32 : forall u : word,
Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u.
Proof.
intro u. unfold low32, word_to_le_bytes.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply Z_to_le_bytes_wrap. lia.
Qed.

Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
reflexivity.
Qed.

Lemma step_sw_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
RiscvSemantics.store_ok segs mem a 4%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.

Lemma step_sh_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 2%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 2 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
reflexivity.
Qed.

Lemma step_sh_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
getr regs rs2 = v ->
RiscvSemantics.store_ok segs mem a 2%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.

Lemma v_addi_m : forall (x : word) (k : Z),
(k <= bv_unsigned x)%Z -> (0 < k)%Z ->
v_addi x (- k) = Z_to_bv 64 (bv_unsigned x - k).
Proof. intros x k _ _. reflexivity. Qed.

End WithFP4.
