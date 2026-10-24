(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n YK11 YK0i YK0h.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section f.
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
rewrite (YK11.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
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
Lemma c_ltu_ltb : forall x y : word,
c_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.
Lemma v_addiw_small : forall (x : word) imm,
(0 <= bv_unsigned x + imm)%Z -> (bv_unsigned x + imm < 2^31)%Z -> (0 <= imm)%Z ->
bv_unsigned (v_addiw x imm) = (bv_unsigned x + imm)%Z.
Proof.
intros x imm Hlo Hhi _. unfold v_addiw.
rewrite Z_to_bv_unsigned.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
Lemma v_addiw_id : forall x : word, (bv_unsigned x < 2^31)%Z -> v_addiw x 0 = x.
Proof.
intros x Hx. apply bv_eq.
rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.
Lemma land_255_small : forall c : word, (bv_unsigned c < 256)%Z ->
bv_and c (Z_to_bv 64 255) = c.
Proof.
intros c Hc. apply bv_eq.
rewrite bv_and_unsigned, Z_to_bv_unsigned.
change (bv_wrap 64 255) with (Z.ones 8).
rewrite Z.land_ones by lia.
apply Z.mod_small.
pose proof (u64_range c). change (2^8)%Z with 256%Z. lia.
Qed.
Lemma tw_write_ret : forall segs regs pc mem rom buf bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
(v_addi pc 4) mem rom) bufs code) ->
to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(buf :: bufs) code.
Proof.
intros segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont.
eapply tw_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit_coden : forall segs regs pc mem rom (c : word),
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} [] c.
Proof.
intros segs regs pc mem rom c H17 H10 Hc.
assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} 0)
(Z_to_bv 64 255) = c).
{ unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0, H10.
apply land_255_small. exact Hc. }
rewrite <- Hg.
eapply tw_exit.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
Qed.
Definition argv_layout_slack : Z := 4300000%Z.
Local Lemma argv_struct_arith : forall a e : Z,
(0 <= a)%Z -> (a <= 1024)%Z -> (0 <= e)%Z -> (e <= 256)%Z ->
(8 + (a + 1) * 8 + (e + 1) * 8 + 160 <= 10424)%Z.
Proof. intros. lia. Qed.
Local Lemma argv_sum_arith : forall a b : Z,
(a <= 10424)%Z -> (b <= 2097152)%Z -> (a + b <= 2107576)%Z.
Proof. intros. lia. Qed.
Local Lemma argv_mod_arith : forall s m : Z,
(0 <= s)%Z -> (0 <= m)%Z -> (m <= 2107576)%Z -> (s + 4300000 < 2^64)%Z ->
(0 <= s + m < 2^64)%Z.
Proof. intros. lia. Qed.
Local Lemma argv_final_arith : forall s m l : Z,
(0 <= m)%Z -> (0 <= l)%Z -> (m <= 2107576)%Z -> (l <= 131071)%Z ->
(s + 4300000 < 2^64)%Z ->
(s <= s + m)%Z /\ (s + m + l + 1 < 2^64)%Z.
Proof. intros. lia. Qed.
Lemma argv_ptr_bounds : forall (sp : word) av ev k,
valid_argv av -> valid_envp ev -> (k < length av)%nat ->
(bv_unsigned sp + argv_layout_slack < 2^64)%Z ->
(bv_unsigned sp <= bv_unsigned (cat_argv_ptr sp av ev k))%Z /\
(bv_unsigned (cat_argv_ptr sp av ev k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
Proof.
intros sp av ev k Hva Hve Hk Hsp.
pose proof (valid_argv_len av Hva) as HavZ.
pose proof (valid_argv_str_len av k Hva Hk) as HnthZ.
destruct Hva as [Hlen [Htot [Hstr Hnz]]].
destruct Hve as [Helen _].
assert (HevZ : (Z.of_nat (length ev) <= 256)%Z) by exact Helen.
assert (HtotZ : (Z.of_nat (total_arg_bytes_nat (firstn k av)) <= 2097152)%Z).
{ rewrite total_arg_bytes_Z in Htot.
pose proof (total_arg_bytes_firstn_le k av). lia. }
assert (HA : (Z.of_nat (cat_struct_size av ev) <= 10424)%Z).
{ unfold cat_struct_size, auxv_size.
repeat (rewrite !Nat2Z.inj_add || rewrite !Nat2Z.inj_mul).
change (Z.of_nat 8) with 8%Z. change (Z.of_nat 1) with 1%Z.
change (Z.of_nat 160) with 160%Z.
apply argv_struct_arith;
solve [ exact HavZ | exact HevZ | apply Nat2Z.is_nonneg ]. }
assert (Hptr : cat_argv_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
set (n := (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat) in *.
assert (HnZ : (Z.of_nat n <= 2107576)%Z)
by (unfold n; rewrite Nat2Z.inj_add; exact (argv_sum_arith _ _ HA HtotZ)).
assert (Hu : bv_unsigned (sp + nat_to_word n) = (bv_unsigned sp + Z.of_nat n)%Z).
{ unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
apply Z.mod_small.
pose proof (u64_range sp) as Hu64.
unfold argv_layout_slack in Hsp.
exact (argv_mod_arith _ _ (proj1 Hu64) (Nat2Z.is_nonneg n) HnZ Hsp). }
rewrite Hptr, Hu.
unfold argv_layout_slack in Hsp.
exact (argv_final_arith _ _ _ (Nat2Z.is_nonneg n)
(Nat2Z.is_nonneg (length (nth k av []))) HnZ HnthZ Hsp).
Qed.
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
End f.
Ltac reg_neq_tac :=
let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.
Section g.
Context {fx : FPState}.
End g.
Ltac getr_resolve :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero;
rewrite ?getr_nz by reg_neq_tac.
Section h.
Context {fx : FPState}.
End h.
Ltac regupd_resolve :=
repeat first [ rewrite regupd_same
| rewrite regupd_other by reg_neq_tac ].
Section o.
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
Lemma step_lw_zero : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
bv_eqb rd 0 = false ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat
= Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs imm Hf He Hd Hrd Hr.
assert (Hval : sext 64 (bv_extract 0 32 (le_bytes_to_word
[Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]))
= Z_to_bv 64 0)
by (apply bv_eq; reflexivity).
step_pipeline Hf He Hd.
rewrite bv_eqb0_is_x0 in Hrd.
unfold getr in Hr; rewrite ?bv_eqb0_is_x0 in Hr.
rewrite ov_rdn, b_addsext, Hr; cbv beta iota.
rewrite Hval, Hrd; cbv beta iota.
rewrite b_npc4. reflexivity.
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
Lemma step_sb256 : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 1 (getr regs rs2))) rom).
Proof. exact step_sb. Qed.
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
Lemma v_divu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
bv_unsigned (v_divu x y) = (bv_unsigned x / bv_unsigned y)%Z.
Proof.
intros x y Hy. unfold v_divu.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range x). pose proof (u64_range y).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; nia.
Qed.
Lemma v_remu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
bv_unsigned (v_remu x y) = (bv_unsigned x mod bv_unsigned y)%Z.
Proof.
intros x y Hy. unfold v_remu.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range y).
pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y) Hy).
lia.
Qed.
Lemma v_subw_small : forall x y : word,
(bv_unsigned y <= bv_unsigned x)%Z ->
(bv_unsigned x - bv_unsigned y < 2^31)%Z ->
bv_unsigned (v_subw x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
intros x y Hle Hlt. unfold v_subw.
rewrite Z_to_bv_unsigned.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
Lemma land_d48 : forall d : Z, (0 <= d)%Z -> (d < 16)%Z -> Z.land d 48 = 0%Z.
Proof.
intros d Hd0 Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 4) as [Hi4|Hi4].
- replace 48%Z with (Z.shiftl 3 4)%Z by reflexivity.
rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite (Z_testbit_high 4 d i) by lia. reflexivity.
Qed.
Lemma lor_small_add : forall d : Z, (0 <= d)%Z -> (d < 16)%Z ->
Z.lor d 48 = (d + 48)%Z.
Proof.
intros d Hd0 Hd.
rewrite <- Z.lxor_lor by (apply land_d48; assumption).
rewrite <- Z.add_nocarry_lxor by (apply land_d48; assumption).
reflexivity.
Qed.
Lemma v_ori_lor : forall d : word, (bv_unsigned d < 16)%Z ->
v_ori d 48 = Z_to_bv 64 (bv_unsigned d + 48).
Proof.
intros d Hd. unfold v_ori.
change (bv_wrap 64 48) with 48%Z.
f_equal. apply lor_small_add; [apply u64_range | exact Hd].
Qed.
Lemma rdn_app : forall segs mem n1 n2 (a : word) bs1 bs2,
rdn segs mem a n1 = Some bs1 ->
rdn segs mem (a + nat_to_word n1) n2 = Some bs2 ->
rdn segs mem a (n1 + n2)%nat = Some (bs1 ++ bs2).
Proof.
intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
- cbn in H1. injection H1 as <-. cbn [app].
rewrite word_add_0 in H2. exact H2.
- change (S n1 + n2)%nat with (S (n1 + n2))%nat.
cbn [rdn] in H1 |- *.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|]; [|discriminate].
destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
injection H1 as <-.
rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
exact H2.
Qed.
Lemma rdn_nth : forall segs mem n (a : word) bs j,
rdn segs mem a n = Some bs -> (j < n)%nat ->
rdn segs mem (a + nat_to_word j) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct j as [|j].
- rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
- cbn [nth].
replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest j Er). lia.
Qed.
Lemma v_addi_m : forall (x : word) (k : Z),
(k <= bv_unsigned x)%Z -> (0 < k)%Z ->
v_addi x (- k) = Z_to_bv 64 (bv_unsigned x - k).
Proof. intros x k _ _. reflexivity. Qed.
Lemma rdn_skipn : forall segs mem n (a : word) bs k,
rdn segs mem a n = Some bs -> (k <= n)%nat ->
rdn segs mem (a + nat_to_word k) (n - k)%nat = Some (skipn k bs).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. rewrite word_add_0.
cbn in H |- *. injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k].
+ rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [Nat.sub skipn].
replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest k Er). lia.
Qed.
Lemma rdn_firstn : forall segs mem n (a : word) bs k,
rdn segs mem a n = Some bs -> (k <= n)%nat ->
rdn segs mem a k = Some (firstn k bs).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. cbn in H |- *.
injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k]; [reflexivity|].
cbn [rdn firstn]. rewrite Eb.
rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End o.
