(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition frm_zero (f : bv 32) : Prop :=
Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.
Lemma fp_frm_zero_fx0 : frm_zero (@fp_csr fx0).
Proof. reflexivity. Qed.
Lemma fp_fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof.
intros [nv dz of uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
destruct nv, dz, of, uf, nx; vm_compute; split; congruence.
Qed.
Lemma fp_u32_range : forall f : bv 32, (0 <= bv_unsigned f < 2^32)%Z.
Proof. intros f. pose proof (bv_unsigned_in_range _ f) as H. unfold bv_modulus in H. exact H. Qed.
Lemma fp_Z_land_range_l : forall n a b, (0 <= n)%Z -> (0 <= a < 2^n)%Z ->
(0 <= Z.land a b < 2^n)%Z.
Proof.
intros n a b Hn Ha. split; [apply Z.land_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
intros k Hk. rewrite Z.land_spec. rewrite (Z_testbit_high n a k) by lia. reflexivity.
Qed.
Lemma fp_Z_lor_range : forall n a b, (0 <= n)%Z -> (0 <= a < 2^n)%Z -> (0 <= b < 2^n)%Z ->
(0 <= Z.lor a b < 2^n)%Z.
Proof.
intros n a b Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
intros k Hk. rewrite Z.lor_spec.
rewrite (Z_testbit_high n a k) by lia. rewrite (Z_testbit_high n b k) by lia. reflexivity.
Qed.
Lemma fp_u_Z2bv32 : forall z, (0 <= z < 2^32)%Z -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.
Lemma fp_frm_zero_accrue : forall (f : bv 32) (b : Z),
(0 <= b < 32)%Z -> frm_zero f ->
frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) b)).
Proof.
intros f b Hb Hf. unfold frm_zero in *.
pose proof (fp_u32_range f) as Hr.
rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 5) by lia.
rewrite (Z.div_small b (2^5)) by lia. rewrite Z.lor_0_r. exact Hf.
Qed.
Lemma fp_frm_zero_slice0_5 : forall (f : bv 32) (v : word),
frm_zero f -> frm_zero (slice_set f 0 5 v).
Proof.
intros f v Hf. unfold frm_zero, slice_set in *.
pose proof (fp_u32_range f) as Hr.
change (Z.shiftl (Z.ones 5) 0) with 31%Z.
rewrite Z.shiftl_0_r.
assert (H1 : (0 <= Z.land (bv_unsigned f) (Z.lnot 31) < 2^32)%Z)
by (apply fp_Z_land_range_l; lia).
assert (H2 : (0 <= Z.land (bv_unsigned v) 31 < 2^32)%Z).
{ split; [apply Z.land_nonneg; right; lia|].
rewrite Z.land_comm. apply (proj2 (fp_Z_land_range_l 32 31 (bv_unsigned v) ltac:(lia) ltac:(lia))). }
rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
rewrite Z.shiftr_lor, !Z.shiftr_land.
change (Z.shiftr (Z.lnot 31) 5) with (-1)%Z. change (Z.shiftr 31 5) with 0%Z.
rewrite Z.land_m1_r, Z.land_0_r, Z.lor_0_r. exact Hf.
Qed.
Lemma fp_resolve_rm : forall (rm : bv 3) (f : bv 32),
frm_zero f ->
(bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
exists md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = Some md.
Proof.
intros rm f Hf Hrm. unfold rmode_of_field. rewrite Hf.
pose proof (bv_unsigned_in_range _ rm) as Hr.
destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE].
- exists RNE. reflexivity.
- unfold rmode_of_Z.
destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
exfalso. lia.
Qed.
Ltac fp_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.drop_access_report,
RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val Sem.exec_csr
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
Sem.accrue Sem.resolve_rm Sem.frm_of
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
RiscvSemantics.access_value RiscvSemantics.drop_access_report
ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst fp_regs fp_csr];
rewrite ?bv_eqb0_is_x0.
Lemma fp_step_fld : forall (fx : FPState) segs regs pc mem rom w rd rs (imm : bv 12) a bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FLoad FMT_D rd rs imm, 4%Z) ->
v_addi (getr regs rs) (bv_signed imm) = a ->
rdn segs mem a 8%nat = Some bs ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.
Lemma fp_step_flw : forall (fx : FPState) segs regs pc mem rom w rd rs (imm : bv 12) a bs,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FLoad FMT_S rd rs imm, 4%Z) ->
v_addi (getr regs rs) (bv_signed imm) = a ->
rdn segs mem a 4%nat = Some bs ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx)) (@fp_csr fx))
regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite ov_rdn, b_addsext, Ha, Hr. cbv beta iota.
cbn [fp_regs fp_csr]. rewrite b_npc4. reflexivity.
Qed.
Lemma fp_step_fsd : forall (fx : FPState) segs regs pc mem rom w rs1 rs2 (imm : bv 12) a,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FStore FMT_D rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
store_ok segs mem a 8%nat = true ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx regs (v_addi pc 4)
(wbytes mem a (word_to_le_bytes 8 (reg_get (@fp_regs fx) rs2))) rom).
Proof.
intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite b_addsext, Ha, Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.
Lemma fp_step_fsw : forall (fx : FPState) segs regs pc mem rom w rs1 rs2 (imm : bv 12) a,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (FStore FMT_S rs1 rs2 imm, 4%Z) ->
v_addi (getr regs rs1) (bv_signed imm) = a ->
store_ok segs mem a 4%nat = true ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx regs (v_addi pc 4)
(wbytes mem a (Z_to_le_bytes 4 (bv_unsigned (low32 (reg_get (@fp_regs fx) rs2))))) rom).
Proof.
intros fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok.
fp_pipeline Hf He Hd.
unfold getr in Ha; rewrite ?bv_eqb0_is_x0 in Ha.
rewrite b_addsext, Ha, Hok. cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4. destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_x_d : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_X_F FMT_D rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (reg_get (@fp_regs fx) rs1))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_x_w : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_X_F FMT_S rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.
Lemma fp_step_fmv_d_x : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_F_X FMT_D rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (getr regs rs1) (@fp_regs fx)) (@fp_csr fx))
regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fmv_w_x : forall (fx : FPState) segs regs pc mem rom w rd rs1,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, 4%Z) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) (@fp_regs fx)) (@fp_csr fx))
regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
fp_pipeline Hf He Hd. unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fsgnj : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
exists fr',
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP fr' (@fp_csr fx)) regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd.
destruct fmt; eexists; fp_pipeline Hf He Hd; cbn [fp_regs fp_csr]; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_fari : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2 (rm : bv 3),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
frm_zero (@fp_csr fx) ->
(bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
exists fr' cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 rm Hf He Hd Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end.
destruct fmt; cbv beta iota; rewrite b_npc4;
(eexists _, _; split; [apply Hacc | reflexivity]).
Qed.
Lemma fp_step_fcvt_to_f : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
(dst = FC_S \/ dst = FC_D) ->
frm_zero (@fp_csr fx) ->
(bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
exists fr' cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP fr' cs') regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct Hdst as [-> | ->]; destruct src; cbv beta iota;
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
try (destruct (is_x0 rs1); cbv beta iota);
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
rewrite b_npc4;
(eexists _, _; split; [ | reflexivity ]; first [apply Hacc | exact Hz]).
Qed.
Lemma fp_step_fcvt_to_x : forall (fx : FPState) segs regs pc mem rom w dst src rd rs1 (rm : bv 3),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
(dst = FC_W \/ dst = FC_WU \/ dst = FC_L \/ dst = FC_LU) ->
(src = FC_S \/ src = FC_D) ->
frm_zero (@fp_csr fx) ->
(bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z ->
exists (v : word) cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs') (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hsrc Hz Hrm.
destruct (fp_resolve_rm rm _ Hz Hrm) as [md Hmd].
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd. rewrite Hmd. cbv beta iota.
destruct Hdst as [-> | [-> | [-> | ->]]]; destruct Hsrc as [-> | ->]; cbv beta iota;
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end;
(destruct (is_x0 rd); cbv beta iota; rewrite b_npc4;
[ exists (Z_to_bv 64 0); eexists; split; [ apply Hacc | reflexivity ]
| eexists _, _; split; [ apply Hacc | reflexivity ] ]).
Qed.
Lemma fp_step_fcmp : forall (fx : FPState) segs regs pc mem rom w op fmt rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
frm_zero (@fp_csr fx) ->
exists (b : bool) cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs')
(if bv_eqb rd 0 then regs else regupd regs rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))))
by (intros fl; apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact Hz]).
fp_pipeline Hf He Hd.
repeat match goal with
| |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota
end.
destruct (is_x0 rd);
[ exists true; eexists; split; [ apply Hacc | rewrite b_npc4; reflexivity ]
| exists v; destruct v; cbv beta iota; rewrite b_npc4;
(eexists; split; [ apply Hacc | reflexivity ]) ].
Qed.
Lemma fp_step_frrm : forall (fx : FPState) segs regs pc mem rom w rd,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Csr CSR_RS rd 0 2, 4%Z) ->
frm_zero (@fp_csr fx) ->
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0))
(v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w rd Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr] in Hz. unfold frm_zero in Hz.
fp_pipeline Hf He Hd.
change (csr_slice 2) with (Some (5%Z, 3%Z)). cbv beta iota.
unfold slice_get. change (Z.ones 3) with 7%Z. rewrite Hz.
change (is_x0 0) with true. cbv beta iota.
destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.
Lemma fp_step_csrsi_fflags : forall (fx : FPState) segs regs pc mem rom w (uimm : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (CsrI CSR_RS 0 uimm 1, 4%Z) ->
frm_zero (@fp_csr fx) ->
exists cs',
frm_zero cs' /\
RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
MachineOk (@mkst (mkFP (@fp_regs fx) cs') regs (v_addi pc 4) mem rom).
Proof.
intros fx segs regs pc mem rom w uimm Hf He Hd Hz.
destruct fx as [fr cs]. cbn [fp_csr fp_regs] in *.
destruct (Z.eqb (bv_unsigned uimm) 0) eqn:Eu.
- exists cs. split; [exact Hz|].
fp_pipeline Hf He Hd. rewrite Eu.
change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
- exists (slice_set cs 0 5 (bv_or (slice_get cs 0 5) (zext 64 uimm))).
split; [apply fp_frm_zero_slice0_5; exact Hz|].
fp_pipeline Hf He Hd. rewrite Eu.
change (csr_slice 1) with (Some (0%Z, 5%Z)). cbv beta iota.
change (is_x0 0) with true. cbv beta iota. rewrite b_npc4. reflexivity.
Qed.
