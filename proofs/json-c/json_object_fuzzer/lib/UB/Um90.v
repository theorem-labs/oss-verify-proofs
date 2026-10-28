(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QRjH.Mq3.
Import UFeQ.Mq0.
Import ListNotations.
Open Scope Z_scope.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

Definition img_clear_ivs : list (Z * Z) :=
[(0, 0x1000); (0x10000,0x66f30); (0x66f31,0x77b30); (0x97c08,0x97c18); (0x77b64,0x77bb0); (0x77bb8,0x77bd0);
(0x77bd8,0x77bf0); (0x77c00,0x77c10); (0x77c20,0x97c08); (0x97c40,0x97e70); (0x97e78,0x97e80); (0x97e91,0x97e98);
(0x97ec8,0x97ef8); (0x97f00,0x97f78); (0x98320,0x99000)]%Z.

Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj QEVk QSjk QiVh Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1SW USPu UU2A U8LG UZSc UsN4 UlKb U39n UJUR Ugw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import UFeQ.Mq0 U1SW USPu UU2A U8LG UZSc UsN4 UlKb U39n UJUR Ugw2.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition mem_w1c (mem : word -> option byte) (sp ra s0 s1 s2 s3 code : word) (tid : Z) :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 0x97e68) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50ed0)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3).

Definition mem_w1A (mem : word -> option byte) (sp ra s0 s1 s2 s3 code : word) (tid : Z) :=
wbytes (wbytes (wbytes (wbytes (wbytes (mem_w1c mem sp ra s0 s1 s2 s3 code tid)
(Z_to_bv 64 0x97c50) (word_to_le_bytes 4 (Z_to_bv 64 0)))
(Z_to_bv 64 0x97c50) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
(Z_to_bv 64 0x97c50) (word_to_le_bytes 4 (Z_to_bv 64 32)))
(Z_to_bv 64 0x97c58) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0x97c48) [Z_to_bv 8 1].

Definition mem_w1I (mem : word -> option byte) (sp ra s0 s1 s2 s3 code : word) (tid : Z) :=
wbytes (mem_w1c mem sp ra s0 s1 s2 s3 code tid) (Z_to_bv 64 0x97c48) [Z_to_bv 8 1].

Definition mem_w1 (armed : bool) (mem : word -> option byte) (sp ra s0 s1 s2 s3 code : word) (tid : Z) :=
if armed then mem_w1A mem sp ra s0 s1 s2 s3 code tid else mem_w1I mem sp ra s0 s1 s2 s3 code tid.

#[using="Type"] Lemma w1A : forall regs mem rom (sp tp code : word) (tid : Z),
getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
(168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
(0 < tid < 2147483648)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e93) 1%nat = Some [Z_to_bv 8 0] ->
atx_state true mem ->
exists regs',
msteps RSEGS (mkst regs (0x50e6c : word) mem rom)
(mkst regs' (0x50e20 : word) (mem_w1A mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) rom)
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
/\ getr regs' 8 = code
/\ getr regs' 1 = Z_to_bv 64 0x50ed4
/\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Gnl (Alock & Ahead & Aslot & Anext & Af0 & Aa0 & Aflag).
zaddr Gnl. zaddr Alock. zaddr Ahead. zaddr Aslot. zaddr Anext. zaddr Af0. zaddr Aa0. zaddr Aflag.
unfold mem_w1A, mem_w1c. eexists. split.
-
stepn F_4f090 D_4f090. rewrite Hsp. sp_renorm.

stepST F_4f094 D_4f094 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
stepST F_4f098 D_4f098 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

stepn F_4f09c D_4f09c.
stepn F_4f0a0 D_4f0a0. rewrite Htp.

stepLD F_4f0a4 D_4f0a4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small tid) by lia.

stepn F_4f0a8 D_4f0a8.
stepn F_4f0ac D_4f0ac.

eapply mst_step; [reflexivity
| eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
[ exact F_4f0b0 | reflexivity | exact D_4f0b0
| gres; u_norm; reflexivity
| gres; rdn_by Mlock
| apply bytes_le_to_Z_4; u_norm; lia ]
| ].
reduce_bv_eqb_ifs; norm_pc_r; vnorm.

eapply mst_step; [reflexivity
| eapply step_bne_ft_r; [exact F_4f0b4 | reflexivity | exact D_4f0b4 | gres; cond_compute ] | ].
norm_pc_r.

eapply mst_step; [reflexivity
| eapply step_sc_w_ok; [exact F_4f0b8 | reflexivity | exact D_4f0b8
| gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
step_simpl; vnorm.

stepb_ft F_4f0bc D_4f0bc ltac:(cond_compute).

stepn F_4f0c0 D_4f0c0.

stepb_ft F_4f0c4 D_4f0c4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

stepb_tk F_4f0c8 D_4f0c8 ltac:(cond_compute).

stepn F_4f0ec D_4f0ec. rewrite Ha0.

stepn F_4f0f0 D_4f0f0.

stepn F_4eeac D_4eeac. sp_renorm.
stepST F_4eeb0 D_4eeb0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50ed0) ltac:(sok_stack SOK).
stepST F_4eeb4 D_4eeb4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST F_4eeb8 D_4eeb8 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
stepST F_4eebc D_4eebc (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
stepST F_4eec0 D_4eec0 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).

stepn F_4eec4 D_4eec4.
stepn F_4eec8 D_4eec8.
stepn F_4eecc D_4eecc.
stepn F_4eed0 D_4eed0.
stepn F_4eed4 D_4eed4.

stepn F_5e774 D_5e774.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_5e778 | reflexivity | exact D_5e778 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_5e77c D_5e77c ltac:(cond_compute).
stepret F_5e96c D_5e96c (0x50cb4 : word) ltac:(bveq).

stepLD8 F_4eed8 D_4eed8 (Z_to_bv 64 0x97c60).
stepb_ft F_4eedc D_4eedc ltac:(cond_compute).

stepLD F_4eee0 D_4eee0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
try rewrite (v_lw_small 1) by lia.
stepn F_4eee4 D_4eee4.

stepn F_4eefc D_4eefc.
stepST F_4ef00 D_4ef00 (Z_to_bv 64 0x97c50) (Z_to_bv 64 0) ltac:(sok_data).

stepb_ft F_4ef04 D_4ef04 ltac:(cond_compute).

stepLD8 F_4ef08 D_4ef08 (Z_to_bv 64 0x97c60).
stepn F_4ef0c D_4ef0c.
stepn F_4ef10 D_4ef10.

stepLD8 F_4ef14 D_4ef14 (Z_to_bv 64 0x50e18).
stepLD8 F_4ef18 D_4ef18 (Z_to_bv 64 0x20fac).

stepn F_4ef1c D_4ef1c.
stepn F_4ef20 D_4ef20.
stepLD F_5e9fc D_5e9fc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
try rewrite (v_lw_small 0) by lia.
stepb_ft F_5ea00 D_5ea00 ltac:(cond_compute).
stepret F_5ea04 D_5ea04 (0x50d00 : word) ltac:(bveq).

stepn F_4ef24 D_4ef24.
stepjr F_4ef28 D_4ef28 (Z_to_bv 64 0x50e18) ltac:(gres; reflexivity). vnorm.
stepjr F_4f03c D_4f03c (Z_to_bv 64 0x20fac) ltac:(gres; reflexivity). vnorm.

stepn F_20d88 D_20d88.
stepLBU F_20d8c D_20d8c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
stepb_ft F_20d90 D_20d90 ltac:(cond_compute).
stepret F_20d94 D_20d94 (0x50d08 : word) ltac:(bveq).

stepn F_4ef2c D_4ef2c.
stepn F_4ef30 D_4ef30.
stepn F_5e774 D_5e774.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_5e778 | reflexivity | exact D_5e778 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_5e77c D_5e77c ltac:(cond_compute).
stepret F_5e96c D_5e96c (0x50d10 : word) ltac:(bveq).

stepLD F_4ef34 D_4ef34 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
try rewrite (v_lw_small 0) by lia.
stepn F_4ef38 D_4ef38.
stepST F_4ef3c D_4ef3c (Z_to_bv 64 0x97c50) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).

stepb_ft F_4ef40 D_4ef40 ltac:(cond_compute).
stepLD8 F_4ef44 D_4ef44 (Z_to_bv 64 0x97c60).
stepn F_4ef48 D_4ef48.

stepLD8 F_4eee8 D_4eee8 (Z_to_bv 64 0).
stepn F_4eeec D_4eeec.
stepST F_4eef0 D_4eef0 (Z_to_bv 64 0x97c50) (Z_to_bv 64 32) ltac:(sok_data).
stepST F_4eef4 D_4eef4 (Z_to_bv 64 0x97c58) (Z_to_bv 64 0) ltac:(sok_data).
stepb_tk F_4eef8 D_4eef8 ltac:(cond_compute).

stepn F_4ef4c D_4ef4c.
stepST F_4ef50 D_4ef50 (Z_to_bv 64 0x97c48) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).

stepn F_4ef54 D_4ef54.
stepLD8 F_4ef58 D_4ef58 (Z_to_bv 64 0x50ed0).
stepLD8 F_4ef5c D_4ef5c code.
stepLD8 F_4ef60 D_4ef60 (getr regs 9).
stepLD8 F_4ef64 D_4ef64 (getr regs 18).
stepLD8 F_4ef68 D_4ef68 (getr regs 19).
stepn F_4ef6c D_4ef6c. sp_renorm.
stepn F_4ef70 D_4ef70.

stepLD F_5e9fc D_5e9fc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
try rewrite (v_lw_small 0) by lia.
stepb_ft F_5ea00 D_5ea00 ltac:(cond_compute).
stepret F_5ea04 D_5ea04 (0x50ed0 : word) ltac:(bveq).

stepn F_4f0f4 D_4f0f4.
apply mst_refl.
- repeat split; gres; try reflexivity. exact Htp.
Qed.

#[using="Type"] Lemma w1I : forall regs mem rom (sp tp code : word) (tid : Z),
getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
(168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
(0 < tid < 2147483648)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e93) 1%nat = Some [Z_to_bv 8 0] ->
atx_state false mem ->
exists regs',
msteps RSEGS (mkst regs (0x50e6c : word) mem rom)
(mkst regs' (0x50e20 : word) (mem_w1I mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) rom)
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
/\ getr regs' 8 = code
/\ getr regs' 1 = Z_to_bv 64 0x50ed4
/\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Gnl (Alock & Ahead).
zaddr Gnl. zaddr Alock. zaddr Ahead.
unfold mem_w1I, mem_w1c. eexists. split.
-
stepn F_4f090 D_4f090. rewrite Hsp. sp_renorm.

stepST F_4f094 D_4f094 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
stepST F_4f098 D_4f098 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

stepn F_4f09c D_4f09c.
stepn F_4f0a0 D_4f0a0. rewrite Htp.

stepLD F_4f0a4 D_4f0a4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small tid) by lia.

stepn F_4f0a8 D_4f0a8.
stepn F_4f0ac D_4f0ac.

eapply mst_step; [reflexivity
| eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
[ exact F_4f0b0 | reflexivity | exact D_4f0b0
| gres; u_norm; reflexivity
| gres; rdn_by Mlock
| apply bytes_le_to_Z_4; u_norm; lia ]
| ].
reduce_bv_eqb_ifs; norm_pc_r; vnorm.

eapply mst_step; [reflexivity
| eapply step_bne_ft_r; [exact F_4f0b4 | reflexivity | exact D_4f0b4 | gres; cond_compute ] | ].
norm_pc_r.

eapply mst_step; [reflexivity
| eapply step_sc_w_ok; [exact F_4f0b8 | reflexivity | exact D_4f0b8
| gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
step_simpl; vnorm.

stepb_ft F_4f0bc D_4f0bc ltac:(cond_compute).

stepn F_4f0c0 D_4f0c0.

stepb_ft F_4f0c4 D_4f0c4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

stepb_tk F_4f0c8 D_4f0c8 ltac:(cond_compute).

stepn F_4f0ec D_4f0ec. rewrite Ha0.

stepn F_4f0f0 D_4f0f0.

stepn F_4eeac D_4eeac. sp_renorm.
stepST F_4eeb0 D_4eeb0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50ed0) ltac:(sok_stack SOK).
stepST F_4eeb4 D_4eeb4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST F_4eeb8 D_4eeb8 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
stepST F_4eebc D_4eebc (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
stepST F_4eec0 D_4eec0 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).

stepn F_4eec4 D_4eec4.
stepn F_4eec8 D_4eec8.
stepn F_4eecc D_4eecc.
stepn F_4eed0 D_4eed0.
stepn F_4eed4 D_4eed4.

stepn F_5e774 D_5e774.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_5e778 | reflexivity | exact D_5e778 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_5e77c D_5e77c ltac:(cond_compute).
stepret F_5e96c D_5e96c (0x50cb4 : word) ltac:(bveq).

stepLD8 F_4eed8 D_4eed8 (Z_to_bv 64 0).
stepb_tk F_4eedc D_4eedc ltac:(cond_compute).

stepn F_4ef4c D_4ef4c.
stepST F_4ef50 D_4ef50 (Z_to_bv 64 0x97c48) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).

stepn F_4ef54 D_4ef54.
stepLD8 F_4ef58 D_4ef58 (Z_to_bv 64 0x50ed0).
stepLD8 F_4ef5c D_4ef5c code.
stepLD8 F_4ef60 D_4ef60 (getr regs 9).
stepLD8 F_4ef64 D_4ef64 (getr regs 18).
stepLD8 F_4ef68 D_4ef68 (getr regs 19).
stepn F_4ef6c D_4ef6c. sp_renorm.
stepn F_4ef70 D_4ef70.

stepLD F_5e9fc D_5e9fc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
try rewrite (v_lw_small 0) by lia.
stepb_ft F_5ea00 D_5ea00 ltac:(cond_compute).
stepret F_5ea04 D_5ea04 (0x50ed0 : word) ltac:(bveq).

stepn F_4f0f4 D_4f0f4.
apply mst_refl.
- repeat split; gres; try reflexivity. exact Htp.
Qed.

#[using="Type"] Lemma w1 : forall (armed : bool) regs mem rom (sp tp code : word) (tid : Z),
getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
(168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
(0 < tid < 2147483648)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
rdn RSEGS mem (Z_to_bv 64 0x97e93) 1%nat = Some [Z_to_bv 8 0] ->
atx_state armed mem ->
exists regs',
msteps RSEGS (mkst regs (0x50e6c : word) mem rom)
(mkst regs' (0x50e20 : word) (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) rom)
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
/\ getr regs' 8 = code
/\ getr regs' 1 = Z_to_bv 64 0x50ed4
/\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
intros [|]; [exact w1A | exact w1I].
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50ed4)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
(Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e50)))
(Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x62688)))
(Z_to_bv 64 0x66f78) [Z_to_bv 8 1].

#[using="Type"] Lemma w2 : forall regs mem rom (sp code s1v : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0x50ed4 -> getr regs 9 = s1v ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
rdn RSEGS mem (Z_to_bv 64 0x659d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62690)) ->
rdn RSEGS mem (Z_to_bv 64 0x659e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62688)) ->
rdn RSEGS mem (Z_to_bv 64 0x62688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20af4)) ->
rdn RSEGS mem (Z_to_bv 64 0x66f78) 1%nat = Some [Z_to_bv 8 0] ->
rdn RSEGS mem (Z_to_bv 64 0x65898) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50d50)) ->
rdn RSEGS mem (Z_to_bv 64 0x669f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x669f8)) ->
rdn RSEGS mem (Z_to_bv 64 0x658a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
exists regs',
msteps RSEGS (mkst regs (0x50e20 : word) mem rom)
(mkst regs' (0x54d7c : word) (mem_w2 mem sp code s1v) rom)
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
/\ getr regs' 8 = code
/\ getr regs' 1 = Z_to_bv 64 0x50ed8
/\ getr regs' 9 = s1v
/\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
zaddr Mdso.
unfold mem_w2. eexists. split.
-
stepn F_4f044 D_4f044. rewrite Hsp. sp_renorm.
stepST F_4f048 D_4f048 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50ed4) ltac:(sok_stack SOK).
stepST F_4f04c D_4f04c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
stepST F_4f050 D_4f050 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).

stepn F_4f054 D_4f054.
stepn F_4f058 D_4f058.
stepLD8 F_4f05c D_4f05c (Z_to_bv 64 0x62690).
stepLD8 F_4f060 D_4f060 (Z_to_bv 64 0x62688).

stepb_ft F_4f064 D_4f064 ltac:(cond_compute).

stepLD8 F_4f068 D_4f068 (Z_to_bv 64 0x20af4).
stepn F_4f06c D_4f06c.
stepjr F_4f070 D_4f070 (Z_to_bv 64 0x20af4) ltac:(gres; reflexivity). vnorm.

stepn F_208d0 D_208d0. sp_renorm.
stepST F_208d4 D_208d4 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x50e50) ltac:(sok_stack SOK).
stepST F_208d8 D_208d8 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x62688) ltac:(sok_stack SOK).
stepn F_208dc D_208dc.
stepn F_208e0 D_208e0.
stepn F_208e4 D_208e4.

stepLBU F_208e8 D_208e8 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
stepn F_208ec D_208ec.
stepb_tk F_208f0 D_208f0 ltac:(cond_compute).
stepn F_208fc D_208fc.
stepn F_20900 D_20900.
stepn F_20904 D_20904.

stepST F_20908 D_20908 (Z_to_bv 64 0x66f78) (Z_to_bv 64 1) ltac:(sok_data).
change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).

stepn F_2090c D_2090c.
stepLD8 F_20910 D_20910 (Z_to_bv 64 0x50d50).
stepb_ft F_20914 D_20914 ltac:(cond_compute).
stepn F_20918 D_20918.
stepn F_2091c D_2091c.
stepn F_20920 D_20920.
stepLD8 F_20924 D_20924 (Z_to_bv 64 0x669f8).
stepn F_20928 D_20928.
stepret F_4ef74 D_4ef74 (0x20b50 : word) ltac:(bveq).
stepn F_2092c D_2092c.

stepn F_20930 D_20930.
stepLD8 F_20934 D_20934 (Z_to_bv 64 0).
stepb_tk F_20938 D_20938 ltac:(cond_compute).

stepLD8 F_20950 D_20950 (Z_to_bv 64 0x50e50).
stepLD8 F_20954 D_20954 (Z_to_bv 64 0x62688).
stepn F_20958 D_20958. sp_renorm.
stepret F_2095c D_2095c (0x50e50 : word) ltac:(bveq).

stepn F_4f074 D_4f074.
stepb_ft F_4f078 D_4f078 ltac:(cond_compute).
stepLD8 F_4f07c D_4f07c (Z_to_bv 64 0x50ed4).
stepLD8 F_4f080 D_4f080 code.
stepLD8 F_4f084 D_4f084 s1v.
stepn F_4f088 D_4f088. sp_renorm.

stepn F_4f08c D_4f08c.
stepret F_4f040 D_4f040 (0x50ed4 : word) ltac:(bveq).
stepn F_4f0f8 D_4f0f8.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UkD9 U8Sj UpBo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import UFeQ.Mq0 USPu UU2A U8LG UZSc UsN4 UlKb U39n UkD9 U8Sj UJUR Ugw2 UpBo.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50ed8)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x54d8c)))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

#[using="Type"] Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0x50ed8 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globals mem ->
file_clean mem 0x66e28 wp1 rp1 ->
file_clean mem 0x66d38 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0x54d7c : word) mem rom)
(mkst regs' (0x50c44 : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr)
(F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
unfold mem_w3a. eexists. split.
-
stepn F_52fa0 D_52fa0. rewrite Hsp. sp_renorm.
stepST F_52fa4 D_52fa4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50ed8) ltac:(sok_stack SOK).
stepST F_52fa8 D_52fa8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).

stepn F_52fac D_52fac.
stepn F_53334 D_53334. sp_renorm.
stepST F_53338 D_53338 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x54d8c) ltac:(sok_stack SOK).
stepST F_5333c D_5333c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
stepn F_53340 D_53340.
stepn F_53344 D_53344.
stepn F_53348 D_53348.

stepn F_5334c D_5334c.
stepn F_5e774 D_5e774.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_5e778 | reflexivity | exact D_5e778 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_5e77c D_5e77c ltac:(cond_compute).
stepret F_5e96c D_5e96c (0x5512c : word) ltac:(bveq).

stepn F_53350 D_53350.
stepLD8 F_53354 D_53354 (Z_to_bv 64 0x54d8c).
stepLD8 F_53358 D_53358 code.
stepn F_5335c D_5335c. sp_renorm.
stepret F_53360 D_53360 (0x54d8c : word) ltac:(bveq).

stepLD8 F_52fb0 D_52fb0 (Z_to_bv 64 0).
stepb_ft F_52fb4 D_52fb4 ltac:(cond_compute).

stepn F_52fb8 D_52fb8.
stepLD8 F_52fbc D_52fbc (Z_to_bv 64 0).
stepb_tk F_52fc0 D_52fc0 ltac:(cond_compute).

stepn F_53014 D_53014.
stepLD8 F_53018 D_53018 (Z_to_bv 64 0x66e28).
stepb_ft F_5301c D_5301c ltac:(cond_compute).

stepLD F_53020 D_53020 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_53024 D_53024 ltac:(cond_compute).

stepLD8 F_53030 D_53030 wp1.
stepLD8 F_53034 D_53034 wp1.
stepb_tk F_53038 D_53038 ltac:(apply c_eq_refl).

stepLD8 F_53050 D_53050 rp1.
stepLD8 F_53054 D_53054 rp1.
stepb_tk F_53058 D_53058 ltac:(apply c_eq_refl).

stepn F_53070 D_53070.
stepLD8 F_53074 D_53074 (Z_to_bv 64 0x66d38).
stepb_ft F_53078 D_53078 ltac:(cond_compute).
stepLD F_5307c D_5307c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_53080 D_53080 ltac:(cond_compute).
stepLD8 F_5308c D_5308c wp2.
stepLD8 F_53090 D_53090 wp2.
stepb_tk F_53094 D_53094 ltac:(apply c_eq_refl).
stepLD8 F_530ac D_530ac rp2.
stepLD8 F_530b0 D_530b0 rp2.
stepb_tk F_530b4 D_530b4 ltac:(apply c_eq_refl).

stepLD8 F_53134 D_53134 (Z_to_bv 64 0x50ed8).
stepLD8 F_53138 D_53138 code.
stepn F_5313c D_5313c. sp_renorm.
stepret F_53140 D_53140 (0x50ed8 : word) ltac:(bveq).

stepn F_4f0fc D_4f0fc.
stepn F_4f100 D_4f100.
stepn F_4ee60 D_4ee60.
stepn F_4ee64 D_4ee64.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN UqHD UVbU UaUj U6yP Ujor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3 QRjH.Mq4 Qn1e.Mq1 QBxa.Mq3.
Import UeDN UqHD.Mq0 UFeQ.Mq1 UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C1.
Context {fF : FPF} {fC : FPC}.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

#[using="HOK Hn0"] Lemma c1_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom) (mkst regs' (0x5f678 : word) (MK (k + 3)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_5d6d0 D_5d6d0 k.
stepn F_5d6d4 D_5d6d4.
stepb_ft F_5d6d8 D_5d6d8 ltac:(cond).
stepn F_5d6dc D_5d6dc.
stepb_tk F_5d6e0 D_5d6e0 ltac:(cond).
stepn F_5d878 D_5d878.
stepn F_5d87c D_5d87c.
stepn F_5d880 D_5d880.
msb F_5d884 D_5d884 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_5d888 D_5d888 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
msb F_5d88c D_5d88c (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia).
stepn F_5d890 D_5d890.
stepn F_5d894 D_5d894.
stepn F_5d898 D_5d898.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

#[using="HOK Hn0"] Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
(ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f678 : word) (MK kk) rom)
(mkst regs' (0x5f6d8 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_5d89c D_5d89c.
mlw F_5d8a0 D_5d8a0 (kk + 1)%Z.
mlw F_5d8a4 D_5d8a4 (kk + 5)%Z.
mlw F_5d8a8 D_5d8a8 (kk + 9)%Z.
mlw F_5d8ac D_5d8ac (kk + 13)%Z.
stepn F_5d8b0 D_5d8b0. stepn F_5d8b4 D_5d8b4. stepn F_5d8b8 D_5d8b8.
stepn F_5d8bc D_5d8bc. stepn F_5d8c0 D_5d8c0. stepn F_5d8c4 D_5d8c4.
stepn F_5d8c8 D_5d8c8. stepn F_5d8cc D_5d8cc. stepn F_5d8d0 D_5d8d0.
stepn F_5d8d4 D_5d8d4. stepn F_5d8d8 D_5d8d8.
stepn F_5d8dc D_5d8dc.
msw F_5d8e0 D_5d8e0 kk ltac:(m24).
msw F_5d8e4 D_5d8e4 (kk + 4)%Z ltac:(m24).
msw F_5d8e8 D_5d8e8 (kk + 8)%Z ltac:(m24).
msw F_5d8ec D_5d8ec (kk + 12)%Z ltac:(m24).
stepn F_5d8f0 D_5d8f0.
stepn F_5d8f4 D_5d8f4.
stepb_ft F_5d8f8 D_5d8f8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f678 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
/\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
+ eexists. split.
* stepn F_5d89c D_5d89c.
mlw F_5d8a0 D_5d8a0 (kk + 1)%Z.
mlw F_5d8a4 D_5d8a4 (kk + 5)%Z.
mlw F_5d8a8 D_5d8a8 (kk + 9)%Z.
mlw F_5d8ac D_5d8ac (kk + 13)%Z.
stepn F_5d8b0 D_5d8b0. stepn F_5d8b4 D_5d8b4. stepn F_5d8b8 D_5d8b8.
stepn F_5d8bc D_5d8bc. stepn F_5d8c0 D_5d8c0. stepn F_5d8c4 D_5d8c4.
stepn F_5d8c8 D_5d8c8. stepn F_5d8cc D_5d8cc. stepn F_5d8d0 D_5d8d0.
stepn F_5d8d4 D_5d8d4. stepn F_5d8d8 D_5d8d8.
stepn F_5d8dc D_5d8dc.
msw F_5d8e0 D_5d8e0 kk ltac:(m24).
msw F_5d8e4 D_5d8e4 (kk + 4)%Z ltac:(m24).
msw F_5d8e8 D_5d8e8 (kk + 8)%Z ltac:(m24).
msw F_5d8ec D_5d8ec (kk + 12)%Z ltac:(m24).
stepn F_5d8f0 D_5d8f0.
stepn F_5d8f4 D_5d8f4.
stepb_tk F_5d8f8 D_5d8f8 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma c1_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps RSEGS (mkst regs (0x5f6d8 : word) (MK kk) rom)
(mkst regs' (0x5f7f8 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f498 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d8fc D_5d8fc.
stepn F_5d900 D_5d900.
stepb_tk F_5d904 D_5d904 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f6e4 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d8fc D_5d8fc.
stepn F_5d900 D_5d900.
stepb_ft F_5d904 D_5d904 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f770 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="HOK Hn0"] Lemma c1_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3 QRjH.Mq4 Qn1e.Mq1 QBxa.Mq3.
Import UeDN UqHD.Mq0 UFeQ.Mq1 UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C2.
Context {fF : FPF} {fC : FPC}.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

#[using="HOK Hn0"] Lemma c2_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom) (mkst regs' (0x5f4dc : word) (MK (k + 2)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_5d6d0 D_5d6d0 k.
stepn F_5d6d4 D_5d6d4.
stepb_ft F_5d6d8 D_5d6d8 ltac:(cond).
stepn F_5d6dc D_5d6dc.
stepb_ft F_5d6e0 D_5d6e0 ltac:(cond).
stepn F_5d6e4 D_5d6e4.
stepn F_5d6e8 D_5d6e8.
msb F_5d6ec D_5d6ec k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
msb F_5d6f0 D_5d6f0 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).
stepn F_5d6f4 D_5d6f4.
stepn F_5d6f8 D_5d6f8.
stepn F_5d6fc D_5d6fc.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

#[using="HOK Hn0"] Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
(ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f4dc : word) (MK kk) rom)
(mkst regs' (0x5f53c : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_5d700 D_5d700.
mlw F_5d704 D_5d704 (kk + 2)%Z.
mlw F_5d708 D_5d708 (kk + 6)%Z.
mlw F_5d70c D_5d70c (kk + 10)%Z.
mlw F_5d710 D_5d710 (kk + 14)%Z.
stepn F_5d714 D_5d714. stepn F_5d718 D_5d718. stepn F_5d71c D_5d71c.
stepn F_5d720 D_5d720. stepn F_5d724 D_5d724. stepn F_5d728 D_5d728.
stepn F_5d72c D_5d72c. stepn F_5d730 D_5d730. stepn F_5d734 D_5d734.
stepn F_5d738 D_5d738. stepn F_5d73c D_5d73c.
stepn F_5d740 D_5d740.
msw F_5d744 D_5d744 kk ltac:(m16).
msw F_5d748 D_5d748 (kk + 4)%Z ltac:(m16).
msw F_5d74c D_5d74c (kk + 8)%Z ltac:(m16).
msw F_5d750 D_5d750 (kk + 12)%Z ltac:(m16).
stepn F_5d754 D_5d754.
stepn F_5d758 D_5d758.
stepb_ft F_5d75c D_5d75c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f4dc : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
/\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
+ eexists. split.
* stepn F_5d700 D_5d700.
mlw F_5d704 D_5d704 (kk + 2)%Z.
mlw F_5d708 D_5d708 (kk + 6)%Z.
mlw F_5d70c D_5d70c (kk + 10)%Z.
mlw F_5d710 D_5d710 (kk + 14)%Z.
stepn F_5d714 D_5d714. stepn F_5d718 D_5d718. stepn F_5d71c D_5d71c.
stepn F_5d720 D_5d720. stepn F_5d724 D_5d724. stepn F_5d728 D_5d728.
stepn F_5d72c D_5d72c. stepn F_5d730 D_5d730. stepn F_5d734 D_5d734.
stepn F_5d738 D_5d738. stepn F_5d73c D_5d73c.
stepn F_5d740 D_5d740.
msw F_5d744 D_5d744 kk ltac:(m16).
msw F_5d748 D_5d748 (kk + 4)%Z ltac:(m16).
msw F_5d74c D_5d74c (kk + 8)%Z ltac:(m16).
msw F_5d750 D_5d750 (kk + 12)%Z ltac:(m16).
stepn F_5d754 D_5d754.
stepn F_5d758 D_5d758.
stepb_tk F_5d75c D_5d75c ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma c2_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps RSEGS (mkst regs (0x5f53c : word) (MK kk) rom)
(mkst regs' (0x5f7f8 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f498 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d760 D_5d760.
stepn F_5d764 D_5d764.
stepb_tk F_5d768 D_5d768 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f6e4 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d760 D_5d760.
stepn F_5d764 D_5d764.
stepb_ft F_5d768 D_5d768 ltac:(cond).
stepn F_5d76c D_5d76c.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f770 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="HOK Hn0"] Lemma c2_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3 QRjH.Mq4 Qn1e.Mq1 QBxa.Mq3.
Import UeDN UqHD.Mq0 UFeQ.Mq1 UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section C3.
Context {fF : FPF} {fC : FPC}.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
#[local] Notation SB := (sb_ bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlw F D jj :=
chain_step; [reflexivity
| eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
Ltac msw F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].
Ltac msb F D kk valtac :=
mk_at kk;
chain_step; [reflexivity
| eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | valtac | lia | lia]
| step_simpl].

Ltac cond :=
rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
rewrite ?land_3 by lia; lia.
Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

#[using="HOK Hn0"] Lemma c3_pro : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom) (mkst regs' (0x5f5e4 : word) (MK (k + 1)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
/\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
/\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
- mlw F_5d6d0 D_5d6d0 k.
stepn F_5d6d4 D_5d6d4.
stepb_tk F_5d6d8 D_5d6d8 ltac:(cond).
msb F_5d7f4 D_5d7f4 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).
stepn F_5d7f8 D_5d7f8.
stepn F_5d7fc D_5d7fc.
stepn F_5d800 D_5d800.
stepn F_5d804 D_5d804.
mk_eq. apply mst_refl.
- post. unfold v_addi. unorm. f_equal. lia.
Qed.

#[using="HOK Hn0"] Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
(ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
(16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f5e4 : word) (MK kk) rom)
(mkst regs' (0x5f644 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
/\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
/\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
Proof.
induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
- eexists. split.
+ stepn F_5d808 D_5d808.
mlw F_5d80c D_5d80c (kk + 3)%Z.
mlw F_5d810 D_5d810 (kk + 7)%Z.
mlw F_5d814 D_5d814 (kk + 11)%Z.
mlw F_5d818 D_5d818 (kk + 15)%Z.
stepn F_5d81c D_5d81c. stepn F_5d820 D_5d820. stepn F_5d824 D_5d824.
stepn F_5d828 D_5d828. stepn F_5d82c D_5d82c. stepn F_5d830 D_5d830.
stepn F_5d834 D_5d834. stepn F_5d838 D_5d838. stepn F_5d83c D_5d83c.
stepn F_5d840 D_5d840. stepn F_5d844 D_5d844.
stepn F_5d848 D_5d848.
msw F_5d84c D_5d84c kk ltac:(m8).
msw F_5d850 D_5d850 (kk + 4)%Z ltac:(m8).
msw F_5d854 D_5d854 (kk + 8)%Z ltac:(m8).
msw F_5d858 D_5d858 (kk + 12)%Z ltac:(m8).
stepn F_5d85c D_5d85c.
stepn F_5d860 D_5d860.
stepb_ft F_5d864 D_5d864 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
+ post. unfold v_addi. unorm. f_equal. lia.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f5e4 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
/\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
/\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
+ eexists. split.
* stepn F_5d808 D_5d808.
mlw F_5d80c D_5d80c (kk + 3)%Z.
mlw F_5d810 D_5d810 (kk + 7)%Z.
mlw F_5d814 D_5d814 (kk + 11)%Z.
mlw F_5d818 D_5d818 (kk + 15)%Z.
stepn F_5d81c D_5d81c. stepn F_5d820 D_5d820. stepn F_5d824 D_5d824.
stepn F_5d828 D_5d828. stepn F_5d82c D_5d82c. stepn F_5d830 D_5d830.
stepn F_5d834 D_5d834. stepn F_5d838 D_5d838. stepn F_5d83c D_5d83c.
stepn F_5d840 D_5d840. stepn F_5d844 D_5d844.
stepn F_5d848 D_5d848.
msw F_5d84c D_5d84c kk ltac:(m8).
msw F_5d850 D_5d850 (kk + 4)%Z ltac:(m8).
msw F_5d854 D_5d854 (kk + 8)%Z ltac:(m8).
msw F_5d858 D_5d858 (kk + 12)%Z ltac:(m8).
stepn F_5d85c D_5d85c.
stepn F_5d860 D_5d860.
stepb_tk F_5d864 D_5d864 ltac:(unfold v_addi; cond).
mk_eq. apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

#[using="HOK"] Lemma c3_exit : forall regs (ret : word) kk,
getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
getr regs 12 = Z_to_bv 64 (n - kk) ->
(0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
let m := (n - kk)%Z in
exists regs',
msteps RSEGS (mkst regs (0x5f644 : word) (MK kk) rom)
(mkst regs' (0x5f7f8 : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
destruct B16 as [HL16|HL16].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f498 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d868 D_5d868.
stepn F_5d86c D_5d86c.
stepb_tk F_5d870 D_5d870 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f6e4 : word) (MK kk) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d868 D_5d868.
stepn F_5d86c D_5d86c.
stepb_ft F_5d870 D_5d870 ltac:(cond).
stepn F_5d874 D_5d874.
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f770 : word) (MK (kk + 16)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
* destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="HOK Hn0"] Lemma c3_run : forall regs (ret : word) k,
getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
(0 <= k)%Z -> (32 <= n - k)%Z ->
exists regs' m,
msteps RSEGS (mkst regs (0x5f4ac : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
Proof.
intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
{ subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
set (m := (n - kk)%Z).
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
fold kk in RUN2, Q11, Q13, Q12.
destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
fold m in RUN3, S11, S13, S12.
exists r3, m.
assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
rewrite E in RUN3, S11, S13.
split; [| split; [lia | repeat split; try assumption]].
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
- eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uhzw ULxO U5hz UoL3 UuT1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import Uhzw UFeQ ULxO U5hz UoL3 UuT1 USPu UU2A U8LG.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Ubsan.M.phdrs.

Section P3.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).
Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).

Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
Local Notation s := (nth 0 av []) (only parsing).
Local Notation A8 := (Z_to_bv 64 0x97e80) (only parsing).

#[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
#[using="sp0 Hve"] Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
Proof. destruct Hve as [H1 _]. lia. Qed.

#[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
#[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

#[using="Hlo"] Lemma rd_above : forall J D (a : Z) n bs,
(bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
Proof.
intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma rd_envp : forall J D k, (k < length ev)%nat ->
rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
= Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
Proof.
intros J D k Hk. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
exact (read_envp_ptr_k SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_hi' k Hk).
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma rd_envp_null : forall J D,
rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
= Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
intros J D. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
with (sp0 + nat_to_word (envp_off av + 8 * length ev))
by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
exact (read_envp_null SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_hi').
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
nth j (auxv_words RPH rnd a_uid a_hwcap) (Z_to_bv 64 0) = w ->
rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
Proof.
intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_hi' j Hj).
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
(k + n = length ev)%nat ->
getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
(forall regs',
getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
getr regs' 10 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [9; 10]%list) regs regs' ->
G (mkst regs' (0x505d4 : word) (CM J D) rom)) ->
G (mkst regs (0x505c8 : word) (CM J D) rom).
Proof.
intros G HG.
pose proof len_av as Hlen. pose proof len_ev as Hlev.
induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
-
assert (k = length ev) by lia. subst k.
eapply HG.
{ ld_step F_4e7e0 D_4e7e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
sv F_4e7e4 D_4e7e4 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
stepb_ft F_4e7e8 D_4e7e8 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
- assert (Hk : (k < length ev)%nat) by lia.
pose proof (cat_envp_ptr_nz sp0 av ev Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
eapply HG.
{ ld_step F_4e7e0 D_4e7e0 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
sv F_4e7e4 D_4e7e4 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
stepb_tk F_4e7e8 D_4e7e8 ltac:(pin; apply c_eq_0_false; exact Hnz).
apply mst_refl. }
eapply (IH (S k)); [lia | gres; reflexivity |].
intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.

#[using="Hva Hve Hhi"] Lemma pn_bounds :
(bv_unsigned sp0 <= bv_unsigned pn)%Z
/\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
Proof.
pose proof len_av.
exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
Proof.
intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
apply rd_above; [lia | lia |].
replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
by (rewrite word_add_nat; reflexivity).
rewrite <- Hb.
exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j a_uid a_hwcap a_rnd ltac:(lia) Hj
(bsb_nw RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_hi')).
Qed.

#[using="Type"] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof. intros; subst; reflexivity. Qed.

#[using="sp0"] Lemma c_eq_byte47 : forall b : byte,
c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
Proof.
intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
rewrite !u_Z2bv by lia. reflexivity.
Qed.

#[using="sp0"] Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
Proof.
intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
Qed.

#[using="Hva Hve Hlo Hhi"] Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
getr regs 10 = Z_to_bv 64 0x97e80 ->
getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
getr regs 12 = Z_to_bv 64 47 ->
(forall regs',
getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
regs_agree (fun r => In r [11; 13]%list) regs regs' ->
G (mkst regs' (0x50698 : word)
(CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
+ Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
G (mkst regs (0x5068c : word)
(CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
Proof.
intros G HG.
pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
-
assert (Hjl : j = length s).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
eapply HG.
{ lb_step F_4e8a4 D_4e8a4 (Z_to_bv 8 0)
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
stepb_ft F_4e8a8 D_4e8a8 ltac:(pin; cond_compute).
stepb_ft F_4e8ac D_4e8ac ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
- assert (Hjlt : (j < length s)%nat).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
{ rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
assert (Hbnz : b <> Z_to_bv 8 0).
{ intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
assert (Hskip' : skipn (S j) s = l2).
{ replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
cbn [after_last_slash] in Hk0.
destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
+
eapply HG.
{ lb_step F_4e8a4 D_4e8a4 b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_tk F_4e8a8 D_4e8a8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
stw F_4e89c D_4e89c (Z_to_bv 64 0x97e80) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
sv F_4e8a0 D_4e8a0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
+ eapply HG.
{ lb_step F_4e8a4 D_4e8a4 b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_ft F_4e8a8 D_4e8a8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
stepb_tk F_4e8ac D_4e8ac ltac:(pin; apply c_eq_byte0; exact Hbnz).
sv F_4e8a0 D_4e8a0 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.

Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

#[using="Hva Hve Hlo Hhi"] Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
wfJ sp0 Jf ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 8 = pn ->
getr regs 9 = envp_w sp0 av ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
(forall regs',
getr regs' 1 = Z_to_bv 64 0x506a0 ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs' 18 = Z_to_bv 64 0x97e90 ->
regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
G (mkst regs' (0x508b0 : word) (CM (J_aux sp0 av ev Jf) (D_libc sp0 av ev)) rom)) ->
G (mkst regs (0x505bc : word)
(CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
Proof.
intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
unfold envp_w in H9.
eapply HG.
{ sn F_4e7d4 D_4e7d4.
ld_step F_4e7d8 D_4e7d8 (word_to_le_bytes 8 (Z_to_bv 64 0x77b30)) (Z_to_bv 64 0x77b30)
ltac:(rd_img img_63e10_8) ltac:(apply bytes_le_to_Z_8).
stw F_4e7dc D_4e7dc (Z_to_bv 64 0x77b30) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
apply mst_refl. }

eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
intros regs1 H9a H10a Hag1.
carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
clear H9 H10 H8 H2.
eapply HG.
{ sn F_4e7ec D_4e7ec.
sn F_4e7f0 D_4e7f0.
stw F_4e7f4 D_4e7f4 (Z_to_bv 64 0x97e98)
(Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).

ld_step F_4e7f8 D_4e7f8 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_4e7fc D_4e7fc ltac:(pin; cond_compute).
sv F_4e800 D_4e800 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
sn F_4e804 D_4e804.
sv F_4e808 D_4e808 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn F_4e80c D_4e80c.

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 5%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 11) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 a_hwcap) a_hwcap ltac:(rdA 7%nat a_hwcap) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 240)) a_hwcap ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 a_uid) a_uid ltac:(rdA 11%nat a_uid) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 280)) a_uid ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 a_uid) a_uid ltac:(rdA 13%nat a_uid) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 272)) a_uid ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
stepb_ft F_4e818 D_4e818 ltac:(pin; cond_compute).

stepb_ft F_4e81c D_4e81c ltac:(pin; cond_compute).
ld_step F_4e820 D_4e820 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
sn F_4e824 D_4e824.
sv F_4e828 D_4e828 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
stw F_4e82c D_4e82c (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
sn F_4e830 D_4e830.
ld_step F_4e810 D_4e810 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sv F_4e814 D_4e814 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
stepb_tk F_4e818 D_4e818 ltac:(pin; cond_compute).

ld_step F_4e834 D_4e834 (word_to_le_bytes 8 a_hwcap) a_hwcap
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e838 D_4e838 (zeros 8) (Z_to_bv 64 0)
ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
ltac:(reflexivity).
sn F_4e83c D_4e83c.
stw F_4e840 D_4e840 (Z_to_bv 64 0x97ef8) a_hwcap ltac:(ok_data).
stepb_tk F_4e844 D_4e844 ltac:(pin; cond_compute).

ld_step F_4e85c D_4e85c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stw F_4e860 D_4e860 (Z_to_bv 64 0x97ec0) (Z_to_bv 64 4096) ltac:(ok_data).
stepb_tk F_4e864 D_4e864 ltac:(pin; apply c_eq_0_false; lia).
stepb_tk F_4e86c D_4e86c ltac:(pin; apply c_eq_0_false; lia).

sn F_4e878 D_4e878.
ld_step F_4e87c D_4e87c (word_to_le_bytes 8 (Z_to_bv 64 0x97e88)) (Z_to_bv 64 0x97e88)
ltac:(rd_img img_63e18_8) ltac:(apply bytes_le_to_Z_8).
sn F_4e880 D_4e880.
ld_step F_4e884 D_4e884 (word_to_le_bytes 8 (Z_to_bv 64 0x97e80)) (Z_to_bv 64 0x97e80)
ltac:(rd_img img_63e20_8) ltac:(apply bytes_le_to_Z_8).
stw F_4e888 D_4e888 (Z_to_bv 64 0x97e88) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
sv F_4e88c D_4e88c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).
stw F_4e890 D_4e890 (Z_to_bv 64 0x97e80) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
sn F_4e894 D_4e894.
sn F_4e898 D_4e898.
apply mst_refl. }

eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
intros regs2 H11b Hag2.
carry Hag2 H2a (2 : reg) H2b.
eapply HG.
{ sv F_4e8b0 D_4e8b0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn F_4e8b4 D_4e8b4.
apply mst_refl. }
apply Hk.
- gres; bveq.
- gres; exact H2b.
- gres; reflexivity.
- gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
- ra_chain.
Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import Uhzw UFeQ USPu UU2A U8LG UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR Ugw2 UpBo.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Variable sp0 : word.
Variable Jb : word -> option byte.
Variables av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).

#[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Ltac rd_win8 := rewrite rdn_cmem_win by region_side; rd_hit8.

Ltac PREP tid := pose proof len_av as Hlen; pose proof (u64_range tid) as Htid;
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.

#[using="Hva Hlo Hhi"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 0x506a0) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 8 = (pn_w sp0 av ev) ->
getr regs 9 = x9v ->
getr regs 10 = (Z_to_bv 64 (bv_unsigned sp0 - 368)) ->
getr regs 18 = (Z_to_bv 64 0x97e90) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 0x97e90) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 0x97c08) ->
getr regs' 13 = (Z_to_bv 64 11) ->
getr regs' 15 = (Z_to_bv 64 0x10040) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 0x6474e551) ->
getr regs' 29 = (Z_to_bv 64 0x10040) ->
getr regs' 30 = (Z_to_bv 64 0x20000) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x50938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom)) ->
G (mkst regs (0x508b0 : word) (CM (J_aux sp0 av ev (J_lsm sp0 av Jb)) (D_libc sp0 av ev)) rom).
Proof.
intros G HG regs rom tid x9v HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ sv F_4eb28 D_4eb28 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_4eb2c D_4eb2c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 0x506a0) ltac:(ok_win HJ).
stw F_4eb30 D_4eb30 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_4eb34 D_4eb34 (Z_to_bv 64 (bv_unsigned sp0 - 440)) x9v ltac:(ok_win HJ).
stw F_4eb38 D_4eb38 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 0x97e90) ltac:(ok_win HJ).
stw F_4eb3c D_4eb3c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4eb40 D_4eb40 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4eb44 D_4eb44 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_4eb48 D_4eb48 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sn F_4eb4c D_4eb4c.
sn F_4eb50 D_4eb50.
sn F_4eb54 D_4eb54.
sn F_4eb58 D_4eb58.
stepb_ft F_4eb5c D_4eb5c ltac:(pin; cond_compute).
sn F_4eb60 D_4eb60.
sn F_4eb64 D_4eb64.
sn F_4eb68 D_4eb68.
ld_step F_4eb6c D_4eb6c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4eb70 D_4eb70 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sn F_4eb74 D_4eb74.
sn F_4eb78 D_4eb78.
ld_step F_4eb7c D_4eb7c (word_to_le_bytes 4 (Z_to_bv 64 0x20000)) (Z_to_bv 64 0x20000) ltac:(rd_img img_65140_4) ltac:(vm_compute; reflexivity).
ld_step F_4eb80 D_4eb80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_63cd8_8) ltac:(apply bytes_le_to_Z_8).
sn F_4eb84 D_4eb84.
sn F_4eb88 D_4eb88.
sn F_4eb8c D_4eb8c.
sn F_4eb90 D_4eb90.
sn F_4eb94 D_4eb94.
sn F_4eb98 D_4eb98.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo"] Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 9 = (Z_to_bv 64 0x97e90) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 0x97c08) ->
getr regs 13 = (Z_to_bv 64 11) ->
getr regs 15 = (Z_to_bv 64 0x10040) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 17 = (Z_to_bv 64 0) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
getr regs 28 = (Z_to_bv 64 0x6474e551) ->
getr regs 29 = (Z_to_bv 64 0x10040) ->
getr regs 30 = (Z_to_bv 64 0x20000) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 0x97e90) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 0x97c08) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 6) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 0x6474e551) ->
getr regs' 29 = (Z_to_bv 64 0x10158) ->
getr regs' 30 = (Z_to_bv 64 0x20000) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x50938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom)) ->
G (mkst regs (0x50938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
PREP tid.
eapply HG.
{ ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
ld_step F_4eb9c D_4eb9c (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_4eba0 D_4eba0.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo"] Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 5 = (Z_to_bv 64 0) ->
getr regs 7 = (Z_to_bv 64 7) ->
getr regs 9 = (Z_to_bv 64 0x97e90) ->
getr regs 10 = (Z_to_bv 64 56) ->
getr regs 11 = (Z_to_bv 64 0x97c08) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 13 = (Z_to_bv 64 6) ->
getr regs 16 = (Z_to_bv 64 6) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
getr regs 28 = (Z_to_bv 64 0x6474e551) ->
getr regs 29 = (Z_to_bv 64 0x10158) ->
getr regs 30 = (Z_to_bv 64 0x20000) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 9 = (Z_to_bv 64 0x97e90) ->
getr regs' 11 = (Z_to_bv 64 0x97c08) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 17 = (Z_to_bv 64 0x10158) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x50988 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom)) ->
G (mkst regs (0x50938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H5 H7 H9 H10 H11 H12 H13 H16 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
PREP tid.
eapply HG.
{ ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_tk F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e552)) (Z_to_bv 64 0x6474e552) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e550)) (Z_to_bv 64 0x6474e550) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 0x6474e551)) (Z_to_bv 64 0x6474e551) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_ft F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
ld_step F_4ebdc D_4ebdc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10228_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_4ebe0 D_4ebe0 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_ft F_4ebac D_4ebac ltac:(pin; cond_compute).
ld_step F_4ebb0 D_4ebb0 (word_to_le_bytes 4 (Z_to_bv 64 0x70000003)) (Z_to_bv 64 0x70000003) ltac:(rd_img img_10270_4) ltac:(vm_compute; reflexivity).
stepb_ft F_4ebb4 D_4ebb4 ltac:(pin; cond_compute).
stepb_tk F_4ebb8 D_4ebb8 ltac:(pin; cond_compute).
sn F_4ebcc D_4ebcc.
stepb_ft F_4ebd0 D_4ebd0 ltac:(pin; cond_compute).
sn F_4ebd4 D_4ebd4.
stepb_tk F_4ebd8 D_4ebd8 ltac:(pin; cond_compute).
sn F_4ebf8 D_4ebf8.
sn F_4ebfc D_4ebfc.
sn F_4eba4 D_4eba4.
sn F_4eba8 D_4eba8.
stepb_tk F_4ebac D_4ebac ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import Uhzw UFeQ USPu UU2A U8LG UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR Ugw2 UpBo.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P5.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Variable sp0 : word.
Variable Jb : word -> option byte.
Variables av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).

#[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Ltac rd_dat := rewrite rdn_cmem_data by region_side; rd_hit8.
Ltac rd_win8 := rewrite rdn_cmem_win by region_side; rd_hit8.

Ltac PREP tid := pose proof len_av as Hlen; pose proof (u64_range tid) as Htid;
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.

#[using="Hva Hlo"] Lemma tls_c4a : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 9 = (Z_to_bv 64 0x97e90) ->
getr regs 11 = (Z_to_bv 64 0x97c08) ->
getr regs 12 = (Z_to_bv 64 0) ->
getr regs 17 = (Z_to_bv 64 0x10158) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 9 = (Z_to_bv 64 0x97e90) ->
getr regs' 10 = (Z_to_bv 64 8) ->
getr regs' 11 = (Z_to_bv 64 232) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs' ->
G (mkst regs' (0x50a50 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8)))) rom)) ->
G (mkst regs (0x50988 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev)) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H9 H11 H12 H17 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ stepb_ft F_4ec00 D_4ec00 ltac:(pin; cond_compute).
sn F_4ec04 D_4ec04.
ld_step F_4ec08 D_4ec08 (word_to_le_bytes 8 (Z_to_bv 64 0x61680)) (Z_to_bv 64 0x61680) ltac:(rd_img img_10168_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ec0c D_4ec0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_10178_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ec10 D_4ec10 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10180_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ec14 D_4ec14 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rd_img img_10188_8) ltac:(apply bytes_le_to_Z_8).
sn F_4ec18 D_4ec18.
sn F_4ec1c D_4ec1c.
stw F_4ec20 D_4ec20 (Z_to_bv 64 0x97c18) (Z_to_bv 64 0x61680) ltac:(ok_data).
stw F_4ec24 D_4ec24 (Z_to_bv 64 0x97c20) (Z_to_bv 64 0) ltac:(ok_data).
stw F_4ec28 D_4ec28 (Z_to_bv 64 0x97c30) (Z_to_bv 64 8) ltac:(ok_data).
stw F_4ec2c D_4ec2c (Z_to_bv 64 0x97ea0) (Z_to_bv 64 0x97c10) ltac:(ok_data).
stw F_4ec30 D_4ec30 (Z_to_bv 64 0x97eb8) (Z_to_bv 64 1) ltac:(ok_data).
sn F_4ec34 D_4ec34.
sn F_4ec44 D_4ec44.
sn F_4ec48 D_4ec48.
sn F_4ec4c D_4ec4c.
sn F_4ec50 D_4ec50.
sn F_4ec54 D_4ec54.
sn F_4ec58 D_4ec58.
sn F_4ec5c D_4ec5c.
stw F_4ec60 D_4ec60 (Z_to_bv 64 0x97c28) (Z_to_bv 64 8) ltac:(ok_data).
stw F_4ec64 D_4ec64 (Z_to_bv 64 0x97c38) (Z_to_bv 64 0) ltac:(ok_data).
stepb_tk F_4ec68 D_4ec68 ltac:(pin; cond_compute).
sn F_4ec74 D_4ec74.
sn F_4ec78 D_4ec78.
sn F_4ec7c D_4ec7c.
sn F_4ec80 D_4ec80.
sn F_4ec84 D_4ec84.
sn F_4ec88 D_4ec88.
stw F_4ec8c D_4ec8c (Z_to_bv 64 0x97ea8) (Z_to_bv 64 232) ltac:(ok_data).
stw F_4ec90 D_4ec90 (Z_to_bv 64 0x97eb0) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_4ec94 D_4ec94 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo"] Lemma tls_c4b : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 9 = (Z_to_bv 64 0x97e90) ->
getr regs 10 = (Z_to_bv 64 8) ->
getr regs 11 = (Z_to_bv 64 232) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 10 = (Z_to_bv 64 0x97c08) ->
getr regs' 11 = (Z_to_bv 64 0x97ec8) ->
getr regs' 12 = (Z_to_bv 64 1) ->
getr regs' 13 = (Z_to_bv 64 0x77c00) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 0) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 0x77b38) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0x77c10) ->
getr regs' 21 = (Z_to_bv 64 0x77c20) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x50b0c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x50a50 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8)))) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H9 H10 H11 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ sn F_4ecc8 D_4ecc8.
ld_step F_4eccc D_4eccc (word_to_le_bytes 8 (Z_to_bv 64 0x97c10)) (Z_to_bv 64 0x97c10) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ecd0 D_4ecd0 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
sn F_4ecd4 D_4ecd4.
sn F_4ecd8 D_4ecd8.
sn F_4ecdc D_4ecdc.
sn F_4ece0 D_4ece0.
sn F_4ece4 D_4ece4.
sn F_4ece8 D_4ece8.
sn F_4ecec D_4ecec.
sn F_4ecf0 D_4ecf0.
sn F_4ecf4 D_4ecf4.
sn F_4ecf8 D_4ecf8.
sn F_4ecfc D_4ecfc.
stepb_ft F_4ed00 D_4ed00 ltac:(pin; cond_compute).
sn F_4ed04 D_4ed04.
sn F_4ed08 D_4ed08.
sn F_4ed0c D_4ed0c.
ld_step F_4ed10 D_4ed10 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
sn F_4ed14 D_4ed14.
sn F_4ed18 D_4ed18.
sn F_4ed1c D_4ed1c.
stw F_4ed20 D_4ed20 (Z_to_bv 64 0x77c18) (Z_to_bv 64 0x78400) ltac:(ok_data).
ld_step F_4ed24 D_4ed24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ed28 D_4ed28 (word_to_le_bytes 8 (Z_to_bv 64 0x61680)) (Z_to_bv 64 0x61680) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ed2c D_4ed2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
sn F_4ed30 D_4ed30.
sn F_4ed34 D_4ed34.
sn F_5d65c D_5d65c.
stepb_tk F_5d660 D_5d660 ltac:(pin; cond_compute).
sn F_5d770 D_5d770.
sn F_5d774 D_5d774.
stepb_ft F_5d778 D_5d778 ltac:(pin; cond_compute).
sn F_5d77c D_5d77c.
stepb_tk F_5d780 D_5d780 ltac:(pin; cond_compute).
sn F_5d7b8 D_5d7b8.
stepb_tk F_5d7bc D_5d7bc ltac:(pin; cond_compute).
sn F_5d7d8 D_5d7d8.
stepb_tk F_5d7dc D_5d7dc ltac:(pin; cond_compute).
sn F_5da1c D_5da1c.
stepb_ft F_5da20 D_5da20 ltac:(pin; cond_compute).
sn F_5da24 D_5da24.
stepb_ft F_5da28 D_5da28 ltac:(pin; cond_compute).
stepret F_5da2c D_5da2c (0x50ac0 : word) ltac:(pin; first [reflexivity | bveq]).
ld_step F_4ed38 D_4ed38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_75d60_8) ltac:(apply bytes_le_to_Z_8).
sn F_4ed3c D_4ed3c.
stepb_ft F_4ed40 D_4ed40 ltac:(pin; cond_compute).
ld_step F_4ed44 D_4ed44 (word_to_le_bytes 8 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_dat) ltac:(apply bytes_le_to_Z_8).
stw F_4ed48 D_4ed48 (Z_to_bv 64 0x77c10) (Z_to_bv 64 1) ltac:(ok_data).
stw F_4ed4c D_4ed4c (Z_to_bv 64 0x77bf8) (Z_to_bv 64 0x77c10) ltac:(ok_data).
stw F_4ed50 D_4ed50 (Z_to_bv 64 0x77b38) (Z_to_bv 64 0x77b38) ltac:(ok_data).
sn F_4ed54 D_4ed54.
sn F_4ed58 D_4ed58.
sn F_5f094 D_5f094.
sn F_5f098 D_5f098.
stepret F_5f09c D_5f09c (0x50ae4 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_4ed5c D_4ed5c ltac:(pin; cond_compute).
stepb_ft F_4ed60 D_4ed60 ltac:(pin; cond_compute).
sn F_4ed64 D_4ed64.
stw F_4ed68 D_4ed68 (Z_to_bv 64 0x97e90) (Z_to_bv 64 1) ltac:(ok_data).
sn F_4ed6c D_4ed6c.
sn F_4ed70 D_4ed70.
stw F_4ed74 D_4ed74 (Z_to_bv 64 0x77b60) (Z_to_bv 64 2) ltac:(ok_data).
sn F_4ed78 D_4ed78.
sn F_4ed7c D_4ed7c.
sn F_4ed80 D_4ed80.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo Hhi"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 4 = (Z_to_bv 64 0x77c00) ->
getr regs 10 = tid ->
getr regs 11 = (Z_to_bv 64 0x97ec8) ->
getr regs 18 = (Z_to_bv 64 0x77b38) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0x77c10) ->
getr regs 21 = (Z_to_bv 64 0x77c20) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x506a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x50b10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H4 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ sn F_4ed88 D_4ed88.
stw F_4ed8c D_4ed8c (Z_to_bv 64 0x77b58) tid ltac:(ok_data).
stw F_4ed90 D_4ed90 (Z_to_bv 64 0x77bd0) (Z_to_bv 64 0x97ec8) ltac:(ok_data).
stw F_4ed94 D_4ed94 (Z_to_bv 64 0x77bb0) (Z_to_bv 64 0x77bb0) ltac:(ok_data).
sn F_4ed98 D_4ed98.
ld_step F_4ed9c D_4ed9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_76118_8) ltac:(apply bytes_le_to_Z_8).
stw F_4eda0 D_4eda0 (Z_to_bv 64 0x77b40) (Z_to_bv 64 0x77b38) ltac:(ok_data).
stw F_4eda4 D_4eda4 (Z_to_bv 64 0x77b48) (Z_to_bv 64 0x77b38) ltac:(ok_data).
stw F_4eda8 D_4eda8 (Z_to_bv 64 0x77b50) (Z_to_bv 64 0) ltac:(ok_data).
sn F_4edac D_4edac.
ld_step F_4edb4 D_4edb4 (word_to_le_bytes 8 (Z_to_bv 64 0x506a0)) (Z_to_bv 64 0x506a0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edb8 D_4edb8 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edbc D_4edbc (word_to_le_bytes 8 x9v) x9v ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edc0 D_4edc0 (word_to_le_bytes 8 (Z_to_bv 64 0x97e90)) (Z_to_bv 64 0x97e90) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edc4 D_4edc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edc8 D_4edc8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4edcc D_4edcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_4edd0 D_4edd0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_4edd4 D_4edd4 (0x506a0 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import Uhzw UFeQ U1SW ULxO U5hz UoL3 UuT1 USPu UU2A U8LG UVbU UaUj U6yP Ujor UkD9 U8Sj UJUR.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Variable sp0 : word.
Variable Jb : word -> option byte.
Variables av ev : list (list byte).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd)) (only parsing).

#[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
#[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
#[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

Ltac rd_win8 := rewrite rdn_cmem_win by region_side; rd_hit8.

Ltac rd_winz := rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia.
Ltac PREP tid := pose proof len_av as Hlen; pose proof (u64_range tid) as Htid;
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.

#[using="AMB Hva Hve Hlo Hhi Hal"] Lemma rnd_bounds :
(bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
/\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
/\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
Proof.
destruct (rnd_facts SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
unfold rnd_w. repeat split; lia.
Qed.

#[using="Hva Hve Hlo Hhi Hal"] Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
= Some (firstn n (skipn j rnd_bytes)).
Proof.
intros J D j n Hjn.
destruct (rnd_facts SEGS RPH sp0 av ev a_uid a_hwcap a_rnd Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
unfold rnd_w, rnd_bytes. rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.

#[using="Type"] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof. intros; subst; reflexivity. Qed.

Ltac RD_RND j :=
eapply rdn_addr; [ etransitivity; [apply (rd_rnd _ _ j); cbn; lia | reflexivity]
| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

Ltac RD_GUARD :=
rewrite rdn_cmem_data by region_side; unfold canary_bytes; apply rdn_guard3; lia.

#[using="sp0 Hva"] Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
Proof.
pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.

#[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 4 = (Z_to_bv 64 0x77c00) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
G (mkst regs' (0x506a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom)) ->
G (mkst regs (0x506a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ ld_step F_4e8b8 D_4e8b8 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sn F_4e8bc D_4e8bc.
sv F_4f1e8 D_4f1e8 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
stw F_4f1ec D_4f1ec (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 0x506a8) ltac:(ok_win HJ).
stepb_ft F_4f1f0 D_4f1f0 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
sv F_4f1f4 D_4f1f4 (rnd_w sp0 av ev).
sn F_4f1f8 D_4f1f8.
ld_step F_4f1fc D_4f1fc (word_to_le_bytes 8 (Z_to_bv 64 0x97e70)) (Z_to_bv 64 0x97e70) ltac:(rd_img img_63e38_8) ltac:(apply bytes_le_to_Z_8).
sn F_4f200 D_4f200.
sn F_4f204 D_4f204.
stepiv F_5d65c D_5d65c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
stepb_tk F_5d660 D_5d660 ltac:(pin; cond_compute).
sn F_5d770 D_5d770.
sn F_5d774 D_5d774.
stepb_ft F_5d778 D_5d778 ltac:(pin; cond_compute).
sn F_5d77c D_5d77c.
stepb_tk F_5d780 D_5d780 ltac:(pin; cond_compute).
sn F_5d7b8 D_5d7b8.
stepb_ft F_5d7bc D_5d7bc ltac:(pin; cond_compute).
ld_step F_5d7c0 D_5d7c0 [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3] (le_bytes_to_word [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) ltac:(RD_RND 0%nat) ltac:(apply bytes_le_to_Z_of_word; cbn; lia).
ld_step F_5d7c4 D_5d7c4 [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7] (le_bytes_to_word [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) ltac:(RD_RND 4%nat) ltac:(apply bytes_le_to_Z_of_word; cbn; lia).
stw F_5d7c8 D_5d7c8 (Z_to_bv 64 0x97e70) (v_lw (le_bytes_to_word [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3])) ltac:(ok_data). rewrite (w2lb4_lw [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) by reflexivity.
stw F_5d7cc D_5d7cc (Z_to_bv 64 0x97e74) (v_lw (le_bytes_to_word [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7])) ltac:(ok_data). rewrite (w2lb4_lw [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) by reflexivity.
sn F_5d7d0 D_5d7d0.
sv F_5d7d4 D_5d7d4 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
sn F_5d7d8 D_5d7d8.
stepb_tk F_5d7dc D_5d7dc ltac:(pin; cond_compute).
sn F_5da1c D_5da1c.
stepb_ft F_5da20 D_5da20 ltac:(pin; cond_compute).
sn F_5da24 D_5da24.
stepb_ft F_5da28 D_5da28 ltac:(pin; cond_compute).
stepret F_5da2c D_5da2c (0x50fe4 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_4f208 D_4f208.
sn F_4f224 D_4f224.
ld_step F_4f228 D_4f228 (word_to_le_bytes 8 (Z_to_bv 64 0x97e70)) (Z_to_bv 64 0x97e70) ltac:(rd_img img_63e38_8) ltac:(apply bytes_le_to_Z_8).
stw F_4f22c D_4f22c (Z_to_bv 64 0x97e71) (Z_to_bv 64 0) ltac:(ok_data).
ld_step F_4f230 D_4f230 canary_bytes ssp_canary ltac:(RD_GUARD) ltac:(symmetry; apply u_ssp_canary).
sn F_4f234 D_4f234.
stw F_4f238 D_4f238 (Z_to_bv 64 0x77bf0) ssp_canary ltac:(ok_data).
ld_step F_4f23c D_4f23c (word_to_le_bytes 8 (Z_to_bv 64 0x506a8)) (Z_to_bv 64 0x506a8) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_4f240 D_4f240 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_4f244 D_4f244 (0x506a8 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo Hhi"] Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 4 = (Z_to_bv 64 0x77c00) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 0) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 + 0)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 8 = (Z_to_bv 64 0) ->
getr regs' 9 = (Z_to_bv 64 0) ->
getr regs' 10 = (Z_to_bv 64 0x20b84) ->
getr regs' 11 = (argc_w av) ->
getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
getr regs' 18 = (Z_to_bv 64 0) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
G (mkst regs' (0x50868 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom)) ->
G (mkst regs (0x506a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom).
Proof.
intros G HG regs rom tid x9v HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ ld_step F_4e8c0 D_4e8c0 (word_to_le_bytes 8 a_uid) a_uid ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e8c4 D_4e8c4 (word_to_le_bytes 8 a_uid) a_uid ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_4e8c8 D_4e8c8 ltac:(pin; apply c_eq_refl).
ld_step F_4e8cc D_4e8cc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_winz) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e8d0 D_4e8d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_winz) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_4e8d4 D_4e8d4 ltac:(pin; cond_compute).
ld_step F_4e8d8 D_4e8d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_4e8dc D_4e8dc ltac:(pin; cond_compute).
ld_step F_4e9bc D_4e9bc (word_to_le_bytes 8 (Z_to_bv 64 0x5083c)) (Z_to_bv 64 0x5083c) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e9c0 D_4e9c0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e9c4 D_4e9c4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e9c8 D_4e9c8 (word_to_le_bytes 8 (Z_to_bv 64 0x20b84)) (Z_to_bv 64 0x20b84) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_4e9cc D_4e9cc (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stepret F_4e9d0 D_4e9d0 (0x5083c : word) ltac:(pin; first [reflexivity | bveq]).
sn F_4ea54 D_4ea54.
sn F_4ea58 D_4ea58.
sn F_4ea5c D_4ea5c.
sv F_4ea60 D_4ea60 (argc_w av).
sv F_4ea64 D_4ea64 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
ld_step F_4ea68 D_4ea68 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ea6c D_4ea6c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ea70 D_4ea70 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ea74 D_4ea74 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_4ea78 D_4ea78 (Z_to_bv 64 (bv_unsigned sp0 + 0)).
stepret F_4ea7c D_4ea7c (0x50868 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo Hhi"] Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 0) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 + 0)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 4 = (Z_to_bv 64 0x77c00) ->
getr regs 8 = (Z_to_bv 64 0) ->
getr regs 9 = (Z_to_bv 64 0) ->
getr regs 10 = (Z_to_bv 64 0x20b84) ->
getr regs 11 = (argc_w av) ->
getr regs 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
getr regs 18 = (Z_to_bv 64 0) ->
getr regs 19 = (Z_to_bv 64 0) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 0x507ec) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 8 = (Z_to_bv 64 0x62688) ->
getr regs' 9 = (Z_to_bv 64 0x62680) ->
getr regs' 18 = (Z_to_bv 64 0x20b84) ->
getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
G (mkst regs' (0x20a80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x5089c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom)) ->
G (mkst regs (0x50868 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom).
Proof.
intros G HG regs rom tid x9v HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ sv F_4ea80 D_4ea80 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stw F_4ea84 D_4ea84 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea88 D_4ea88 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea8c D_4ea8c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea90 D_4ea90 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_4ea94 D_4ea94 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sv F_4ea98 D_4ea98 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv F_4ea9c D_4ea9c (argc_w av).
sn F_4eaa0 D_4eaa0.
stepiv F_4eaa4 D_4eaa4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
sv F_4eaa8 D_4eaa8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
sv F_4eaac D_4eaac (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
sn F_4eab0 D_4eab0.
sv F_4e9d4 D_4e9d4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stw F_4e9d8 D_4e9d8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 0x5089c) ltac:(ok_win HJ).
stw F_4e9dc D_4e9dc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw F_4e9e0 D_4e9e0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
sn F_4e9e4 D_4e9e4.
stepret F_4e7a4 D_4e7a4 (0x507d0 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_4e9e8 D_4e9e8.
sn F_4e9ec D_4e9ec.
ld_step F_4e9f0 D_4e9f0 (word_to_le_bytes 8 (Z_to_bv 64 0x62688)) (Z_to_bv 64 0x62688) ltac:(rd_img img_63e28_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4e9f4 D_4e9f4 (word_to_le_bytes 8 (Z_to_bv 64 0x62680)) (Z_to_bv 64 0x62680) ltac:(rd_img img_63e30_8) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_4e9f8 D_4e9f8 ltac:(pin; cond_compute).
ld_step F_4e9fc D_4e9fc (word_to_le_bytes 8 (Z_to_bv 64 0x20a80)) (Z_to_bv 64 0x20a80) ltac:(rd_img img_608a8_8) ltac:(apply bytes_le_to_Z_8).
stepjr F_4ea00 D_4ea00 (0x20a80 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hva Hlo Hhi"] Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (tid : word) (x9v : word),
wfJ sp0 Jb ->
getr regs 1 = (Z_to_bv 64 0x507ec) ->
getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
getr regs 3 = (Z_to_bv 64 0x10800) ->
getr regs 4 = (Z_to_bv 64 0x77c00) ->
getr regs 8 = (Z_to_bv 64 0x62688) ->
getr regs 9 = (Z_to_bv 64 0x62680) ->
getr regs 18 = (Z_to_bv 64 0x20b84) ->
getr regs 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
getr regs 20 = (Z_to_bv 64 0) ->
getr regs 21 = (Z_to_bv 64 0) ->
getr regs 22 = (Z_to_bv 64 0) ->
getr regs 23 = (Z_to_bv 64 0) ->
getr regs 24 = (Z_to_bv 64 0) ->
getr regs 25 = (Z_to_bv 64 0) ->
getr regs 26 = (Z_to_bv 64 0) ->
getr regs 27 = (Z_to_bv 64 0) ->
(forall regs',
getr regs' 1 = (Z_to_bv 64 0x508ac) ->
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
getr regs' 3 = (Z_to_bv 64 0x10800) ->
getr regs' 4 = (Z_to_bv 64 0x77c00) ->
getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
getr regs' 9 = (argc_w av) ->
getr regs' 10 = (argc_w av) ->
getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
getr regs' 18 = (Z_to_bv 64 0x20b84) ->
getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
G (mkst regs' (0x20b84 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x5089c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x507ec))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x62688))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary)) (Z_to_bv 64 0x66f30) [Z_to_bv 8 1])) rom)) ->
G (mkst regs (0x20a80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a0))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 x9v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 0x97e90))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x5089c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev) (Z_to_bv 64 0x97c18) (word_to_le_bytes 8 (Z_to_bv 64 0x61680))) (Z_to_bv 64 0x97c20) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97c30) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97ea0) (word_to_le_bytes 8 (Z_to_bv 64 0x97c10))) (Z_to_bv 64 0x97eb8) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x97c28) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x97c38) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97ea8) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 0x97eb0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 0x77c18) (word_to_le_bytes 8 (Z_to_bv 64 0x78400))) (Z_to_bv 64 0x77c10) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 0x77bf8) (word_to_le_bytes 8 (Z_to_bv 64 0x77c10))) (Z_to_bv 64 0x77b38) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x97e90) [Z_to_bv 8 1]) (Z_to_bv 64 0x77b60) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 0x77b58) (word_to_le_bytes 4 tid)) (Z_to_bv 64 0x77bd0) (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8))) (Z_to_bv 64 0x77bb0) (word_to_le_bytes 8 (Z_to_bv 64 0x77bb0))) (Z_to_bv 64 0x77b40) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b48) (word_to_le_bytes 8 (Z_to_bv 64 0x77b38))) (Z_to_bv 64 0x77b50) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 0x97e70) [rnd_byte 0; rnd_byte 1; rnd_byte 2; rnd_byte 3]) (Z_to_bv 64 0x97e74) [rnd_byte 4; rnd_byte 5; rnd_byte 6; rnd_byte 7]) (Z_to_bv 64 0x97e71) [Z_to_bv 8 0]) (Z_to_bv 64 0x77bf0) (word_to_le_bytes 8 ssp_canary))) rom).
Proof.
intros G HG regs rom tid x9v HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
PREP tid.
eapply HG.
{ sv F_2085c D_2085c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
stw F_20860 D_20860 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 0x507ec) ltac:(ok_win HJ).
stw F_20864 D_20864 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 0x62688) ltac:(ok_win HJ).
sv F_20868 D_20868 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
sn F_2086c D_2086c.
sn F_20870 D_20870.
lb_step F_20874 D_20874 (Z_to_bv 8 0) ltac:(rd_img img_65150_1).
sn F_20878 D_20878.
stepb_tk F_2087c D_2087c ltac:(pin; cond_compute).
sn F_20888 D_20888.
sn F_2088c D_2088c.
sn F_20890 D_20890.
stw F_20894 D_20894 (Z_to_bv 64 0x66f30) (Z_to_bv 64 1) ltac:(ok_data).
sn F_20898 D_20898.
ld_step F_2089c D_2089c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_63cf8_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_208a0 D_208a0 ltac:(pin; cond_compute).
ld_step F_208c0 D_208c0 (word_to_le_bytes 8 (Z_to_bv 64 0x507ec)) (Z_to_bv 64 0x507ec) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_208c4 D_208c4 (word_to_le_bytes 8 (Z_to_bv 64 0x62688)) (Z_to_bv 64 0x62688) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_208c8 D_208c8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stepret F_208cc D_208cc (0x507ec : word) ltac:(pin; first [reflexivity | bveq]).
sn F_4ea04 D_4ea04.
stepb_ft F_4ea08 D_4ea08 ltac:(pin; cond_compute).
ld_step F_4ea0c D_4ea0c (word_to_le_bytes 8 (Z_to_bv 64 0x5089c)) (Z_to_bv 64 0x5089c) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ea10 D_4ea10 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
ld_step F_4ea14 D_4ea14 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rd_win8) ltac:(apply bytes_le_to_Z_8).
sv F_4ea18 D_4ea18 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stepret F_4ea1c D_4ea1c (0x5089c : word) ltac:(pin; first [reflexivity | bveq]).
sv F_4eab4 D_4eab4 (argc_w av).
sv F_4eab8 D_4eab8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv F_4eabc D_4eabc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
stepjr F_4eac0 D_4eac0 (0x20b84 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq9.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UFeQ.Mq0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
rdn RSEGS mem (Z_to_bv 64 0x659d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x97e70))
/\ rdn RSEGS mem (Z_to_bv 64 0x97e70) 8%nat = Some (word_to_le_bytes 8 can).

Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
(mem' : word -> option byte) : Prop := {
swp_agree : forall x : word,
~ (su - 112 <= bv_unsigned x < su)%Z ->
~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
mem' x = mem x;
swp_grows : mem_grows mem mem';
swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

#[using="Type"] Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
sw_post mem su f bufp bufsz mem' ->
rdn RSEGS mem a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
rdn RSEGS mem' a n = Some bs.
Proof.
intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.

Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
(sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
ec_sp   : getr regs 2 = sp;
ec_tp   : getr regs 4 = tp;
ec_a0   : getr regs 10 = code;
ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
ec_tplo : (168 <= bv_unsigned tp)%Z;
ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
ec_tid  : (0 < tid < 2147483648)%Z;

ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));

ec_lock : rdn RSEGS mem (Z_to_bv 64 0x97e68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));

ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x659d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62690));
ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x659e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x62688));
ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x62688) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20af4));

ec_comp : rdn RSEGS mem (Z_to_bv 64 0x66f78) 1%nat = Some [Z_to_bv 8 0];
ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x65898) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50d50));
ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x658a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));

ec_glob : stdio_globals mem;

ec_err  : file_clean mem 0x66d38 wp2 rp2;

ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x669f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x669f8));
ec_atx  : exists armed, atx_state armed mem
}.

Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
(pending : list byte) : Prop := {
sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
sp_write : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x551dc));
sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
sp_range : (0x97e78 <= wb < wp /\ wp <= 0x99000)%Z;
sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
sp_max   : (Z.of_nat (length pending) <= rw_bytes_max)%Z;
sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
sp_ssp   : ssp_cells mem can
}.

Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
(code : word) (pending : list byte) : Prop :=
exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
exit_common regs mem sp tp code tid wp2 rp2
/\ m_halted model = None /\ m_vm_lazy model = []
/\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x66e28 wp1 rp1)
\/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
stdout_pending mem wb wp bufp bufsz rp1 can pending
/\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
