(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Um90 USPu UU2A U8LG UZSc UsN4 UlKb U39n UkD9 U8Sj UJUR Ugw2 UpBo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import UFeQ.Mq0 Um90.Mq2 USPu UU2A U8LG UZSc UsN4 UlKb U39n UkD9 U8Sj UJUR Ugw2 UpBo.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
/\ rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
/\ rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x551dc)).

#[using="Type"] Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0x50ed8 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globals mem ->
stdout_dirty_hdr mem wb wp ->
(0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
exists regs',
msteps RSEGS (mkst regs (0x54d7c : word) mem rom)
(mkst regs' (0x551dc : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = Z_to_bv 64 0x66e28
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 1 = Z_to_bv 64 0x54e2c
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
/\ getr regs' 8 = Z_to_bv 64 0x66e28
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
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

stepLD8 F_53030 D_53030 (Z_to_bv 64 wp).
stepLD8 F_53034 D_53034 (Z_to_bv 64 wb).
stepb_ft F_53038 D_53038 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

stepLD8 F_5303c D_5303c (Z_to_bv 64 0x551dc).
stepn F_53040 D_53040.
stepn F_53044 D_53044.
stepn F_53048 D_53048.
stepjr F_5304c D_5304c (Z_to_bv 64 0x551dc) ltac:(gres; reflexivity). vnorm.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

#[using="Type"] Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x66e28 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50ed8)) ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 (0x66e28 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 0x66e20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66d38)) ->
file_clean mem 0x66d38 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0x54e2c : word) mem rom)
(mkst regs' (0x50c44 : word) mem rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
(F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
eexists. split.
-
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
stepn F_5313c D_5313c. rewrite Hsp. sp_renorm.
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
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0 QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Import Um90 UZSc UsN4 UlKb U39n.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

#[using="Type"] Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

#[using="Type"] Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

#[using="Type"] Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

#[using="Type"] Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
pose proof (Z_lxor_range a b Ha Hb) as Hr.
rewrite u_Z2bv by lia.
destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

#[using="Type"] Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

#[using="Type"] Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

#[using="Type"] Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

#[using="Type"] Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

#[using="Type"] Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

#[using="Type"] Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
intros a H. unfold v_and. u_norm.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
f_equal. apply Z.mod_small. lia.
Qed.

#[using="Type"] Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b H H2. unfold v_subw. u_norm.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
reflexivity.
Qed.

Definition mem_sw1 (mem : word -> option byte) (su : Z) (ra s0 s1 s2 s3 s4 s5 s6 : word)
(can : word) (wb n : Z) (s l : word) :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (su - 8))  (word_to_le_bytes 8 ra))
(Z_to_bv 64 (su - 16)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 (su - 24)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (su - 32)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (su - 40)) (word_to_le_bytes 8 s3))
(Z_to_bv 64 (su - 48)) (word_to_le_bytes 8 s4))
(Z_to_bv 64 (su - 56)) (word_to_le_bytes 8 s5))
(Z_to_bv 64 (su - 64)) (word_to_le_bytes 8 s6))
(Z_to_bv 64 (su - 72)) (word_to_le_bytes 8 can))
(Z_to_bv 64 (su - 104)) (word_to_le_bytes 8 (Z_to_bv 64 wb)))
(Z_to_bv 64 (su - 96)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
(Z_to_bv 64 (su - 88)) (word_to_le_bytes 8 s))
(Z_to_bv 64 (su - 80)) (word_to_le_bytes 8 l).

#[using="Type"] Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x551dc : word) mem rom)
(mkst regs' (0x55264 : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 104)
/\ getr regs' 12 = Z_to_bv 64 2
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
/\ getr regs' 21 = Z_to_bv 64 0x97e70
/\ getr regs' 22 = Z_to_bv 64 (wp - wb + bv_unsigned l)
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
intros regs mem rom su f wb wp fd s l bufp bufsz can ret
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
FD WBP WPhi SMALL.
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
unfold mem_sw1. eexists. split.
- stepn F_53400 D_53400. rewrite Hsp. sp_renorm.

stepST F_53404 D_53404 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_53408 D_53408 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_5340c D_5340c (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_53410 D_53410 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_53414 D_53414 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_53418 D_53418 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_5341c D_5341c (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_53420 D_53420 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).

stepn F_53424 D_53424. rewrite Ha2.
stepn F_53428 D_53428. rewrite Ha0.

stepn F_5342c D_5342c.
stepLD8 F_53430 D_53430 (Z_to_bv 64 0x97e70).
stepLD8 F_53434 D_53434 can.
stepST F_53438 D_53438 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).

stepLD8 F_5343c D_5343c (Z_to_bv 64 wp).
stepLD8 F_53440 D_53440 (Z_to_bv 64 wb).

stepn F_53444 D_53444. rewrite (v_sub_Z wp wb) by lia.
stepn F_53448 D_53448.

stepST F_5344c D_5344c (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
stepST F_53450 D_53450 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
stepST F_53454 D_53454 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_53458 D_53458 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).

stepn F_5345c D_5345c. rewrite (v_add_Z (wp - wb) l) by lia.
stepn F_53460 D_53460. rewrite (sltu0_xor_ne wp wb) by lia.

stepb_ft F_53464 D_53464 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
stepn F_53468 D_53468.
replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
by (unfold v_addi; u_norm; f_equal; lia).
stepn F_5346c D_5346c.

stepLD F_53474 D_53474 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_53478 D_53478.
stepn F_5347c D_5347c.
stepn F_53480 D_53480.
stepn F_53484 D_53484.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

#[using="Type"] Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
sw_file mem f wp wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x551dc : word) mem rom)
(mkst regs' (0x55264 : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 88)
/\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
/\ getr regs' 21 = Z_to_bv 64 0x97e70
/\ getr regs' 22 = l
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
intros regs mem rom su f wp fd s l bufp bufsz can ret
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi [Fwp Fwb Ffd Fbuf Fbsz] [Ggot Gcan]
FD WPhi SMALL.
pose proof (u64_range l) as Hl.
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
unfold mem_sw1. eexists. split.
- stepn F_53400 D_53400. rewrite Hsp. sp_renorm.
stepST F_53404 D_53404 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_53408 D_53408 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_5340c D_5340c (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_53410 D_53410 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_53414 D_53414 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_53418 D_53418 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_5341c D_5341c (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_53420 D_53420 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
stepn F_53424 D_53424. rewrite Ha2.
stepn F_53428 D_53428. rewrite Ha0.
stepn F_5342c D_5342c.
stepLD8 F_53430 D_53430 (Z_to_bv 64 0x97e70).
stepLD8 F_53434 D_53434 can.
stepST F_53438 D_53438 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
stepLD8 F_5343c D_5343c (Z_to_bv 64 wp).
stepLD8 F_53440 D_53440 (Z_to_bv 64 wp).
stepn F_53444 D_53444. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
stepn F_53448 D_53448.
stepST F_5344c D_5344c (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
stepST F_53450 D_53450 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
stepST F_53454 D_53454 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_53458 D_53458 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
stepn F_5345c D_5345c.
stepn F_53460 D_53460. rewrite sltu0_xor_eq.

stepb_tk F_53464 D_53464 ltac:(apply c_eq_refl).
stepn F_53470 D_53470.
replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
by (unfold v_addi; u_norm; f_equal; lia).
stepLD F_53474 D_53474 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_53478 D_53478.
stepn F_5347c D_5347c.
stepn F_53480 D_53480.
stepn F_53484 D_53484.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeDN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqHD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqHD.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UVbU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVbU. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaUj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaUj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U6yP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U6yP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujor.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujor. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UkD9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UkD9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8Sj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8Sj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJUR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJUR.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ALL.
Context {fF : FPF} {fC : FPC}.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Variable rom : word -> option byte.
Hypothesis HOK : mcH mem0 dst src n bs.

#[local] Notation MK := (memk mem0 dst bs).
Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

Ltac mlbu F D jj :=
chain_step; [reflexivity
| eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vnorm.

Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
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

Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.

Ltac conda := rwH; unfold at_; cond.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[using="HOK Hn0"] Lemma al_finish : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f558 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
set (m := ((n - k) mod 16)%Z).
pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f594 : word) (MK (n - m)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P). exists r.
subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f5b4 : word) (MK (n - m + Z.land m 8)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7f8 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
{ destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P).
exists r. split; [exact R | eapply keeps_trans; eassumption].
Qed.

#[using="HOK Hn0"] Lemma mis_run : forall regs (ret : word) k q,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
(0 <= k <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f488 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
-
destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f490 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6ac D_5d6ac.
stepb_ft F_5d6b0 D_5d6b0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
set (m := (n - k)%Z) in *.
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f7f8 : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
/\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
* destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
* cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3).
exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f4ac : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6ac D_5d6ac.
stepb_tk F_5d6b0 D_5d6b0 ltac:(cond).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
assert (CASE : exists regs' m,
msteps RSEGS (mkst r1 (0x5f4ac : word) (MK k) rom)
(mkst regs' (0x5f7f8 : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
/\ (0 <= m < 32)%Z
/\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
/\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
{ destruct Hq as [-> | [-> | ->]].
- apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
- apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2).
destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3).
exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
Qed.

#[using="HOK Hn0 Hnwd"] Lemma j_run : forall regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
(0 <= k <= n)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f480 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
intros regs ret k Hret H1 H11 H13 H12 Hk.
pose proof (u64_range dst).
set (q := ((bv_unsigned dst + k) mod 4)%Z).
pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
destruct (Z.eq_dec q 0) as [Hq0|Hq0].
-
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f558 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6a4 D_5d6a4.
stepb_tk F_5d6a8 D_5d6a8 ltac:(conda).
apply mst_refl.
* cbv beta. post.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
- eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f488 : word) (MK k) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
/\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
+ eexists. split.
* stepn F_5d6a4 D_5d6a4.
stepb_ft F_5d6a8 D_5d6a8 ltac:(conda).
apply mst_refl.
* cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
change (bv_wrap 64 3) with 3%Z. reflexivity.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

#[using="HOK Hn0 Hnws Hnwd"] Lemma hl_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
(Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
exists regs',
msteps RSEGS (mkst regs (0x5f450 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ keeps regs regs'.
Proof.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
-
pose proof (u64_range src).
destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f480 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_5d674 D_5d674 k.
stepn F_5d678 D_5d678.
stepn F_5d67c D_5d67c.
stepn F_5d680 D_5d680.
msb F_5d684 D_5d684 k ltac:(apply sb_val_plain).
stepn F_5d688 D_5d688.
stepn F_5d68c D_5d68c.
stepb_tk F_5d690 D_5d690 ltac:(conda).
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f480 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
* eexists. split.
-- mlbu F_5d674 D_5d674 k.
stepn F_5d678 D_5d678.
stepn F_5d67c D_5d67c.
stepn F_5d680 D_5d680.
msb F_5d684 D_5d684 k ltac:(apply sb_val_plain).
stepn F_5d688 D_5d688.
stepn F_5d68c D_5d68c.
stepb_ft F_5d690 D_5d690 ltac:(conda).
stepn F_5d694 D_5d694.
stepb_ft F_5d698 D_5d698 ltac:(cond).
stepn F_5d69c D_5d69c.
apply mst_refl.
-- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
pose proof (u64_range src).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f450 : word) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
/\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
+ eexists. split.
* mlbu F_5d674 D_5d674 k.
stepn F_5d678 D_5d678.
stepn F_5d67c D_5d67c.
stepn F_5d680 D_5d680.
msb F_5d684 D_5d684 k ltac:(apply sb_val_plain).
stepn F_5d688 D_5d688.
stepn F_5d68c D_5d68c.
stepb_ft F_5d690 D_5d690 ltac:(conda).
stepn F_5d694 D_5d694.
stepb_tk F_5d698 D_5d698 ltac:(cond).
apply mst_refl.
* cbv beta. post. unfold v_addi. unorm. f_equal. lia.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

#[using="HOK Hn0 Hnws Hnwd"] Theorem ref_memcpy : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps RSEGS (mkst regs (0x5f438 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ keeps regs regs'.
Proof.
intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src). pose proof (u64_range dst).
rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
-
destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f558 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_5d65c D_5d65c.
stepb_tk F_5d660 D_5d660 ltac:(conda).
stepn F_5d770 D_5d770.
stepn F_5d774 D_5d774.
stepb_ft F_5d778 D_5d778 ltac:(cond).
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f488 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
* eexists. split.
-- stepn F_5d65c D_5d65c.
stepb_tk F_5d660 D_5d660 ltac:(conda).
stepn F_5d770 D_5d770.
stepn F_5d774 D_5d774.
stepb_tk F_5d778 D_5d778 ltac:(cond).
apply mst_refl.
-- cbv beta. post; try (rewrite at_0; reflexivity).
unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R15 & K1).
pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
-
destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
+ eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f480 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
* eexists. split.
-- stepn F_5d65c D_5d65c.
stepb_ft F_5d660 D_5d660 ltac:(conda).
stepb_tk F_5d664 D_5d664 ltac:(cond).
stepn F_5d6a0 D_5d6a0.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2).
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
+ set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
eapply (runs_trans RSEGS _ (fun r => mkst r (0x5f450 : word) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
/\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
* eexists. split.
-- stepn F_5d65c D_5d65c.
stepb_ft F_5d660 D_5d660 ltac:(conda).
stepb_ft F_5d664 D_5d664 ltac:(cond).
stepn F_5d668 D_5d668.
stepn F_5d66c D_5d66c.
stepn F_5d670 D_5d670.
apply mst_refl.
-- cbv beta. post. rewrite at_0. reflexivity.
* cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2).
{ subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

