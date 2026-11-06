(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QS67 QY6W QQ7a Q9dN QpBN QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import QS67 QY6W QQ7a Q9dN QpBN QCKW.Mq3.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xcc71c)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xd2fc0)))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 wp0 rp0 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0xcc71c ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xea840 wp0 rp0 ->
file_clean mem 0xea750 wp1 rp1 ->
file_clean mem 0xea660 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0xd2fb0 : word) mem rom)
(mkst regs' (0xcc488 : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code wp1 rp1 wp2 rp2 wp0 rp0 Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F0l & F0wp & F0wb & F0rp & F0re)
(F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
unfold mem_w3a. eexists. split.
-
stepn F_d2fd4 D_d2fd4. rewrite Hsp. sp_renorm.
stepST F_d2fd8 D_d2fd8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xcc71c) ltac:(sok_stack SOK).
stepST F_d2fdc D_d2fdc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).

stepn F_d2fe0 D_d2fe0.
stepn F_d35dc D_d35dc. sp_renorm.
stepST F_d35e0 D_d35e0 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xd2fc0) ltac:(sok_stack SOK).
stepST F_d35e4 D_d35e4 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
stepn F_d35e8 D_d35e8.
stepn F_d35ec D_d35ec.
stepn F_d35f0 D_d35f0.

stepn F_d35f4 D_d35f4.
stepn F_dc460 D_dc460.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_dc464 | reflexivity | exact D_dc464 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_dc468 D_dc468 ltac:(cond_compute).
stepret F_dc658 D_dc658 (0xd35d4 : word) ltac:(bveq).

stepn F_d35f8 D_d35f8.
stepLD8 F_d35fc D_d35fc (Z_to_bv 64 0xd2fc0).
stepLD8 F_d3600 D_d3600 code.
stepn F_d3604 D_d3604. sp_renorm.
stepret F_d3608 D_d3608 (0xd2fc0 : word) ltac:(bveq).

stepLD8 F_d2fe4 D_d2fe4 (Z_to_bv 64 0).
stepb_ft F_d2fe8 D_d2fe8 ltac:(cond_compute).

stepn F_d2fec D_d2fec.
stepLD8 F_d2ff0 D_d2ff0 (Z_to_bv 64 0xea840).
stepb_ft F_d2ff4 D_d2ff4 ltac:(cond_compute).

stepLD F_d2ff8 D_d2ff8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d2ffc D_d2ffc ltac:(cond_compute).

stepLD8 F_d3008 D_d3008 wp0.
stepLD8 F_d300c D_d300c wp0.
stepb_tk F_d3010 D_d3010 ltac:(apply c_eq_refl).

stepLD8 F_d3028 D_d3028 rp0.
stepLD8 F_d302c D_d302c rp0.
stepb_tk F_d3030 D_d3030 ltac:(apply c_eq_refl).

stepn F_d3048 D_d3048.
stepLD8 F_d304c D_d304c (Z_to_bv 64 0xea750).
stepb_ft F_d3050 D_d3050 ltac:(cond_compute).

stepLD F_d3054 D_d3054 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d3058 D_d3058 ltac:(cond_compute).

stepLD8 F_d3064 D_d3064 wp1.
stepLD8 F_d3068 D_d3068 wp1.
stepb_tk F_d306c D_d306c ltac:(apply c_eq_refl).

stepLD8 F_d3084 D_d3084 rp1.
stepLD8 F_d3088 D_d3088 rp1.
stepb_tk F_d308c D_d308c ltac:(apply c_eq_refl).

stepn F_d30a4 D_d30a4.
stepLD8 F_d30a8 D_d30a8 (Z_to_bv 64 0xea660).
stepb_ft F_d30ac D_d30ac ltac:(cond_compute).
stepLD F_d30b0 D_d30b0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d30b4 D_d30b4 ltac:(cond_compute).
stepLD8 F_d30c0 D_d30c0 wp2.
stepLD8 F_d30c4 D_d30c4 wp2.
stepb_tk F_d30c8 D_d30c8 ltac:(apply c_eq_refl).
stepLD8 F_d30e0 D_d30e0 rp2.
stepLD8 F_d30e4 D_d30e4 rp2.
stepb_tk F_d30e8 D_d30e8 ltac:(apply c_eq_refl).

stepLD8 F_d3168 D_d3168 (Z_to_bv 64 0xcc71c).
stepLD8 F_d316c D_d316c code.
stepn F_d3170 D_d3170. sp_renorm.
stepret F_d3174 D_d3174 (0xcc71c : word) ltac:(bveq).

stepn F_cc740 D_cc740.
stepn F_cc744 D_cc744.
stepn F_cc4a4 D_cc4a4.
stepn F_cc4a8 D_cc4a8.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0 QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Import QCKW.Mq2 QQ7a.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
pose proof (Z_lxor_range a b Ha Hb) as Hr.
rewrite u_Z2bv by lia.
destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
intros a H. unfold v_and. u_norm.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
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

Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd29d0 : word) mem rom)
(mkst regs' (0xd2a58 : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 104)
/\ getr regs' 12 = Z_to_bv 64 2
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
/\ getr regs' 21 = Z_to_bv 64 0x642ea0
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
- stepn F_d29f4 D_d29f4. rewrite Hsp. sp_renorm.

stepST F_d29f8 D_d29f8 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_d29fc D_d29fc (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_d2a00 D_d2a00 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_d2a04 D_d2a04 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_d2a08 D_d2a08 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_d2a0c D_d2a0c (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_d2a10 D_d2a10 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_d2a14 D_d2a14 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).

stepn F_d2a18 D_d2a18. rewrite Ha2.
stepn F_d2a1c D_d2a1c. rewrite Ha0.

stepn F_d2a20 D_d2a20.
stepLD8 F_d2a24 D_d2a24 (Z_to_bv 64 0x642ea0).
stepLD8 F_d2a28 D_d2a28 can.
stepST F_d2a2c D_d2a2c (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).

stepLD8 F_d2a30 D_d2a30 (Z_to_bv 64 wp).
stepLD8 F_d2a34 D_d2a34 (Z_to_bv 64 wb).

stepn F_d2a38 D_d2a38. rewrite (v_sub_Z wp wb) by lia.
stepn F_d2a3c D_d2a3c.

stepST F_d2a40 D_d2a40 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
stepST F_d2a44 D_d2a44 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
stepST F_d2a48 D_d2a48 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_d2a4c D_d2a4c (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).

stepn F_d2a50 D_d2a50. rewrite (v_add_Z (wp - wb) l) by lia.
stepn F_d2a54 D_d2a54. rewrite (sltu0_xor_ne wp wb) by lia.

stepb_ft F_d2a58 D_d2a58 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
stepn F_d2a5c D_d2a5c.
replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
by (unfold v_addi; u_norm; f_equal; lia).
stepn F_d2a60 D_d2a60.

stepLD F_d2a68 D_d2a68 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_d2a6c D_d2a6c.
stepn F_d2a70 D_d2a70.
stepn F_d2a74 D_d2a74.
stepn F_d2a78 D_d2a78.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
sw_file mem f wp wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd29d0 : word) mem rom)
(mkst regs' (0xd2a58 : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 88)
/\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
/\ getr regs' 21 = Z_to_bv 64 0x642ea0
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
- stepn F_d29f4 D_d29f4. rewrite Hsp. sp_renorm.
stepST F_d29f8 D_d29f8 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_d29fc D_d29fc (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_d2a00 D_d2a00 (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_d2a04 D_d2a04 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_d2a08 D_d2a08 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_d2a0c D_d2a0c (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_d2a10 D_d2a10 (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_d2a14 D_d2a14 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
stepn F_d2a18 D_d2a18. rewrite Ha2.
stepn F_d2a1c D_d2a1c. rewrite Ha0.
stepn F_d2a20 D_d2a20.
stepLD8 F_d2a24 D_d2a24 (Z_to_bv 64 0x642ea0).
stepLD8 F_d2a28 D_d2a28 can.
stepST F_d2a2c D_d2a2c (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
stepLD8 F_d2a30 D_d2a30 (Z_to_bv 64 wp).
stepLD8 F_d2a34 D_d2a34 (Z_to_bv 64 wp).
stepn F_d2a38 D_d2a38. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
stepn F_d2a3c D_d2a3c.
stepST F_d2a40 D_d2a40 (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
stepST F_d2a44 D_d2a44 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
stepST F_d2a48 D_d2a48 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_d2a4c D_d2a4c (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
stepn F_d2a50 D_d2a50.
stepn F_d2a54 D_d2a54. rewrite sltu0_xor_eq.

stepb_tk F_d2a58 D_d2a58 ltac:(apply c_eq_refl).
stepn F_d2a64 D_d2a64.
replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
by (unfold v_addi; u_norm; f_equal; lia).
stepLD F_d2a68 D_d2a68 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_d2a6c D_d2a6c.
stepn F_d2a70 D_d2a70.
stepn F_d2a74 D_d2a74.
stepn F_d2a78 D_d2a78.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Q1jK QxOv Qwsr QGoa Q9j0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import Q1jK QxOv Qwsr QGoa Q9j0 QCKW.Mq8.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
wbytes (wbytes (wbytes (wbytes mem
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xcede0)))
(Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
(Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xd5684)))
(Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 wp0 rp0 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0xcede0 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xecf20 wp0 rp0 ->
file_clean mem 0xece30 wp1 rp1 ->
file_clean mem 0xecd40 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0xd5674 : word) mem rom)
(mkst regs' (0xceb4c : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code wp1 rp1 wp2 rp2 wp0 rp0 Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F0l & F0wp & F0wb & F0rp & F0re)
(F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
unfold mem_w3a. eexists. split.
-
stepn F_d56c0 D_d56c0. rewrite Hsp. sp_renorm.
stepST F_d56c4 D_d56c4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xcede0) ltac:(sok_stack SOK).
stepST F_d56c8 D_d56c8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).

stepn F_d56cc D_d56cc.
stepn F_d5cc8 D_d5cc8. sp_renorm.
stepST F_d5ccc D_d5ccc (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0xd5684) ltac:(sok_stack SOK).
stepST F_d5cd0 D_d5cd0 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
stepn F_d5cd4 D_d5cd4.
stepn F_d5cd8 D_d5cd8.
stepn F_d5cdc D_d5cdc.

stepn F_d5ce0 D_d5ce0.
stepn F_deb4c D_deb4c.
chain_step; [reflexivity
| eapply step_lb with (b := Z_to_bv 8 0);
[exact F_deb50 | reflexivity | exact D_deb50 | gres; imm_norm; addr_norm; rdn_solve]
| step_simpl]; vnorm.
stepb_tk F_deb54 D_deb54 ltac:(cond_compute).
stepret F_ded44 D_ded44 (0xd5c98 : word) ltac:(bveq).

stepn F_d5ce4 D_d5ce4.
stepLD8 F_d5ce8 D_d5ce8 (Z_to_bv 64 0xd5684).
stepLD8 F_d5cec D_d5cec code.
stepn F_d5cf0 D_d5cf0. sp_renorm.
stepret F_d5cf4 D_d5cf4 (0xd5684 : word) ltac:(bveq).

stepLD8 F_d56d0 D_d56d0 (Z_to_bv 64 0).
stepb_ft F_d56d4 D_d56d4 ltac:(cond_compute).

stepn F_d56d8 D_d56d8.
stepLD8 F_d56dc D_d56dc (Z_to_bv 64 0xecf20).
stepb_ft F_d56e0 D_d56e0 ltac:(cond_compute).

stepLD F_d56e4 D_d56e4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d56e8 D_d56e8 ltac:(cond_compute).

stepLD8 F_d56f4 D_d56f4 wp0.
stepLD8 F_d56f8 D_d56f8 wp0.
stepb_tk F_d56fc D_d56fc ltac:(apply c_eq_refl).

stepLD8 F_d5714 D_d5714 rp0.
stepLD8 F_d5718 D_d5718 rp0.
stepb_tk F_d571c D_d571c ltac:(apply c_eq_refl).

stepn F_d5734 D_d5734.
stepLD8 F_d5738 D_d5738 (Z_to_bv 64 0xece30).
stepb_ft F_d573c D_d573c ltac:(cond_compute).

stepLD F_d5740 D_d5740 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d5744 D_d5744 ltac:(cond_compute).

stepLD8 F_d5750 D_d5750 wp1.
stepLD8 F_d5754 D_d5754 wp1.
stepb_tk F_d5758 D_d5758 ltac:(apply c_eq_refl).

stepLD8 F_d5770 D_d5770 rp1.
stepLD8 F_d5774 D_d5774 rp1.
stepb_tk F_d5778 D_d5778 ltac:(apply c_eq_refl).

stepn F_d5790 D_d5790.
stepLD8 F_d5794 D_d5794 (Z_to_bv 64 0xecd40).
stepb_ft F_d5798 D_d5798 ltac:(cond_compute).
stepLD F_d579c D_d579c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
stepb_tk F_d57a0 D_d57a0 ltac:(cond_compute).
stepLD8 F_d57ac D_d57ac wp2.
stepLD8 F_d57b0 D_d57b0 wp2.
stepb_tk F_d57b4 D_d57b4 ltac:(apply c_eq_refl).
stepLD8 F_d57cc D_d57cc rp2.
stepLD8 F_d57d0 D_d57d0 rp2.
stepb_tk F_d57d4 D_d57d4 ltac:(apply c_eq_refl).

stepLD8 F_d5854 D_d5854 (Z_to_bv 64 0xcede0).
stepLD8 F_d5858 D_d5858 code.
stepn F_d585c D_d585c. sp_renorm.
stepret F_d5860 D_d5860 (0xcede0 : word) ltac:(bveq).

stepn F_cee2c D_cee2c.
stepn F_cee30 D_cee30.
stepn F_ceb90 D_ceb90.
stepn F_ceb94 D_ceb94.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Import QCKW.Mq7 Qwsr.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Lemma v_sub_Z : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H H2. unfold v_sub. u_norm. reflexivity. Qed.

Lemma v_add_Z : forall a (l : word), (0 <= a < 2^64)%Z ->
v_add (Z_to_bv 64 a) l = Z_to_bv 64 (a + bv_unsigned l).
Proof. intros a l H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_wZ : forall (b : word) c, (0 <= c < 2^64)%Z ->
v_add b (Z_to_bv 64 c) = Z_to_bv 64 (bv_unsigned b + c).
Proof. intros b c H. unfold v_add. u_norm. reflexivity. Qed.

Lemma v_add_ZZ' : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z ->
v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. u_norm. reflexivity. Qed.

Lemma sltu0_xor_ne : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> a <> b ->
v_sltu (Z_to_bv 64 0) (v_xor (Z_to_bv 64 a) (Z_to_bv 64 b)) = Z_to_bv 64 1.
Proof.
intros a b Ha Hb Hne. unfold v_sltu, c_ltu, bv_ltu, v_xor.
rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 0) by lia.
pose proof (Z_lxor_range a b Ha Hb) as Hr.
rewrite u_Z2bv by lia.
destruct (Z.ltb_spec 0 (Z.lxor a b)) as [Hlt|Hge]; [reflexivity|].
exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.

Lemma sltu0_xor_eq : forall a : word, v_sltu (Z_to_bv 64 0) (v_xor a a) = Z_to_bv 64 0.
Proof.
intros a. unfold v_sltu, c_ltu, bv_ltu, v_xor. rewrite Z.lxor_nilpotent.
rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Lemma sltu_ge : forall a b, (0 <= b <= a)%Z -> (a < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [lia|reflexivity].
Qed.

Lemma sltu_lt : forall a b, (0 <= a < b)%Z -> (b < 2^64)%Z ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof.
intros a b H H2. unfold v_sltu, c_ltu, bv_ltu. u_norm.
destruct (Z.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma c_lts_pos_0 : forall a, (0 <= a < 2^63)%Z ->
c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof.
intros a H. unfold c_lts, bv_lts. rewrite !bv_signed_small by (u_norm; lia). u_norm.
destruct (Z.ltb_spec a 0); [lia|reflexivity].
Qed.

Lemma v_and_0_l : forall (x : word), v_and (Z_to_bv 64 0) x = Z_to_bv 64 0.
Proof. intros x. unfold v_and. rewrite (u_Z2bv 0) by lia. rewrite Z.land_0_l. reflexivity. Qed.

Lemma v_and_m1_l : forall a, (0 <= a < 2^64)%Z ->
v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 a) = Z_to_bv 64 a.
Proof.
intros a H. unfold v_and. u_norm.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
f_equal. apply Z.mod_small. lia.
Qed.

Lemma v_subw_small_lit : forall a b, (0 <= b <= a)%Z -> (a < 2^31)%Z ->
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

Lemma sw_enter : forall regs mem rom (su f wb wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wb < wp)%Z -> (wp < 2^64)%Z -> (wp - wb + bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd5094 : word) mem rom)
(mkst regs' (0xd511c : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 104)
/\ getr regs' 12 = Z_to_bv 64 2
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 2 /\ getr regs' 19 = Z_to_bv 64 (su - 104)
/\ getr regs' 21 = Z_to_bv 64 0x645560
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
- stepn F_d50e0 D_d50e0. rewrite Hsp. sp_renorm.

stepST F_d50e4 D_d50e4 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_d50e8 D_d50e8 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_d50ec D_d50ec (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_d50f0 D_d50f0 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_d50f4 D_d50f4 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_d50f8 D_d50f8 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_d50fc D_d50fc (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_d5100 D_d5100 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).

stepn F_d5104 D_d5104. rewrite Ha2.
stepn F_d5108 D_d5108. rewrite Ha0.

stepn F_d510c D_d510c.
stepLD8 F_d5110 D_d5110 (Z_to_bv 64 0x645560).
stepLD8 F_d5114 D_d5114 can.
stepST F_d5118 D_d5118 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).

stepLD8 F_d511c D_d511c (Z_to_bv 64 wp).
stepLD8 F_d5120 D_d5120 (Z_to_bv 64 wb).

stepn F_d5124 D_d5124. rewrite (v_sub_Z wp wb) by lia.
stepn F_d5128 D_d5128.

stepST F_d512c D_d512c (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) ltac:(sok_frame SOK).
stepST F_d5130 D_d5130 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 (wp - wb)) ltac:(sok_frame SOK).
stepST F_d5134 D_d5134 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_d5138 D_d5138 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).

stepn F_d513c D_d513c. rewrite (v_add_Z (wp - wb) l) by lia.
stepn F_d5140 D_d5140. rewrite (sltu0_xor_ne wp wb) by lia.

stepb_ft F_d5144 D_d5144 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
stepn F_d5148 D_d5148.
replace (v_addi (Z_to_bv 64 (su - 112)) 8) with (Z_to_bv 64 (su - 104))
by (unfold v_addi; u_norm; f_equal; lia).
stepn F_d514c D_d514c.

stepLD F_d5154 D_d5154 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_d5158 D_d5158.
stepn F_d515c D_d515c.
stepn F_d5160 D_d5160.
stepn F_d5164 D_d5164.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

Lemma sw_enter_eq : forall regs mem rom (su f wp fd : Z) (s l bufp bufsz can ret : word),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
sw_file mem f wp wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
(0 <= wp < 2^64)%Z -> (bv_unsigned l < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd5094 : word) mem rom)
(mkst regs' (0xd511c : word)
(mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wp 0 s l) rom)
/\ getr regs' 17 = Z_to_bv 64 66
/\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (su - 88)
/\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 2 = Z_to_bv 64 (su - 112)
/\ getr regs' 8 = l /\ getr regs' 9 = Z_to_bv 64 f
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 (su - 88)
/\ getr regs' 21 = Z_to_bv 64 0x645560
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
- stepn F_d50e0 D_d50e0. rewrite Hsp. sp_renorm.
stepST F_d50e4 D_d50e4 (Z_to_bv 64 (su - 8)) ret ltac:(sok_frame SOK).
stepST F_d50e8 D_d50e8 (Z_to_bv 64 (su - 16)) (getr regs 8) ltac:(sok_frame SOK).
stepST F_d50ec D_d50ec (Z_to_bv 64 (su - 24)) (getr regs 9) ltac:(sok_frame SOK).
stepST F_d50f0 D_d50f0 (Z_to_bv 64 (su - 32)) (getr regs 18) ltac:(sok_frame SOK).
stepST F_d50f4 D_d50f4 (Z_to_bv 64 (su - 40)) (getr regs 19) ltac:(sok_frame SOK).
stepST F_d50f8 D_d50f8 (Z_to_bv 64 (su - 48)) (getr regs 20) ltac:(sok_frame SOK).
stepST F_d50fc D_d50fc (Z_to_bv 64 (su - 56)) (getr regs 21) ltac:(sok_frame SOK).
stepST F_d5100 D_d5100 (Z_to_bv 64 (su - 64)) (getr regs 22) ltac:(sok_frame SOK).
stepn F_d5104 D_d5104. rewrite Ha2.
stepn F_d5108 D_d5108. rewrite Ha0.
stepn F_d510c D_d510c.
stepLD8 F_d5110 D_d5110 (Z_to_bv 64 0x645560).
stepLD8 F_d5114 D_d5114 can.
stepST F_d5118 D_d5118 (Z_to_bv 64 (su - 72)) can ltac:(sok_frame SOK).
stepLD8 F_d511c D_d511c (Z_to_bv 64 wp).
stepLD8 F_d5120 D_d5120 (Z_to_bv 64 wp).
stepn F_d5124 D_d5124. rewrite (v_sub_Z wp wp) by lia. rewrite Z.sub_diag.
stepn F_d5128 D_d5128.
stepST F_d512c D_d512c (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wp) ltac:(sok_frame SOK).
stepST F_d5130 D_d5130 (Z_to_bv 64 (su - 96)) (Z_to_bv 64 0) ltac:(sok_frame SOK).
stepST F_d5134 D_d5134 (Z_to_bv 64 (su - 88)) s ltac:(sok_frame SOK).
stepST F_d5138 D_d5138 (Z_to_bv 64 (su - 80)) l ltac:(sok_frame SOK).
stepn F_d513c D_d513c.
stepn F_d5140 D_d5140. rewrite sltu0_xor_eq.

stepb_tk F_d5144 D_d5144 ltac:(apply c_eq_refl).
stepn F_d5150 D_d5150.
replace (v_addi (Z_to_bv 64 (su - 112)) 24) with (Z_to_bv 64 (su - 88))
by (unfold v_addi; u_norm; f_equal; lia).
stepLD F_d5154 D_d5154 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.
stepn F_d5158 D_d5158.
stepn F_d515c D_d515c.
stepn F_d5160 D_d5160.
stepn F_d5164 D_d5164.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq3.
From Stdlib Require NArith FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi Qfub QMz4 Q9ox QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import QZsi.
Import QCKW.Mq5 Qfub.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.

Import ListNotations.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section DrvSysA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma read_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(p : list byte) (off : word) (data junk : list byte) (dst cnt lo : Z),
CK J c ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo ->
rw_cells asegs m dst [CB (Z.to_nat cnt) junk] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
let bs := file_read data off (Z_to_bv 64 cnt) in
munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' dst [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 3) (FdFile p (bv_add off (len_word bs))) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (len_word bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> Hfd Hfs Hcnt Hdst Hlo DST ST LOS SPH MI RA HK. cbv zeta in HK.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m) as MU.
apply (aj_evt J). unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 dst cnt).
{ pose proof (proj2 DST) as W. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_read_file_w F fc asegs J (SYS F fc) R pc mm ro c 3 dst cnt p off data K HCK);
[reflexivity | reflexivity | lia | reflexivity | reflexivity | lia | unfold TASK_SIZE; lia | exact WR | exact Hfd | exact Hfs |] end.
intros c' HN FDS FSE.
rewrite <- write_to_mem_wbytes.
set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
pose proof (length_file_read_le data off cnt ltac:(lia)) as LENB. fold bs in LENB.
pose proof (wr_at_store_ok asegs m0 dst _ 0 (length bs) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK2.
rewrite Z.add_0_r in SOK2.
pose proof (mem_inv_store asegs m0 (wa dst) bs MI SOK2) as MI2.
assert (MU2 : munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [exact MU| lia| lia| cbn [inside]; right; left; lia]. }
assert (MU1 : munch [(dst, dst + cnt)] m0 (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [apply munch_refl| lia| lia| cbn [inside]; left; lia]. }
pose proof (wmono_write asegs m m0 (wa dst) bs WM) as WM2.
pose proof (wmono_write asegs m0 m0 (wa dst) bs (wmono_refl asegs m0)) as WM1.
pose proof (rw_cells_fill0 m0 dst (Z.to_nat cnt) junk bs DST LENB) as DST2.
pose proof (stk_write asegs m0 lo _ dst bs ST ltac:(lia) ltac:(lia)) as ST2.
assert (FR2 : rw_cells asegs (write_to_mem m0 (wa dst) bs) (bv_unsigned sp + -16) [CB 8 (firstn 8 junk0); C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia| exact I]. }
change (write_to_mem m0 (Z_to_bv 64 dst) bs) with (write_to_mem m0 (wa dst) bs).
clear SOK2 MU MU1 WM WM1 DST ST FR MI WR.
set (m2 := write_to_mem m0 (wa dst) bs) in *. clearbody m2.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 912920) 4) with (Z_to_bv 64 912924 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step.
unfold len_word. step. if_truex.
step.
apply evt_done. release_frame FR2 ST2 (bv_unsigned sp).
eapply HK; [exact MU2| exact WM2| exact MI2| exact ST2| exact DST2| exact HN| exact FDS| exact FSE].
Qed.

Lemma close_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(e : FdEntry) (lo : Z),
CK J c ->
a0 = Z_to_bv 64 3 ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some e ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
CNEXT J c c' -> m_fds (cfg_model c') = fd_remove (m_fds (cfg_model c)) (Z_to_bv 64 3) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 CLOSE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> Hfd ST LOS SPH MI RA HK.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply (aj_evt J). unfold CLOSE_SYM.
carve_frame 16%nat ST.
do 3 step. step.
do 8 step. step.
do 7 step.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_close F fc asegs J (SYS F fc) R pc mm ro c 3 e K HCK); [reflexivity | reflexivity | lia | exact Hfd |] end.
intros c' HN FDS FSE.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 912920) 4) with (Z_to_bv 64 912924 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step. step.
do 2 step. step. if_truex. step.
do 3 step. step.
apply evt_done. release_frame FR ST (bv_unsigned sp).
eapply HK; [exact MU| exact WM| exact MI| exact ST| exact HN| exact FDS| exact FSE].
Qed.

Lemma read_dir_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(dst cnt lo : Z) (errv : word),
CK J c ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some FdDir ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo -> 0x647000 <= lo ->
(exists junk, rw_cells asegs m dst [CB (Z.to_nat cnt) junk]) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] -> 0xea000 <= bv_unsigned tp - 164 -> bv_unsigned tp <= 0x647000 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m m' -> wmono asegs m m' ->
mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (bv_unsigned tp - 164) [C4 (Z_to_bv 64 EISDIR)] ->
CNEXT J c c' -> same_io c c' ->
AJ J K c' (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HCK -> -> -> Hfd Hcnt Hdst Hlo Hlo2 (junk & DST) ST LOS SPH ERR TPL TPH MI RA HK.
word_range sp SPR. word_range tp TPR.
replace (bv_unsigned tp - 164) with (bv_unsigned tp + -164) in ERR by lia.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m) as MU.
apply (aj_evt J). unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_done.
pose proof (wr_at_store_ok asegs m0 dst _ 0 (Z.to_nat cnt) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK.
rewrite Z.add_0_r in SOK.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 dst cnt).
{ pose proof (proj2 DST) as W. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_read_dir F fc asegs J (SYS F fc) R pc mm ro c 3 dst cnt K HCK);
[reflexivity | reflexivity | lia | reflexivity | reflexivity | lia | unfold TASK_SIZE; lia | exact WR | exact Hfd |] end.
intros c' HN SIO.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 912920) 4) with (Z_to_bv 64 912924 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step.
unfold errno_ret, EISDIR. step.
replace (bv_ltu (Z_to_bv 64 (- (21))) (Z_to_bv 64 (-4095))) with false by (vm_compute; reflexivity). cbv iota.
step. step. step.
step.
step. step. step. step.
step.
replace (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- (21)))))) with (Z_to_bv 64 21 : word) in * by (apply bv_eq; vm_compute; reflexivity).
do 4 step. step.
apply evt_done. release_frame FR ST (bv_unsigned sp).
replace (bv_unsigned tp + -164) with (bv_unsigned tp - 164) in ERR by lia.
eapply HK; [exact MU| exact WM| exact MI| exact ST| unfold EISDIR; exact ERR| exact HN| exact SIO].
Qed.
End DrvSysA.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.

Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section DrvSysA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Lemma read_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(p : list byte) (off : word) (data junk : list byte) (dst cnt lo : Z),
CK J c ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo ->
rw_cells asegs m dst [CB (Z.to_nat cnt) junk] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
let bs := file_read data off (Z_to_bv 64 cnt) in
munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' dst [CB (length bs) bs; CB (Z.to_nat cnt - length bs) (skipn (length bs) junk)] ->
CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 3) (FdFile p (bv_add off (len_word bs))) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (len_word bs) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> Hfd Hfs Hcnt Hdst Hlo DST ST LOS SPH MI RA HK. cbv zeta in HK.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m) as MU.
apply (aj_evt J). unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 dst cnt).
{ pose proof (proj2 DST) as W. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_read_file_w F fc asegs J (SYS F fc) R pc mm ro c 3 dst cnt p off data K HCK);
[reflexivity | reflexivity | lia | reflexivity | reflexivity | lia | unfold TASK_SIZE; lia | exact WR | exact Hfd | exact Hfs |] end.
intros c' HN FDS FSE.
rewrite <- write_to_mem_wbytes.
set (bs := file_read data off (Z_to_bv 64 cnt)) in *.
pose proof (length_file_read_le data off cnt ltac:(lia)) as LENB. fold bs in LENB.
pose proof (wr_at_store_ok asegs m0 dst _ 0 (length bs) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK2.
rewrite Z.add_0_r in SOK2.
pose proof (mem_inv_store asegs m0 (wa dst) bs MI SOK2) as MI2.
assert (MU2 : munch [(bv_unsigned sp - 16, bv_unsigned sp); (dst, dst + cnt)] m (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [exact MU| lia| lia| cbn [inside]; right; left; lia]. }
assert (MU1 : munch [(dst, dst + cnt)] m0 (write_to_mem m0 (wa dst) bs)).
{ apply munch_write; [apply munch_refl| lia| lia| cbn [inside]; left; lia]. }
pose proof (wmono_write asegs m m0 (wa dst) bs WM) as WM2.
pose proof (wmono_write asegs m0 m0 (wa dst) bs (wmono_refl asegs m0)) as WM1.
pose proof (rw_cells_fill0 m0 dst (Z.to_nat cnt) junk bs DST LENB) as DST2.
pose proof (stk_write asegs m0 lo _ dst bs ST ltac:(lia) ltac:(lia)) as ST2.
assert (FR2 : rw_cells asegs (write_to_mem m0 (wa dst) bs) (bv_unsigned sp + -16) [CB 8 (firstn 8 junk0); C8 ra]).
{ eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [right; lia| exact I]. }
change (write_to_mem m0 (Z_to_bv 64 dst) bs) with (write_to_mem m0 (wa dst) bs).
clear SOK2 MU MU1 WM WM1 DST ST FR MI WR.
set (m2 := write_to_mem m0 (wa dst) bs) in *. clearbody m2.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 902996) 4) with (Z_to_bv 64 903000 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step.
unfold len_word. step. if_truex.
step.
apply evt_done. release_frame FR2 ST2 (bv_unsigned sp).
eapply HK; [exact MU2| exact WM2| exact MI2| exact ST2| exact DST2| exact HN| exact FDS| exact FSE].
Qed.

Lemma close_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(e : FdEntry) (lo : Z),
CK J c ->
a0 = Z_to_bv 64 3 ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some e ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
CNEXT J c c' -> m_fds (cfg_model c') = fd_remove (m_fds (cfg_model c)) (Z_to_bv 64 3) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J K c'
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 CLOSE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> Hfd ST LOS SPH MI RA HK.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply (aj_evt J). unfold CLOSE_SYM.
carve_frame 16%nat ST.
do 3 step. step.
do 8 step. step.
do 7 step.
apply evt_done.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_close F fc asegs J (SYS F fc) R pc mm ro c 3 e K HCK); [reflexivity | reflexivity | lia | exact Hfd |] end.
intros c' HN FDS FSE.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 902996) 4) with (Z_to_bv 64 903000 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step. step.
do 2 step. step. if_truex. step.
do 3 step. step.
apply evt_done. release_frame FR ST (bv_unsigned sp).
eapply HK; [exact MU| exact WM| exact MI| exact ST| exact HN| exact FDS| exact FSE].
Qed.

Lemma read_dir_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (K : TSet)
(dst cnt lo : Z) (errv : word),
CK J c ->
a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 dst -> a2 = Z_to_bv 64 cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 3) = Some FdDir ->
1 <= cnt <= 65536 -> 0 < dst -> dst + cnt <= lo -> 0x645000 <= lo ->
(exists junk, rw_cells asegs m dst [CB (Z.to_nat cnt) junk]) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] -> 0xe7000 <= bv_unsigned tp - 164 -> bv_unsigned tp <= 0x645000 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte) (c' : config),
munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m m' -> wmono asegs m m' ->
mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (bv_unsigned tp - 164) [C4 (Z_to_bv 64 EISDIR)] ->
CNEXT J c c' -> same_io c c' ->
AJ J K c' (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J K c (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READ_SYM) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HCK -> -> -> Hfd Hcnt Hdst Hlo Hlo2 (junk & DST) ST LOS SPH ERR TPL TPH MI RA HK.
word_range sp SPR. word_range tp TPR.
replace (bv_unsigned tp - 164) with (bv_unsigned tp + -164) in ERR by lia.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned tp - 164, bv_unsigned tp - 160)] m) as MU.
apply (aj_evt J). unfold READ_SYM.
carve_frame 16%nat ST.
do 10 step. step.
do 7 step.
apply evt_done.
pose proof (wr_at_store_ok asegs m0 dst _ 0 (Z.to_nat cnt) (proj2 DST) ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as SOK.
rewrite Z.add_0_r in SOK.
lazymatch goal with |- AJ _ _ _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ c K ecall_fetch ecall_is) end.
assert (WR : QZDE.wr_at asegs m0 dst cnt).
{ pose proof (proj2 DST) as W. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W. }
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_read_dir F fc asegs J (SYS F fc) R pc mm ro c 3 dst cnt K HCK);
[reflexivity | reflexivity | lia | reflexivity | reflexivity | lia | unfold TASK_SIZE; lia | exact WR | exact Hfd |] end.
intros c' HN SIO.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
replace (QsRG.Mq0.v_addi (Z_to_bv 64 902996) 4) with (Z_to_bv 64 903000 : word) by (apply bv_eq; vm_compute; reflexivity).
unfold QsRG.Mq0.regupd. simp_regs.
step.
do 5 step.
unfold errno_ret, EISDIR. step.
replace (bv_ltu (Z_to_bv 64 (- (21))) (Z_to_bv 64 (-4095))) with false by (vm_compute; reflexivity). cbv iota.
step. step. step.
step.
step. step. step. step.
step.
replace (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- (21)))))) with (Z_to_bv 64 21 : word) in * by (apply bv_eq; vm_compute; reflexivity).
do 4 step. step.
apply evt_done. release_frame FR ST (bv_unsigned sp).
replace (bv_unsigned tp + -164) with (bv_unsigned tp - 164) in ERR by lia.
eapply HK; [exact MU| exact WM| exact MI| exact ST| unfold EISDIR; exact ERR| exact HN| exact SIO].
Qed.
End DrvSysA.
