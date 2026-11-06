(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QS67 Qujl QY6W QQ7a Q9dN QpBN QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import QS67 Qujl.Mq0 QY6W QQ7a Q9dN QpBN QCKW.Mq3.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (0xea750 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (0xea750 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
/\ rdn RSEGS mem (Z_to_bv 64 (0xea750 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
/\ rdn RSEGS mem (Z_to_bv 64 (0xea750 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd29d0)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z) (wp0 rp0 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0xcc71c ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xea840 wp0 rp0 ->
stdout_dirty_hdr mem wb wp ->
(0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
exists regs',
msteps RSEGS (mkst regs (0xd2fb0 : word) mem rom)
(mkst regs' (0xd29d0 : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = Z_to_bv 64 0xea750
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 1 = Z_to_bv 64 0xd3060
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
/\ getr regs' 8 = Z_to_bv 64 0xea750
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
intros regs mem rom sp code wb wp wp0 rp0 Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F0l & F0wp & F0wb & F0rp & F0re) (F1l & F1wp & F1wb & F1wr) WB WP NE.
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
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

stepLD8 F_d3064 D_d3064 (Z_to_bv 64 wp).
stepLD8 F_d3068 D_d3068 (Z_to_bv 64 wb).
stepb_ft F_d306c D_d306c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

stepLD8 F_d3070 D_d3070 (Z_to_bv 64 0xd29d0).
stepn F_d3074 D_d3074.
stepn F_d3078 D_d3078.
stepn F_d307c D_d307c.
stepjr F_d3080 D_d3080 (Z_to_bv 64 0xd29d0) ltac:(gres; reflexivity). vnorm.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xea750 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xcc71c)) ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
rdn RSEGS mem (Z_to_bv 64 (0xea750 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 (0xea750 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 0xea748) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea660)) ->
file_clean mem 0xea660 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0xd3060 : word) mem rom)
(mkst regs' (0xcc488 : word) mem rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
(F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
eexists. split.
-
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
stepn F_d3170 D_d3170. rewrite Hsp. sp_renorm.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0 QBxa Q035.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Import QCKW.Mq2 Qujl.Mq1 QY6W QQ7a Q035.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
/\ getr regs' 21 = getr regs 21
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd2a5c : word) mem rom) (mkst regs' (0xd2a64 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_d2a80 D_d2a80.
stepn F_cca2c D_cca2c.
stepn F_cca30 D_cca30.
stepb_tk F_cca34 D_cca34 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cca60 D_cca60 (0xd2a60 : word) ltac:(bveq).
stepb_ft F_d2a84 D_d2a84 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0xd2a5c : word) mem rom) (mkst regs' (0xd2af0 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_d2a80 D_d2a80.
stepn F_cca2c D_cca2c.
stepn F_cca30 D_cca30.
stepb_tk F_cca34 D_cca34 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cca60 D_cca60 (0xd2a60 : word) ltac:(bveq).
stepb_tk F_d2a84 D_d2a84 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd2ae4 : word) mem rom) (mkst regs' (0xd2a64 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_d2b08 D_d2b08.
stepn F_cca2c D_cca2c.
stepn F_cca30 D_cca30.
stepb_tk F_cca34 D_cca34 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cca60 D_cca60 (0xd2ae8 : word) ltac:(bveq).
stepn F_d2b0c D_d2b0c.
stepb_tk F_d2b10 D_d2b10 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0xd2ae4 : word) mem rom) (mkst regs' (0xd2af0 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_d2b08 D_d2b08.
stepn F_cca2c D_cca2c.
stepn F_cca30 D_cca30.
stepb_tk F_cca34 D_cca34 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cca60 D_cca60 (0xd2ae8 : word) ltac:(bveq).
stepn F_d2b0c D_d2b0c.
stepb_ft F_d2b10 D_d2b10 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
(su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
(1 <= ic <= 2)%Z ->
(1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
(bv_unsigned b0 + n0 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd2af0 : word) mem rom)
(mkst regs' (0xd2ae0 : word)
(wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
(Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
/\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io ic cnt n0 rem b0
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
pose proof (u64_range b0) as Hb0.
eexists. split.
-
stepb_ft F_d2b14 D_d2b14 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_d2b18 D_d2b18 (Z_to_bv 64 n0).

stepn F_d2b1c D_d2b1c. rewrite Ha0, (sltu_ge n0 cnt) by lia.

stepn F_d2b20 D_d2b20.
stepn F_d2b24 D_d2b24. rewrite Hs3.

stepLD8 F_d2b28 D_d2b28 b0.

stepn F_d2b2c D_d2b2c.
stepn F_d2b30 D_d2b30. rewrite v_and_0_l.
stepn F_d2b34 D_d2b34. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.

stepn F_d2b38 D_d2b38. rewrite (v_add_wZ b0 cnt) by lia.

stepST F_d2b3c D_d2b3c (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).

stepb_tk F_d2b40 D_d2b40 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).

stepn F_d2ad8 D_d2ad8.
stepn F_d2adc D_d2adc.
stepn F_d2ae0 D_d2ae0. rewrite Hs3, (v_add_ZZ' io 8) by lia.

stepLD8 F_d2ae4 D_d2ae4 (Z_to_bv 64 n0).

stepn F_d2ae8 D_d2ae8. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_d2aec D_d2aec (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_d2af0 D_d2af0. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.

stepn F_d2af4 D_d2af4. rewrite (v_sub_Z n0 cnt) by lia.
stepST F_d2af8 D_d2af8 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).

stepn F_d2afc D_d2afc.
stepn F_d2b00 D_d2b00.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
(su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
(0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
(bv_unsigned b1 + n1 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd2af0 : word) mem rom)
(mkst regs' (0xd2ae0 : word)
(wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
(Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io cnt n0 n1 rem b1
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
pose proof (u64_range b1) as Hb1.
eexists. split.
-
stepb_ft F_d2b14 D_d2b14 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_d2b18 D_d2b18 (Z_to_bv 64 n0).

stepn F_d2b1c D_d2b1c. rewrite Ha0, (sltu_lt n0 cnt) by lia.

stepn F_d2b20 D_d2b20.
stepn F_d2b24 D_d2b24. rewrite Hs3, (v_add_ZZ' io 16) by lia.

stepLD8 F_d2b28 D_d2b28 b1.

stepn F_d2b2c D_d2b2c.
stepn F_d2b30 D_d2b30. rewrite (v_and_m1_l n0) by lia.
stepn F_d2b34 D_d2b34. rewrite Ha0, (v_sub_Z cnt n0) by lia.

stepn F_d2b38 D_d2b38. rewrite (v_add_wZ b1 (cnt - n0)) by lia.

stepST F_d2b3c D_d2b3c (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).

stepb_ft F_d2b40 D_d2b40 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).

stepn F_d2b44 D_d2b44.
stepn F_d2b48 D_d2b48.
stepn F_d2adc D_d2adc.
stepn F_d2ae0 D_d2ae0. rewrite Hs3, (v_add_ZZ' io 24) by lia.

stepLD8 F_d2ae4 D_d2ae4 (Z_to_bv 64 n1).

stepn F_d2ae8 D_d2ae8. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_d2aec D_d2aec (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_d2af0 D_d2af0. rewrite Hs2. vals_lit.

stepn F_d2af4 D_d2af4. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
stepST F_d2af8 D_d2af8 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).

stepn F_d2afc D_d2afc.
stepn F_d2b00 D_d2b00.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
wbytes (wbytes (wbytes mem1
(Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
(Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
(Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
getr regs 2 = Z_to_bv 64 (su - 112) ->
getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
getr regs 21 = Z_to_bv 64 0x642ea0 ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
ret_ok ret ->
rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 0x642ea0) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
exists regs',
msteps RSEGS (mkst regs (0xd2a64 : word) mem rom)
(mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
/\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
/\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
/\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
unfold mem_sw2. eexists. split.
-
stepLD F_d2a88 D_d2a88 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2a8c D_d2a8c (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_d2a90 D_d2a90.

stepST F_d2a94 D_d2a94 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
stepST F_d2a98 D_d2a98 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
stepST F_d2a9c D_d2a9c (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).

stepn F_d2aa0 D_d2aa0. rewrite Hs0.
stepLD F_d2aa4 D_d2aa4 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2aa8 D_d2aa8 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_d2aac D_d2aac ltac:(apply c_eq_refl).

stepLD F_d2ab0 D_d2ab0 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2ab4 D_d2ab4 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2ab8 D_d2ab8 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2abc D_d2abc (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2ac0 D_d2ac0 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2ac4 D_d2ac4 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2ac8 D_d2ac8 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d2acc D_d2acc (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_d2ad0 D_d2ad0. rewrite Hsp. sp_renorm.
replace (su - 0)%Z with su by lia.
stepret F_d2ad4 D_d2ad4 ret ltac:(reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 Qhd4 Q3Gm QlKV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Q7UD Qwm6.
Import Qhd4.Mq0.
Import Q3Gm.Mq0.
Import Qwm6.Mq0 QlKV.Mqa.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma size_test_big : forall n, (n = 0 \/ 65 <= n < 2^63) -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = true.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
apply negb_true_iff. apply Z.ltb_ge.
destruct Hn as [-> | Hn]; [change ((0 + -65) mod 2^64) with (2^64 - 65); lia|].
rewrite Z.mod_small by lia. lia.
Qed.

Lemma asan_rt_get : forall m a bs, asan_rt_ok m -> In (a, bs) a4_rt_cells -> bytes_at asegs m a bs.
Proof. intros m a bs H HI. unfold asan_rt_ok in H. rewrite Forall_forall in H. exact (H (a, bs) HI). Qed.
Ltac rt_in := cbn [a4_rt_cells a4_rt_consts app]; unfold A_GOT_SB, A_SB_CELL, A_SB; repeat (first [ left; reflexivity | right ]).

Lemma asan_rt_ok_stack {RC__ : Q6q3.RunConsts} :
forall m m' lo hi, asan_rt_ok m -> munch [(lo, hi)] m m' -> alloc_ceiling <= lo -> asan_rt_ok m'.
Proof.
intros m m' lo hi RT MU LO. eapply asan_rt_ok_transport; [exact RT | exact MU |].
intros c Hc. pose proof (a4_rt_cells_in_img c Hc) as B. pose proof alloc_ceiling_ge as G.
cbn [disjoint_from]. split; [left; lia | exact I].
Qed.

Tactic Notation "rt_cell" constr(RT) constr(a) "as" ident(H) :=
lazymatch type of RT with asan_rt_ok ?m => pose proof (asan_rt_get m a _ RT ltac:(rt_in)) as H; cbn [fst snd] in H end.

Lemma real_memcpy_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= S < 2^64 -> S + n <= 2^64 -> 0 <= n < 2^63 ->
bytes_at asegs m S src -> length src = Z.to_nat n ->
rw_cells asegs m D [CB (Z.to_nat n) junk] -> (S + n <= D \/ D + n <= S) -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn HS HSn Hn SRC SRCL DST DISJ MI.
pose proof (Qhd4.Mq0.memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as X.
rewrite (unsigned_lit D), (unsigned_lit S), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. unfold Qhd4.Mq0.memcpy_post in P. rewrite ?(unsigned_lit D), ?(unsigned_lit S), ?(unsigned_lit n) in P by lia. exact P.
Qed.

Section RC__icpt. Context {RC__ : Q6q3.RunConsts}.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf07d9 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aae0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End RC__icpt.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Q1jK QxOv Qwsr QGoa Q9j0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1.
Import Q1jK Qujl.Mq2 QxOv Qwsr QGoa Q9j0 QCKW.Mq8.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
rdn RSEGS mem (Z_to_bv 64 (0xece30 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
/\ rdn RSEGS mem (Z_to_bv 64 (0xece30 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
/\ rdn RSEGS mem (Z_to_bv 64 (0xece30 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
/\ rdn RSEGS mem (Z_to_bv 64 (0xece30 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd5094)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z) (wp0 rp0 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
getr regs 1 = Z_to_bv 64 0xcede0 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xecf20 wp0 rp0 ->
stdout_dirty_hdr mem wb wp ->
(0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
exists regs',
msteps RSEGS (mkst regs (0xd5674 : word) mem rom)
(mkst regs' (0xd5094 : word) (mem_w3a mem sp code) rom)
/\ getr regs' 10 = Z_to_bv 64 0xece30
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 1 = Z_to_bv 64 0xd5724
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
/\ getr regs' 8 = Z_to_bv 64 0xece30
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
intros regs mem rom sp code wb wp wp0 rp0 Hsp Hs0 Hra SPlo SPhi SOK
(Gnl & Gofl & Gin & Gout & Gerr) (F0l & F0wp & F0wb & F0rp & F0re) (F1l & F1wp & F1wb & F1wr) WB WP NE.
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
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

stepLD8 F_d5750 D_d5750 (Z_to_bv 64 wp).
stepLD8 F_d5754 D_d5754 (Z_to_bv 64 wb).
stepb_ft F_d5758 D_d5758 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

stepLD8 F_d575c D_d575c (Z_to_bv 64 0xd5094).
stepn F_d5760 D_d5760.
stepn F_d5764 D_d5764.
stepn F_d5768 D_d5768.
stepjr F_d576c D_d576c (Z_to_bv 64 0xd5094) ltac:(gres; reflexivity). vnorm.
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xece30 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xcede0)) ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
rdn RSEGS mem (Z_to_bv 64 (0xece30 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 (0xece30 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
rdn RSEGS mem (Z_to_bv 64 0xece28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xecd40)) ->
file_clean mem 0xecd40 wp2 rp2 ->
exists regs',
msteps RSEGS (mkst regs (0xd5724 : word) mem rom)
(mkst regs' (0xceb4c : word) mem rom)
/\ getr regs' 10 = code
/\ getr regs' 17 = Z_to_bv 64 94
/\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
(F2l & F2wp & F2wb & F2rp & F2re).
zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
eexists. split.
-
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
stepn F_d585c D_d585c. rewrite Hsp. sp_renorm.
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
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB3U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4.
Import QCKW.Mq7 Qujl.Mq3 QxOv Qwsr QB3U.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
/\ getr regs' 21 = getr regs 21
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

Lemma sw_c1_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd5120 : word) mem rom) (mkst regs' (0xd5128 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_d516c D_d516c.
stepn F_cf118 D_cf118.
stepn F_cf11c D_cf11c.
stepb_tk F_cf120 D_cf120 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cf14c D_cf14c (0xd5124 : word) ltac:(bveq).
stepb_ft F_d5170 D_d5170 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0xd5120 : word) mem rom) (mkst regs' (0xd51b4 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_d516c D_d516c.
stepn F_cf118 D_cf118.
stepn F_cf11c D_cf11c.
stepb_tk F_cf120 D_cf120 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cf14c D_cf14c (0xd5124 : word) ltac:(bveq).
stepb_tk F_d5170 D_d5170 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd51a8 : word) mem rom) (mkst regs' (0xd5128 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_d51f4 D_d51f4.
stepn F_cf118 D_cf118.
stepn F_cf11c D_cf11c.
stepb_tk F_cf120 D_cf120 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cf14c D_cf14c (0xd51ac : word) ltac:(bveq).
stepn F_d51f8 D_d51f8.
stepb_tk F_d51fc D_d51fc ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0xd51a8 : word) mem rom) (mkst regs' (0xd51b4 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_d51f4 D_d51f4.
stepn F_cf118 D_cf118.
stepn F_cf11c D_cf11c.
stepb_tk F_cf120 D_cf120 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_cf14c D_cf14c (0xd51ac : word) ltac:(bveq).
stepn F_d51f8 D_d51f8.
stepb_ft F_d51fc D_d51fc ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
(su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
(1 <= ic <= 2)%Z ->
(1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
(bv_unsigned b0 + n0 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd51b4 : word) mem rom)
(mkst regs' (0xd51a4 : word)
(wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
(Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
/\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io ic cnt n0 rem b0
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
pose proof (u64_range b0) as Hb0.
eexists. split.
-
stepb_ft F_d5200 D_d5200 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_d5204 D_d5204 (Z_to_bv 64 n0).

stepn F_d5208 D_d5208. rewrite Ha0, (sltu_ge n0 cnt) by lia.

stepn F_d520c D_d520c.
stepn F_d5210 D_d5210. rewrite Hs3.

stepLD8 F_d5214 D_d5214 b0.

stepn F_d5218 D_d5218.
stepn F_d521c D_d521c. rewrite v_and_0_l.
stepn F_d5220 D_d5220. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.

stepn F_d5224 D_d5224. rewrite (v_add_wZ b0 cnt) by lia.

stepST F_d5228 D_d5228 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).

stepb_tk F_d522c D_d522c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).

stepn F_d51c4 D_d51c4.
stepn F_d51c8 D_d51c8.
stepn F_d51cc D_d51cc. rewrite Hs3, (v_add_ZZ' io 8) by lia.

stepLD8 F_d51d0 D_d51d0 (Z_to_bv 64 n0).

stepn F_d51d4 D_d51d4. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_d51d8 D_d51d8 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_d51dc D_d51dc. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.

stepn F_d51e0 D_d51e0. rewrite (v_sub_Z n0 cnt) by lia.
stepST F_d51e4 D_d51e4 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).

stepn F_d51e8 D_d51e8.
stepn F_d51ec D_d51ec.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
(su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
(0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
(bv_unsigned b1 + n1 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0xd51b4 : word) mem rom)
(mkst regs' (0xd51a4 : word)
(wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
(Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io cnt n0 n1 rem b1
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
pose proof (u64_range b1) as Hb1.
eexists. split.
-
stepb_ft F_d5200 D_d5200 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_d5204 D_d5204 (Z_to_bv 64 n0).

stepn F_d5208 D_d5208. rewrite Ha0, (sltu_lt n0 cnt) by lia.

stepn F_d520c D_d520c.
stepn F_d5210 D_d5210. rewrite Hs3, (v_add_ZZ' io 16) by lia.

stepLD8 F_d5214 D_d5214 b1.

stepn F_d5218 D_d5218.
stepn F_d521c D_d521c. rewrite (v_and_m1_l n0) by lia.
stepn F_d5220 D_d5220. rewrite Ha0, (v_sub_Z cnt n0) by lia.

stepn F_d5224 D_d5224. rewrite (v_add_wZ b1 (cnt - n0)) by lia.

stepST F_d5228 D_d5228 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).

stepb_ft F_d522c D_d522c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).

stepn F_d5230 D_d5230.
stepn F_d5234 D_d5234.
stepn F_d51c8 D_d51c8.
stepn F_d51cc D_d51cc. rewrite Hs3, (v_add_ZZ' io 24) by lia.

stepLD8 F_d51d0 D_d51d0 (Z_to_bv 64 n1).

stepn F_d51d4 D_d51d4. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_d51d8 D_d51d8 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_d51dc D_d51dc. rewrite Hs2. vals_lit.

stepn F_d51e0 D_d51e0. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
stepST F_d51e4 D_d51e4 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).

stepn F_d51e8 D_d51e8.
stepn F_d51ec D_d51ec.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
wbytes (wbytes (wbytes mem1
(Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
(Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
(Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
getr regs 2 = Z_to_bv 64 (su - 112) ->
getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
getr regs 21 = Z_to_bv 64 0x645560 ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
ret_ok ret ->
rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 0x645560) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
exists regs',
msteps RSEGS (mkst regs (0xd5128 : word) mem rom)
(mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
/\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
/\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
/\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
unfold mem_sw2. eexists. split.
-
stepLD F_d5174 D_d5174 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d5178 D_d5178 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_d517c D_d517c.

stepST F_d5180 D_d5180 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
stepST F_d5184 D_d5184 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
stepST F_d5188 D_d5188 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).

stepn F_d518c D_d518c. rewrite Hs0.
stepLD F_d5190 D_d5190 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d5194 D_d5194 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_d5198 D_d5198 ltac:(apply c_eq_refl).

stepLD F_d519c D_d519c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51a0 D_d51a0 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51a4 D_d51a4 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51a8 D_d51a8 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51ac D_d51ac (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51b0 D_d51b0 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51b4 D_d51b4 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_d51b8 D_d51b8 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_d51bc D_d51bc. rewrite Hsp. sp_renorm.
replace (su - 0)%Z with su by lia.
stepret F_d51c0 D_d51c0 ret ltac:(reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3Gm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3Gm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma size_test_big : forall n, (n = 0 \/ 65 <= n < 2^63) -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = true.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
apply negb_true_iff. apply Z.ltb_ge.
destruct Hn as [-> | Hn]; [change ((0 + -65) mod 2^64) with (2^64 - 65); lia|].
rewrite Z.mod_small by lia. lia.
Qed.

Lemma asan_rt_get : forall m a bs, asan_rt_ok m -> In (a, bs) a4_rt_cells -> bytes_at asegs m a bs.
Proof. intros m a bs H HI. unfold asan_rt_ok in H. rewrite Forall_forall in H. exact (H (a, bs) HI). Qed.
Ltac rt_in := cbn [a4_rt_cells a4_rt_consts app]; unfold A_GOT_SB, A_SB_CELL, A_SB; repeat (first [ left; reflexivity | right ]).

Lemma asan_rt_ok_stack {RC__ : Q6q3.RunConsts} :
forall m m' lo hi, asan_rt_ok m -> munch [(lo, hi)] m m' -> alloc_ceiling <= lo -> asan_rt_ok m'.
Proof.
intros m m' lo hi RT MU LO. eapply asan_rt_ok_transport; [exact RT | exact MU |].
intros c Hc. pose proof (a4_rt_cells_in_img c Hc) as B. pose proof alloc_ceiling_ge as G.
cbn [disjoint_from]. split; [left; lia | exact I].
Qed.

Tactic Notation "rt_cell" constr(RT) constr(a) "as" ident(H) :=
lazymatch type of RT with asan_rt_ok ?m => pose proof (asan_rt_get m a _ RT ltac:(rt_in)) as H; cbn [fst snd] in H end.

Lemma real_memcpy_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= S < 2^64 -> S + n <= 2^64 -> 0 <= n < 2^63 ->
bytes_at asegs m S src -> length src = Z.to_nat n ->
rw_cells asegs m D [CB (Z.to_nat n) junk] -> (S + n <= D \/ D + n <= S) -> mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn HS HSn Hn SRC SRCL DST DISJ MI.
pose proof (Qhd4.Mq2.memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk) as X.
rewrite (unsigned_lit D), (unsigned_lit S), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact SRC | exact SRCL | exact DST | exact DISJ | exact MI] |].
intros ms' P. unfold Qhd4.Mq2.memcpy_post in P. rewrite ?(unsigned_lit D), ?(unsigned_lit S), ?(unsigned_lit n) in P by lia. exact P.
Qed.

Section RC__icpt. Context {RC__ : Q6q3.RunConsts}.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf2e99 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aeb8) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End RC__icpt.
