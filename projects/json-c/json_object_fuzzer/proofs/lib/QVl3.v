(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Qc27 Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QnRU QteI QQNJ QMPy QIG5 QC9y Qr5k QbPx_c1 QCqp Qi1S QHRw Qvzz Q8Kb QCFK QlES QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0 QQNJ.Mq3.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qi1S.Mq1 QCqp.Mq1 QHRw.Mq0 Qvzz.Mq0 Q8Kb.Mq0 QCFK.Mq0.
Import Q8Kb.Mq1 Q8Kb.Mq2 Q8Kb.Mq3 QCFK.Mq1.
Import QlES.
Import QXE1.Mq0.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Jsonc.
Context {BAND : Band}.

Definition snprintf_ld_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n i : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_ld ->
-2^63 <= i < 2^63 -> bv_unsigned a3 = i mod 2^64 ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 21 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text i)) (dec_text i) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_ld_proof : snprintf_ld_stmt.
Proof.
unfold snprintf_ld_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 Hi Ha3 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
pose proof (dec_text_length i ltac:(lia)) as L.
eapply (snprintf_icpt_proof A_FMT_ld FMT_ld printf_common_ld (vsnprintf_proof A_FMT_ld FMT_ld printf_common_ld)) with (args := [PA_li i]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_ld_bytes; exact MI) | (unfold FMT_ld; forall_range) | apply pass1_ok_ld | (apply printf_sn_ld; exact Hi) | apply fp_calls_ld
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | lia])
| (unfold zlength in *; lia) | (unfold A_FMT_ld; lia) | (unfold A_FMT_ld, STATIC_SPLIT, FMT_ld, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_ld, FMT_ld, zlength; cbn [length]; lia)
| (apply RD; unfold zlength in *; lia) | (intros K; apply RD; unfold zlength in *; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.

Definition snprintf_lu_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in let u := bv_unsigned a3 in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_lu ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 21 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text u)) (dec_text u) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_lu_proof : snprintf_lu_stmt.
Proof.
unfold snprintf_lu_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
pose proof (bv_unsigned_in_range 64 a3) as Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ru.
pose proof (dec_text_length (bv_unsigned a3) ltac:(lia)) as L.
eapply (snprintf_icpt_proof A_FMT_lu FMT_lu printf_common_lu (vsnprintf_proof A_FMT_lu FMT_lu printf_common_lu)) with (args := [PA_lu (bv_unsigned a3)]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_lu_bytes; exact MI) | (unfold FMT_lu; forall_range) | apply pass1_ok_lu | (apply printf_sn_lu; lia) | apply fp_calls_lu
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | reflexivity | lia])
| (unfold zlength in *; lia) | (unfold A_FMT_lu; lia) | (unfold A_FMT_lu, STATIC_SPLIT, FMT_lu, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_lu, FMT_lu, zlength; cbn [length]; lia)
| (apply RD; unfold zlength in *; lia) | (intros K; apply RD; unfold zlength in *; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.

Definition snprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_u00cc ->
-2^31 <= c1 < 2^31 -> bv_unsigned a3 mod 2^32 = c1 mod 2^32 ->
-2^31 <= c2 < 2^31 -> bv_unsigned a4 mod 2^32 = c2 mod 2^32 ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(7 <= dn)%nat -> (7 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 7 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 6 [92; 117; 48; 48; c1 mod 256; c2 mod 256] lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_u00cc_proof : snprintf_u00cc_stmt.
Proof.
unfold snprintf_u00cc_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 Hc1 Hs1 Hc2 Hs2 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
eapply (snprintf_icpt_proof A_FMT_u00cc FMT_u00cc printf_common_u00cc (vsnprintf_proof A_FMT_u00cc FMT_u00cc printf_common_u00cc)) with (args := [PA_i c1; PA_i c2]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_u00cc_bytes; exact MI) | (unfold FMT_u00cc; forall_range) | apply pass1_ok_u00cc | apply printf_sn_u00cc | apply fp_calls_u00cc
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | lia])
| (unfold zlength; cbn [length]; lia) | (unfold A_FMT_u00cc; lia) | (unfold A_FMT_u00cc, STATIC_SPLIT, FMT_u00cc, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_u00cc, FMT_u00cc, zlength; cbn [length]; lia)
| (apply RD; unfold zlength; cbn [length]; lia) | (intros K; apply RD; unfold zlength; cbn [length]; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.
End Jsonc.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbPx_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbPx_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi1S.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHRw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHRw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvzz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Kb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCFK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCFK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Kb.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Kb.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8Kb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Kb.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCFK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCFK.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section Jsonc.
Context {BAND : Band}.

Definition snprintf_ld_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n i : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_ld ->
-2^63 <= i < 2^63 -> bv_unsigned a3 = i mod 2^64 ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 21 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text i)) (dec_text i) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_ld_proof : snprintf_ld_stmt.
Proof.
unfold snprintf_ld_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 Hi Ha3 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
pose proof (dec_text_length i ltac:(lia)) as L.
eapply (snprintf_icpt_proof A_FMT_ld FMT_ld printf_common_ld (vsnprintf_proof A_FMT_ld FMT_ld printf_common_ld)) with (args := [PA_li i]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_ld_bytes; exact MI) | (unfold FMT_ld; forall_range) | apply pass1_ok_ld | (apply printf_sn_ld; exact Hi) | apply fp_calls_ld
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | lia])
| (unfold zlength in *; lia) | (unfold A_FMT_ld; lia) | (unfold A_FMT_ld, STATIC_SPLIT, FMT_ld, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_ld, FMT_ld, zlength; cbn [length]; lia)
| (apply RD; unfold zlength in *; lia) | (intros K; apply RD; unfold zlength in *; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.

Definition snprintf_lu_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in let u := bv_unsigned a3 in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_lu ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(21 <= dn)%nat -> (21 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 21 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (zlength (dec_text u)) (dec_text u) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_lu_proof : snprintf_lu_stmt.
Proof.
unfold snprintf_lu_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
pose proof (bv_unsigned_in_range 64 a3) as Ru. unfold bv_modulus in Ru. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ru.
pose proof (dec_text_length (bv_unsigned a3) ltac:(lia)) as L.
eapply (snprintf_icpt_proof A_FMT_lu FMT_lu printf_common_lu (vsnprintf_proof A_FMT_lu FMT_lu printf_common_lu)) with (args := [PA_lu (bv_unsigned a3)]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_lu_bytes; exact MI) | (unfold FMT_lu; forall_range) | apply pass1_ok_lu | (apply printf_sn_lu; lia) | apply fp_calls_lu
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | reflexivity | lia])
| (unfold zlength in *; lia) | (unfold A_FMT_lu; lia) | (unfold A_FMT_lu, STATIC_SPLIT, FMT_lu, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_lu, FMT_lu, zlength; cbn [length]; lia)
| (apply RD; unfold zlength in *; lia) | (intros K; apply RD; unfold zlength in *; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.

Definition snprintf_u00cc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A_FMT_u00cc ->
-2^31 <= c1 < 2^31 -> bv_unsigned a3 mod 2^32 = c1 mod 2^32 ->
-2^31 <= c2 < 2^31 -> bv_unsigned a4 mod 2^32 = c2 mod 2^32 ->
rw_cells asegs m D [CB dn junkd] -> ISH m ->
(7 <= dn)%nat -> (7 <= n < 2^63) ->
stk asegs m lo q -> (lo <= q - SNP_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(D + Z.of_nat dn <= lo \/ q <= D) ->
dapp D (Z.of_nat dn) -> (forall k, 0 < k <= 7 -> rng_ok m D k) ->
evt asegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 6 [92; 117; 48; 48; c1 mod 256; c2 mod 256] lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 snprintf_stub) fc None m (seg_rom asegs)).

Theorem snprintf_u00cc_proof : snprintf_u00cc_stmt.
Proof.
unfold snprintf_u00cc_stmt. intros until canary. cbv zeta. intros Ha0 Ha1 Ha2 Hc1 Hs1 Hc2 Hs2 DST ISHm Hdn Hn ST LO GLO QHI SSP MI FRM DD1 DAPP RD.
eapply (snprintf_icpt_proof A_FMT_u00cc FMT_u00cc printf_common_u00cc (vsnprintf_proof A_FMT_u00cc FMT_u00cc printf_common_u00cc)) with (args := [PA_i c1; PA_i c2]).
all: first [ exact Ha0 | exact Ha1 | exact Ha2 | exact DST | exact ISHm | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact DD1 | exact DAPP
| (apply fmt_u00cc_bytes; exact MI) | (unfold FMT_u00cc; forall_range) | apply pass1_ok_u00cc | apply printf_sn_u00cc | apply fp_calls_u00cc
| (cbn [sargs_ok sarg_ok]; repeat split; first [assumption | lia])
| (unfold zlength; cbn [length]; lia) | (unfold A_FMT_u00cc; lia) | (unfold A_FMT_u00cc, STATIC_SPLIT, FMT_u00cc, zlength; cbn [length]; lia)
| (apply szone_fmt; unfold gzone, A_FMT_u00cc, FMT_u00cc, zlength; cbn [length]; lia)
| (apply RD; unfold zlength; cbn [length]; lia) | (intros K; apply RD; unfold zlength; cbn [length]; lia) | lia
| match goal with |- ?g => idtac "LEFT" g; fail end ].
Qed.
End Jsonc.
