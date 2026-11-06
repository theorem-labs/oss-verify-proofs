(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QsV0 QBxa QSpR QS67 QCKW Qujl QuXQ QPra QY6W QQ7a QZsi Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4 QBxa.Mq5 QSpR.Mq0 QBxa.Mq2.
Import QS67 QCKW.Mq2 QCKW.Mq3 Qujl.Mq0 QuXQ.Mq0 Qujl.Mq1 QuXQ.Mq1 QPra.Mq0 QY6W QQ7a.
Import QZsi.

Import QCKW.Mq4.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.
Variable J : aj_base RSEGS.
Hypothesis SYS : @Q0TL.aj_sys fF fC RSEGS J.
Local Notation RZAc md ms K := (AJ J K md ms).

Theorem stdio_exit_flush_A :
forall regs mem model (sp code : word) (wp2 rp2 wp0 rp0 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 1 = Z_to_bv 64 0xcc71c ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xea840 wp0 rp0 ->
file_clean mem 0xea660 wp2 rp2 ->
stdout_pending mem wb wp bufp bufsz rp1 can pending ->
CK J model ->
RZAc model (mkst regs (0xd2fb0 : word) mem (seg_rom RSEGS))
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs (cfg_model model)))).
Proof.
intros regs mem model sp code wp2 rp2 wp0 rp0 wb wp bufp bufsz rp1 can pending Hsp Hs0 Hra SPlo SPhi SOK SG FC0 FC2 SP HCK0.
pose proof (u64_range sp) as Hspr.
destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
pose proof SG as (Gnl & Gofl & Gin & Gout & Gerr).

destruct (w3b1 regs mem (seg_rom RSEGS) sp code wb wp wp0 rp0)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ repeat split; assumption. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN3 |]. clear RUN3.

replace (Z_to_bv 64 0xd3060) with (0xd3060 : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a mem sp code).
eapply (ref_stdio_write J SYS regs3 mem3 model (bv_unsigned sp - 32) 0xea750 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0xd3060 : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a; sok_stack SOK
| lia | lia
|  split; subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve
|  split; subst mem3; unfold mem_w3a; rdn_solve
| left; reflexivity | exact HCK0
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 c4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST HN4 [_ HS4].
rewrite R3s0 in Q8.
destruct FC2 as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
zaddr P1rp; zaddr P1re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN5 |]. clear RUN5.
rewrite <- HS4. eapply (AJ_exit_at RSEGS J SYS); [exact F_cc4ac | exact E_cc4ac | exact (cnext_ck _ J _ _ HN4) | right; exact R5a7 | exact R5a0].
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1jK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuXQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuXQ.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuXQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuXQ.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPra.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxOv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxOv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwsr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwsr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.
Variable J : aj_base RSEGS.
Hypothesis SYS : @Qfub.aj_sys fF fC RSEGS J.
Local Notation RZAc md ms K := (AJ J K md ms).

Theorem stdio_exit_flush_A :
forall regs mem model (sp code : word) (wp2 rp2 wp0 rp0 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 1 = Z_to_bv 64 0xcede0 ->
(4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
stdio_globalsA mem ->
file_clean mem 0xecf20 wp0 rp0 ->
file_clean mem 0xecd40 wp2 rp2 ->
stdout_pending mem wb wp bufp bufsz rp1 can pending ->
CK J model ->
RZAc model (mkst regs (0xd5674 : word) mem (seg_rom RSEGS))
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs (cfg_model model)))).
Proof.
intros regs mem model sp code wp2 rp2 wp0 rp0 wb wp bufp bufsz rp1 can pending Hsp Hs0 Hra SPlo SPhi SOK SG FC0 FC2 SP HCK0.
pose proof (u64_range sp) as Hspr.
destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
pose proof SG as (Gnl & Gofl & Gin & Gout & Gerr).

destruct (w3b1 regs mem (seg_rom RSEGS) sp code wb wp wp0 rp0)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ repeat split; assumption. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN3 |]. clear RUN3.

replace (Z_to_bv 64 0xd5724) with (0xd5724 : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a mem sp code).
eapply (ref_stdio_write J SYS regs3 mem3 model (bv_unsigned sp - 32) 0xece30 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0xd5724 : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a; sok_stack SOK
| lia | lia
|  split; subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve
|  split; subst mem3; unfold mem_w3a; rdn_solve
| left; reflexivity | exact HCK0
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 c4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST HN4 [_ HS4].
rewrite R3s0 in Q8.
destruct FC2 as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
zaddr P1rp; zaddr P1re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN5 |]. clear RUN5.
rewrite <- HS4. eapply (AJ_exit_at RSEGS J SYS); [exact F_ceb98 | exact E_ceb98 | exact (cnext_ck _ J _ _ HN4) | right; exact R5a7 | exact R5a0].
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
