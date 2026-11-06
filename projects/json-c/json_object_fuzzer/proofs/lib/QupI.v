(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QZsi QS67 Qujl QY6W QCKW Qr6U QsRG Qnhz QBxa QRjH QsV0 Q9ox QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn Qwm6 QlKV QGm2 QbKA QjDJ QrJ1 Qlna Qirj QMjx Q0TL Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD QZsi.
Import QS67 Qujl.Mq0 QY6W QCKW.Mq2 Qr6U.Mq0 QCKW.Mq3.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 QRjH.Mq3 Q9ox.Mq0 QBxa.Mq5.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mq8.
Import QGm2.Mq0 QbKA.Mq2 QjDJ.Mq0 QrJ1.Mq0 Qlna.Mq0 Qirj.Mq0 QMjx.Mq0 Qujl.

Import QCKW.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section ExitA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @Q0TL.aj_sys F fc asegs J.

Lemma rdn_munch : forall W m m' (a : word) n bs,
rdn asegs m a n = Some bs -> munch W m m' -> disjoint_from W (bv_unsigned a) (Z.of_nat n) ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn asegs m' a n = Some bs.
Proof.
intros W m m' a n bs Hr MU DJ Hnw. rewrite (rdn_ext asegs n m' m a Hnw); [exact Hr|].
intros x Hx. apply MU. eapply disjoint_outside; [exact DJ | lia].
Qed.

Lemma store_ok_of_wr_at : forall m a n, wr_at asegs m a (Z.of_nat n) -> store_ok asegs m (Z_to_bv 64 a) n = true.
Proof.
intros m a n (Ha & Hn & Hw).
assert (G : forall k i, (Z.of_nat k + Z.of_nat i = Z.of_nat n)%Z -> store_ok asegs m (Z_to_bv 64 (a + Z.of_nat k)) i = true).
{ intros k i. revert k. induction i as [|i IH]; intros k Hk; [reflexivity|].
cbn [store_ok]. unfold wa in Hw.
destruct (wview asegs m (Z_to_bv 64 (a + Z.of_nat k))) eqn:E.
- replace (Z_to_bv 64 (a + Z.of_nat k) + 1)%bv with (Z_to_bv 64 (a + Z.of_nat (S k))).
+ apply (IH (S k)). lia.
+ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1 : word)) with 1%Z.
rewrite Zplus_mod_idemp_l. f_equal. lia.
- exfalso. apply (Hw (Z.of_nat k)); [lia | exact E]. }
replace a with (a + Z.of_nat 0)%Z by lia. apply (G 0%nat n). lia.
Qed.

Ltac wlit := rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Theorem exit_clean_A :
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) (wp1 rp1 wp2 rp2 wp0 rp0 : word),
CK J md ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 0x800000000000 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
stdio_globalsA m -> file_clean m 0xea840 wp0 rp0 -> file_clean m 0xea750 wp1 rp1 -> file_clean m 0xea660 wp2 rp2 ->
AJ J (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs (cfg_model md))) md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcc6b0) fc None m (seg_rom asegs)).
Proof.
intros until rp0. intros HCK MI ST CEIL LO AL SPHI XC SG FC0 FC1 FC2.
apply (aj_evt J).
eapply (exit_entry_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ lo tid g0 g1 g5 g6 g7 dso ob junkM mid
MI ST CEIL LO AL XC).
intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' FR'.

Ltac djW := unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; cbn [disjoint_from];
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac xfer K MU := eapply rdn_munch in K; [| exact MU | djW | wlit].
destruct SG as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (SG' : stdio_globalsA m') by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC0 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC0' : file_clean m' 0xea840 wp0 rp0) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC1 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC1' : file_clean m' 0xea750 wp1 rp1) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC2 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC2' : file_clean m' 0xea660 wp2 rp2) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.

assert (SOK : store_ok asegs m' (Z_to_bv 64 (bv_unsigned sp - 144)) 144 = true).
{ apply store_ok_of_wr_at. destruct ST' as (S1 & S2 & S3). destruct FR' as [[_ _] FW].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases (bv_unsigned sp - 144 + i) (bv_unsigned sp - 16)) as [Hl|Hg].
- apply (proj1 (S3 (bv_unsigned sp - 144 + i) ltac:(lia))).
- destruct FW as (_ & _ & FW3). replace (bv_unsigned sp - 144 + i) with (bv_unsigned sp - 16 + (i - 128)) by lia.
apply FW3. cbn [cells_size csize Nat.add] . lia. }

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
destruct (w3a (fF:=F) (fC:=fc) R m' (seg_rom asegs) sp a0 wp1 rp1 wp2 rp2 wp0 rp0) as (regs3 & RUN & R3a0 & R3a7 & R3sp);
[ reflexivity | reflexivity | reflexivity | lia | exact SPHI | exact SOK | exact SG' | exact FC0' | exact FC1' | exact FC2' | ]
end.
replace (Z_to_bv 64 864176 : word) with (864176%bv : word) by (apply bv_eq; reflexivity).
lazymatch type of RUN with QsRG.msteps _ ?x ?y =>
apply (evt_cut asegs (eq y)); [exists y; split; [apply msteps_of_ascatsim; exact RUN | reflexivity] |] end.
intros ms3 <-.

apply evt_done.
eapply (AJ_exit_at asegs J (SYS F fc)); [exact F_cc4ac | exact E_cc4ac | exact HCK | right; exact R3a7 | exact R3a0].
Qed.

Theorem exit_flush_A :
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) (wp2 rp2 wp0 rp0 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
CK J md ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 0x800000000000 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
stdio_globalsA m -> file_clean m 0xea840 wp0 rp0 -> file_clean m 0xea660 wp2 rp2 -> stdout_pending m wb wp bufp bufsz rp1 can pending ->
AJ J (t_emit (QBxa.Mq5.W 1 pending) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs (cfg_model md)))) md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcc6b0) fc None m (seg_rom asegs)).
Proof.
intros until pending. intros HCK MI ST CEIL LO AL SPHI XC SG FC0 FC2 SP.
apply (aj_evt J).
eapply (exit_entry_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ lo tid g0 g1 g5 g6 g7 dso ob junkM mid
MI ST CEIL LO AL XC).
intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' FR'.
Ltac djW2 := unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; cbn [disjoint_from];
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac xfer2 K MU := eapply rdn_munch in K; [| exact MU | djW2 | wlit].
destruct SG as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (SG' : stdio_globalsA m') by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC0 as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (FC0' : file_clean m' 0xea840 wp0 rp0) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC2 as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (FC2' : file_clean m' 0xea660 wp2 rp2) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct SP as [P1 P2 P3 P4 P5 P6 P7 P8 P9 RANGE LEN PMAX BYTES [Ggot Gcan]].
pose proof (u64_range can) as CANR.
xfer2 P1 MU. xfer2 P2 MU. xfer2 P3 MU. xfer2 P4 MU. xfer2 P5 MU. xfer2 P6 MU. xfer2 P7 MU. xfer2 P8 MU. xfer2 P9 MU.
eapply rdn_munch in BYTES; [| exact MU | djW2 | rewrite unsigned_lit by lia; lia].
xfer2 Ggot MU. xfer2 Gcan MU.
assert (SP' : stdout_pending m' wb wp bufp bufsz rp1 can pending).
{ constructor; try assumption. split; assumption. }
clear P1 P2 P3 P4 P5 P6 P7 P8 P9 BYTES Ggot Gcan.
assert (SOK : store_ok asegs m' (Z_to_bv 64 (bv_unsigned sp - 144)) 144 = true).
{ apply store_ok_of_wr_at. destruct ST' as (S1 & S2 & S3). destruct FR' as [[_ _] FW].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases (bv_unsigned sp - 144 + i) (bv_unsigned sp - 16)) as [Hl|Hg].
- apply (proj1 (S3 (bv_unsigned sp - 144 + i) ltac:(lia))).
- destruct FW as (_ & _ & FW3). replace (bv_unsigned sp - 144 + i) with (bv_unsigned sp - 16 + (i - 128)) by lia.
apply FW3. cbn [cells_size csize Nat.add] . lia. }
apply evt_done.
replace (Z_to_bv 64 864176 : word) with (864176%bv : word) by (apply bv_eq; reflexivity).
lazymatch goal with |- AJ _ _ _ (MS ?R _ _ _ _ _ _) =>
apply (stdio_exit_flush_A (fF:=F) (fC:=fc) J (SYS F fc) R m' md sp a0 wp2 rp2 wp0 rp0 wb wp bufp bufsz rp1 can pending);
[ reflexivity | reflexivity | reflexivity | lia | exact SPHI | exact SOK | exact SG' | exact FC0' | exact FC2' | exact SP' | exact HCK ]
end.
Qed.
End ExitA.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Q1jK QxOv Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import QZsi.
Import Q1jK Qujl.Mq2 QxOv QCKW.Mq7 Qr6U QCKW.Mq8.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 QRjH.Mq3 Q9ox.Mq0 QBxa.Mq5.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq4 QlKV.Mqi.
Import QGm2 QbKA QjDJ QrJ1 Qlna Qirj QMjx Qujl.Mq4.

Import QCKW.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section ExitA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @Qfub.aj_sys F fc asegs J.

Lemma rdn_munch : forall W m m' (a : word) n bs,
rdn asegs m a n = Some bs -> munch W m m' -> disjoint_from W (bv_unsigned a) (Z.of_nat n) ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn asegs m' a n = Some bs.
Proof.
intros W m m' a n bs Hr MU DJ Hnw. rewrite (rdn_ext asegs n m' m a Hnw); [exact Hr|].
intros x Hx. apply MU. eapply disjoint_outside; [exact DJ | lia].
Qed.

Lemma store_ok_of_wr_at : forall m a n, wr_at asegs m a (Z.of_nat n) -> store_ok asegs m (Z_to_bv 64 a) n = true.
Proof.
intros m a n (Ha & Hn & Hw).
assert (G : forall k i, (Z.of_nat k + Z.of_nat i = Z.of_nat n)%Z -> store_ok asegs m (Z_to_bv 64 (a + Z.of_nat k)) i = true).
{ intros k i. revert k. induction i as [|i IH]; intros k Hk; [reflexivity|].
cbn [store_ok]. unfold wa in Hw.
destruct (wview asegs m (Z_to_bv 64 (a + Z.of_nat k))) eqn:E.
- replace (Z_to_bv 64 (a + Z.of_nat k) + 1)%bv with (Z_to_bv 64 (a + Z.of_nat (S k))).
+ apply (IH (S k)). lia.
+ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned (1 : word)) with 1%Z.
rewrite Zplus_mod_idemp_l. f_equal. lia.
- exfalso. apply (Hw (Z.of_nat k)); [lia | exact E]. }
replace a with (a + Z.of_nat 0)%Z by lia. apply (G 0%nat n). lia.
Qed.

Ltac wlit := rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Theorem exit_clean_A :
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) (wp1 rp1 wp2 rp2 wp0 rp0 : word),
CK J md ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 0x800000000000 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
stdio_globalsA m -> file_clean m 0xecf20 wp0 rp0 -> file_clean m 0xece30 wp1 rp1 -> file_clean m 0xecd40 wp2 rp2 ->
AJ J (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs (cfg_model md))) md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced74) fc None m (seg_rom asegs)).
Proof.
intros until rp0. intros HCK MI ST CEIL LO AL SPHI XC SG FC0 FC1 FC2.
apply (aj_evt J).
eapply (exit_entry_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ lo tid g0 g1 g5 g6 g7 dso ob junkM mid
MI ST CEIL LO AL XC).
intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' FR'.

Ltac djW := unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; cbn [disjoint_from];
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac xfer K MU := eapply rdn_munch in K; [| exact MU | djW | wlit].
destruct SG as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (SG' : stdio_globalsA m') by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC0 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC0' : file_clean m' 0xecf20 wp0 rp0) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC1 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC1' : file_clean m' 0xece30 wp1 rp1) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC2 as (K1 & K2 & K3 & K4 & K5). xfer K1 MU. xfer K2 MU. xfer K3 MU. xfer K4 MU. xfer K5 MU.
assert (FC2' : file_clean m' 0xecd40 wp2 rp2) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.

assert (SOK : store_ok asegs m' (Z_to_bv 64 (bv_unsigned sp - 144)) 144 = true).
{ apply store_ok_of_wr_at. destruct ST' as (S1 & S2 & S3). destruct FR' as [[_ _] FW].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases (bv_unsigned sp - 144 + i) (bv_unsigned sp - 16)) as [Hl|Hg].
- apply (proj1 (S3 (bv_unsigned sp - 144 + i) ltac:(lia))).
- destruct FW as (_ & _ & FW3). replace (bv_unsigned sp - 144 + i) with (bv_unsigned sp - 16 + (i - 128)) by lia.
apply FW3. cbn [cells_size csize Nat.add] . lia. }

lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
destruct (w3a (fF:=F) (fC:=fc) R m' (seg_rom asegs) sp a0 wp1 rp1 wp2 rp2 wp0 rp0) as (regs3 & RUN & R3a0 & R3a7 & R3sp);
[ reflexivity | reflexivity | reflexivity | lia | exact SPHI | exact SOK | exact SG' | exact FC0' | exact FC1' | exact FC2' | ]
end.
replace (Z_to_bv 64 874100 : word) with (874100%bv : word) by (apply bv_eq; reflexivity).
lazymatch type of RUN with QsRG.msteps _ ?x ?y =>
apply (evt_cut asegs (eq y)); [exists y; split; [apply msteps_of_ascatsim; exact RUN | reflexivity] |] end.
intros ms3 <-.

apply evt_done.
eapply (AJ_exit_at asegs J (SYS F fc)); [exact F_ceb98 | exact E_ceb98 | exact HCK | right; exact R3a7 | exact R3a0].
Qed.

Theorem exit_flush_A :
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) (wp2 rp2 wp0 rp0 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
CK J md ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp <= 0x800000000000 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
stdio_globalsA m -> file_clean m 0xecf20 wp0 rp0 -> file_clean m 0xecd40 wp2 rp2 -> stdout_pending m wb wp bufp bufsz rp1 can pending ->
AJ J (t_emit (QBxa.Mq5.W 1 pending) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs (cfg_model md)))) md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced74) fc None m (seg_rom asegs)).
Proof.
intros until pending. intros HCK MI ST CEIL LO AL SPHI XC SG FC0 FC2 SP.
apply (aj_evt J).
eapply (exit_entry_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ lo tid g0 g1 g5 g6 g7 dso ob junkM mid
MI ST CEIL LO AL XC).
intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' FR'.
Ltac djW2 := unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; cbn [disjoint_from];
rewrite ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64)%Z; rewrite ?Z.mod_small by lia;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac xfer2 K MU := eapply rdn_munch in K; [| exact MU | djW2 | wlit].
destruct SG as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (SG' : stdio_globalsA m') by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC0 as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (FC0' : file_clean m' 0xecf20 wp0 rp0) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct FC2 as (K1 & K2 & K3 & K4 & K5). xfer2 K1 MU. xfer2 K2 MU. xfer2 K3 MU. xfer2 K4 MU. xfer2 K5 MU.
assert (FC2' : file_clean m' 0xecd40 wp2 rp2) by (split; [exact K1 | split; [exact K2 | split; [exact K3 | split; [exact K4 | exact K5]]]]).
clear K1 K2 K3 K4 K5.
destruct SP as [P1 P2 P3 P4 P5 P6 P7 P8 P9 RANGE LEN PMAX BYTES [Ggot Gcan]].
pose proof (u64_range can) as CANR.
xfer2 P1 MU. xfer2 P2 MU. xfer2 P3 MU. xfer2 P4 MU. xfer2 P5 MU. xfer2 P6 MU. xfer2 P7 MU. xfer2 P8 MU. xfer2 P9 MU.
eapply rdn_munch in BYTES; [| exact MU | djW2 | rewrite unsigned_lit by lia; lia].
xfer2 Ggot MU. xfer2 Gcan MU.
assert (SP' : stdout_pending m' wb wp bufp bufsz rp1 can pending).
{ constructor; try assumption. split; assumption. }
clear P1 P2 P3 P4 P5 P6 P7 P8 P9 BYTES Ggot Gcan.
assert (SOK : store_ok asegs m' (Z_to_bv 64 (bv_unsigned sp - 144)) 144 = true).
{ apply store_ok_of_wr_at. destruct ST' as (S1 & S2 & S3). destruct FR' as [[_ _] FW].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases (bv_unsigned sp - 144 + i) (bv_unsigned sp - 16)) as [Hl|Hg].
- apply (proj1 (S3 (bv_unsigned sp - 144 + i) ltac:(lia))).
- destruct FW as (_ & _ & FW3). replace (bv_unsigned sp - 144 + i) with (bv_unsigned sp - 16 + (i - 128)) by lia.
apply FW3. cbn [cells_size csize Nat.add] . lia. }
apply evt_done.
replace (Z_to_bv 64 874100 : word) with (874100%bv : word) by (apply bv_eq; reflexivity).
lazymatch goal with |- AJ _ _ _ (MS ?R _ _ _ _ _ _) =>
apply (stdio_exit_flush_A (fF:=F) (fC:=fc) J (SYS F fc) R m' md sp a0 wp2 rp2 wp0 rp0 wb wp bufp bufsz rp1 can pending);
[ reflexivity | reflexivity | reflexivity | lia | exact SPHI | exact SOK | exact SG' | exact FC0' | exact FC2' | exact SP' | exact HCK ]
end.
Qed.
End ExitA.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1jK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrJ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrJ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlna.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlna. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMjx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMjx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Definition MAIN_A : Z := 0x919d0.
Definition RA_MAIN : Z := 0xce674.
Definition A_GP : Z := 0x10800.
Definition TRUN_A : Z := 0x91ca0.
Definition EMITPF_A : Z := 0x91e28.
Definition TARGET_A : Z := 0x91e70.
Definition ADAPTER_FLAG : Z := 0x624810.
Definition EMPTY_A : Z := 0x624820.
Definition GOT_STDERR : Z := 0xe8e20.
Definition STDERR_P : Z := 0xe80b0.
Definition GOT_LLVMINIT : Z := 0xe8e28.
Definition F_STDERR : Z := 0xecd40.
Definition F_STDOUT : Z := 0xece30.
Definition STDOUT_BUF : Z := 0x645ca8.
Definition OPEN_A : Z := 0xcefe8.
Definition CLOSE_A : Z := 0xe3854.
Definition EXIT_A : Z := 0xced74.
Definition T_GLOBLOC_A : Z := 0x6457e8.
Definition T_LOCCELL_A : Z := A_TP - 48.
Definition T_LOCALE_LOCK_A : Z := 0x645890.

Definition pristine (m : word -> option byte) (lo hi : Z) : Prop := forall a, lo <= a < hi -> m (wa a) = None.

Definition RTC_R : list (Z * list byte) :=
[ (0xe8e20, le8 (Z_to_bv 64 0xe80b0));
(0xe80b0, le8 (Z_to_bv 64 0xecd40));
(0xe8e28, le8 (Z_to_bv 64 0x0));
(0xea078, le8 (Z_to_bv 64 0xe3934));
(0xe8fc0, le8 (Z_to_bv 64 0xe4ac8) ++ le8 (Z_to_bv 64 0xe4ab8));
(0xe4ab8, le8 (Z_to_bv 64 0x9b3cc) ++ le8 (Z_to_bv 64 0x3e10c));
(0xe8188, le8 (Z_to_bv 64 0xcec58) ++ le8 (Z_to_bv 64 0x0));
(0xea020, le8 (Z_to_bv 64 0xea020));
(0xe8198, le8 (Z_to_bv 64 0x181c60) ++ le8 (Z_to_bv 64 0xea208) ++ le8 (Z_to_bv 64 0x183ce8) ++ le8 (Z_to_bv 64 0xef9b8) ++ le8 (Z_to_bv 64 0xf21b8) ++ le8 (Z_to_bv 64 0xf2ea8) ++ le8 (Z_to_bv 64 0xf2eb0) ++ le8 (Z_to_bv 64 0xf2ea0) ++ le8 (Z_to_bv 64 0xea1d0));
(0xe8ec0, le8 (Z_to_bv 64 0xed040) ++ le8 (Z_to_bv 64 0xeeb00)) ].
Definition rtc_R (m : word -> option byte) : Prop := Forall (fun c => bytes_at asegs m (fst c) (snd c)) RTC_R.

Definition PRIS_A : list (Z * Z) :=
[ (0xec920, 0xec980);
(0xeccf8, 0xecd40);
(0xece28, 0xece30);
(0xecf18, 0xed020);
(0xed028, 0xed040);
(0xed040, 0xeeb00);
(0xeeb10, 0xeeb58);
(0x184060, 0x184068);
(0x624840, 0x624848);
(0x624880, 0x624884);
(0x6456a0, 0x6457a0);
(0x645820, 0x6458a0);
(0x645c48, 0x645ca0) ].

Definition pris_A (m : word -> option byte) : Prop := Forall (fun iv => pristine m (fst iv) (snd iv)) PRIS_A.

Definition STDIO0_A : list (Z * Z) := [ (0xecd40, 0xece28); (0xece30, 0xecf18); (0x645ca0, 0x6460b0); (0x624810, 0x624840) ].
Definition stdio0 (m : word -> option byte) : Prop := Forall (fun iv => pristine m (fst iv) (snd iv)) STDIO0_A.

Definition argstr (m : word -> option byte) (USP p : Z) (s : list byte) : Prop :=
bytes_at asegs m p (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ USP + 24 <= p /\ (p + Z.of_nat (length s) + 1 + 8 <= USP + 2^22 - 4096 /\ (Z.of_nat (length s) < 2^17 /\ p + Z.of_nat (length s) + 1 + 8 <= 2^47))
/\ (exists t, bytes_at asegs m (p + Z.of_nat (length s) + 1) t /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length t)).

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Record drvA_mem (argv : list (list byte)) (USP : Z) (m : word -> option byte) : Prop := DMA {
dm_mi     : mem_inv asegs m;

dm_argc   : 1 <= Z.of_nat (length argv) <= 1024;
dm_arg0   : exists p0, ro_cells asegs m (USP + 8) [C8 (Z_to_bv 64 p0)] /\ argstr m USP p0 (nth 0 argv []);
dm_arg1   : (2 <= length argv)%nat -> exists p1, ro_cells asegs m (USP + 16) [C8 (Z_to_bv 64 p1)] /\ argstr m USP p1 (nth 1 argv []);

dm_pris   : pris_A m;

dm_tid    : exists tid, ro_cells asegs m (A_TP - 168) [C4 (Z_to_bv 64 tid)] /\ 0 < tid < 2^31;
dm_loc    : rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)];

dm_atexit : exists mid, rw_cells asegs m ATEXIT_A (atexit_cells m mid) /\ length mid = 240%nat
}.

Record drvA_pre (argv : list (list byte)) (USP LO : Z) (m : word -> option byte) (md : Model) : Prop := DPA {

dp_usp    : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47;
dp_lo     : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48;
dp_stk    : stk asegs m LO (USP - 48);

dp_fd1    : fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
dp_fd2    : fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
dp_fd3    : alloc_fd (m_fds md) = Z_to_bv 64 3 /\ fd_lookup (m_fds md) (Z_to_bv 64 3) = None;
dp_mem    : drvA_mem argv USP m;

dp_stdio0 : stdio0 m
}.

Section TargetA.
Variable HIx : heap_iface_A A4L.

Variable GA : (word -> option byte) -> Prop.

Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Notation HEAPAx := (HEAPA A4L HIx).

Definition xtgt_A (SP : Z) (a : Z) : Prop :=
a4_volatile a \/ (T_LOCCELL_A <= a < T_LOCCELL_A + 8) \/ (A_SB + alloc_ceiling / 8 <= a <= A_SB + SP / 8).

Definition target_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (B : bud) (data size lo : Z) (payload : list byte) (errv : word),
HEAPAx A LB LM [] B m md ->
TGT_BB_A <= bB B -> TGT_BD_A <= bD B ->

bytes_at asegs m data payload -> Z.of_nat (length payload) = size ->
0 <= size < 2^26 -> 0 < data -> data + size <= alloc_ceiling ->
(size = 0 \/ In (data, size) LB) ->
Z.of_nat (length LM) < 8 ->

rw_cells asegs m T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] ->
rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
GA m ->

stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> hiA_bot A4L HIx <= lo ->
lo <= bv_unsigned sp - TGT_STACK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 32 <= hiA_top A4L HIx ->
bv_unsigned s0 < 2^26 ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> ra = Z_to_bv 64 0x91d6c ->
frm0 fc ->
a0 = Z_to_bv 64 data -> a1 = Z_to_bv 64 size ->
(forall ms' m' md' (A' : ASA A4L HIx) (B' : bud) (errv' gp' : word) (LK : list blk),
ret_statew A4H ra sp gp' tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_presx A4H (xtgt_A (bv_unsigned sp)) (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] ->
rw_cells asegs m' T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m' (A_TP - 164) [C4 errv'] ->
GA m' ->
HEAPAx A' (LB ++ LK) LM [] B' m' md' ->
bB B - TGT_BB_A <= bB B' -> bD B - TGT_BD_A <= bD B' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TARGET_A) fc None m (seg_rom asegs)).
End TargetA.

Section DriverA.
Variable HIx : heap_iface_A A4L.

Definition DRVA_BB (TGT_BB_A : Z) : Z := 2^32 + 4 * TGT_BB_A.
Definition DRVA_BD (TGT_BD_A : Z) : Z := 64 + 4 * TGT_BD_A.

Definition driver_A_stmt (GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A0 : ASA A4L HIx) (LM0 : list blk) (B0 : bud) (argv : list (list byte)) (USP LO : Z),
valid_argv argv ->
drvA_pre argv USP LO m (cfg_model md) ->
HEAPA A4L HIx A0 [] LM0 [] B0 m md ->
DRVA_BB TGT_BB_A <= bB B0 -> DRVA_BD TGT_BD_A <= bD B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 0 <= TGT_BD_A ->
USP <= hiA_top A4L HIx + 160 -> hiA_bot A4L HIx <= LO ->
ra = Z_to_bv 64 RA_MAIN -> sp = Z_to_bv 64 (USP - 48) -> gp = Z_to_bv 64 A_GP -> tp = Z_to_bv 64 A_TP ->
a0 = Z_to_bv 64 (Z.of_nat (length argv)) -> a1 = Z_to_bv 64 (USP + 8) ->
frm0 fc ->
AJ5 A4L HIx A0 (spec argv (m_fs (cfg_model md))) md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 MAIN_A) fc None m (seg_rom asegs)).
End DriverA.

Lemma aj5_conseq : forall (HIx : heap_iface_A A4L) (A : ASA A4L HIx) T T' c ms,
AJ5 A4L HIx A T c ms -> t_eq T T' -> AJ5 A4L HIx A T' c ms.
Proof. intros HIx A T T' c ms K E G. exact (aj_conseq (hiA_J A4L HIx) T T' c ms (K G) E). Qed.
End RC__1.
