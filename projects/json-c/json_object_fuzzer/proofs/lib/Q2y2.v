(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS67.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS67.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrJ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrJ1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlna.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlna.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMjx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMjx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Definition MAIN_A : Z := 0x915f8.
Definition RA_MAIN : Z := 0xcbfb0.
Definition A_GP : Z := 0x10800.
Definition TRUN_A : Z := 0x918c8.
Definition EMITPF_A : Z := 0x91a50.
Definition TARGET_A : Z := 0x91a98.
Definition ADAPTER_FLAG : Z := 0x622150.
Definition EMPTY_A : Z := 0x622160.
Definition GOT_STDERR : Z := 0xe6a20.
Definition STDERR_P : Z := 0xe5cb0.
Definition GOT_LLVMINIT : Z := 0xe6a28.
Definition F_STDERR : Z := 0xea660.
Definition F_STDOUT : Z := 0xea750.
Definition STDOUT_BUF : Z := 0x6435e8.
Definition OPEN_A : Z := 0xcc924.
Definition CLOSE_A : Z := 0xe1190.
Definition EXIT_A : Z := 0xcc6b0.
Definition T_GLOBLOC_A : Z := 0x643128.
Definition T_LOCCELL_A : Z := A_TP - 48.
Definition T_LOCALE_LOCK_A : Z := 0x6431d0.

Definition pristine (m : word -> option byte) (lo hi : Z) : Prop := forall a, lo <= a < hi -> m (wa a) = None.

Definition RTC_R : list (Z * list byte) :=
[ (0xe6a20, le8 (Z_to_bv 64 0xe5cb0));
(0xe5cb0, le8 (Z_to_bv 64 0xea660));
(0xe6a28, le8 (Z_to_bv 64 0x0));
(0xe7c58, le8 (Z_to_bv 64 0xe1270));
(0xe6bb0, le8 (Z_to_bv 64 0xe2400) ++ le8 (Z_to_bv 64 0xe23f0));
(0xe23f0, le8 (Z_to_bv 64 0x99f88) ++ le8 (Z_to_bv 64 0x3dee0));
(0xe5d88, le8 (Z_to_bv 64 0xcc594) ++ le8 (Z_to_bv 64 0x0));
(0xe7c00, le8 (Z_to_bv 64 0xe7c00));
(0xe5d98, le8 (Z_to_bv 64 0x17f5a0) ++ le8 (Z_to_bv 64 0xe7de8) ++ le8 (Z_to_bv 64 0x181628) ++ le8 (Z_to_bv 64 0xed2f8) ++ le8 (Z_to_bv 64 0xefaf8) ++ le8 (Z_to_bv 64 0xf07e8) ++ le8 (Z_to_bv 64 0xf07f0) ++ le8 (Z_to_bv 64 0xf07e0) ++ le8 (Z_to_bv 64 0xe7db0));
(0xe6ab0, le8 (Z_to_bv 64 0xea960) ++ le8 (Z_to_bv 64 0xec420)) ].
Definition rtc_R (m : word -> option byte) : Prop := Forall (fun c => bytes_at asegs m (fst c) (snd c)) RTC_R.

Definition PRIS_A : list (Z * Z) :=
[ (0xea500, 0xea560);
(0xea618, 0xea660);
(0xea748, 0xea750);
(0xea838, 0xea940);
(0xea948, 0xea960);
(0xea960, 0xec420);
(0xec450, 0xec498);
(0x1819a0, 0x1819a8);
(0x622180, 0x622188);
(0x6221c0, 0x6221c4);
(0x642fe0, 0x6430e0);
(0x643160, 0x6431e0);
(0x643588, 0x6435e0) ].

Definition pris_A (m : word -> option byte) : Prop := Forall (fun iv => pristine m (fst iv) (snd iv)) PRIS_A.

Definition STDIO0_A : list (Z * Z) := [ (0xea660, 0xea748); (0xea750, 0xea838); (0x6435e0, 0x6439f0); (0x622150, 0x622180) ].
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
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> ra = Z_to_bv 64 0x91994 ->
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
