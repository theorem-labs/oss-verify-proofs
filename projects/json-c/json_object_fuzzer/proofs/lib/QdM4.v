(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD Qhd4 QsRG QRjH QBxa QMz4 QXup QHnV QCcH QfLs Qsw7 QJjn Qwm6 QlKV QZsi Q0TL QS67 QCKW Q2y2 QdZp Qu3b Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4.
Import QsRG.Mq0 QRjH QBxa.Mq5 QMz4.
Import QXup.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mqa.
Import QZsi.
Import Q0TL QS67 QCKW.Mq1.
Import Q2y2.

Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.

Definition VPRINTF_V : Z := 0x4f98c.
Definition FPRINTF_V : Z := 0x4f998.
Definition FWRITE_V : Z := 0x4f980.
Definition FMT_D : Z := 0x14e05.
Definition FMT_USAGE : Z := 0x1610a.
Definition FMT_CANNOT : Z := 0x1edde.
Definition FMT_READERR : Z := 0x1edf3.
Definition FMT_REFUSED : Z := 0x1a7dd.
Definition MSG_SHORT : Z := 0x2145e.
Definition MSG_OVERRUN : Z := 0x1611b.
Definition MSG_OOM : Z := 0x14df1.

Definition PF_STACK_A : Z := 8192.

Definition PFW_OUT (lo sp : Z) : list (Z * Z) := [(lo, sp); (F_STDOUT, F_STDOUT + 232); (STDOUT_BUF, STDOUT_BUF + 1024)].
Definition PFW_ERR (lo sp : Z) : list (Z * Z) := [(lo, sp); (F_STDERR, F_STDERR + 232)].

Definition STDIO_WRITE_A : Z := 0xd29d0.

Definition STDOUT0_A (m : word -> option byte) : Prop := pristine m F_STDOUT (F_STDOUT + 232) /\ pristine m 0x6435e0 0x6439f0.

Definition STDERR0_A (m : word -> option byte) : Prop := pristine m F_STDERR (F_STDERR + 232).

Definition STDERRC_A (m : word -> option byte) : Prop := exists wp rp : word, file_clean m F_STDERR wp rp.

Fixpoint zl (k : nat) : list Z := match k with O => [] | S k' => 48 :: 10 :: zl k' end.
Definition so_w (k : nat) : QdZp.stdout_st :=
QdZp.mkStdout true (zl (Nat.pred k)) false false.
Definition STDOUTW_A (m : word -> option byte) (k : nat) : Prop := Qu3b.Mq0.stdout_file m (so_w k).

Definition PFIMG_A (m : word -> option byte) : Prop :=
pris_A m /\ rtc_R m
/\ (exists g : word, bytes_at asegs m 0xe6b80 (le8 (Z_to_bv 64 0x642ea0)) /\ bytes_at asegs m 0x642ea0 (le8 g) /\ bytes_at asegs m (A_TP - 16) (le8 g))
/\ bytes_at asegs m 0x6430f3 [Z_to_bv 8 0].

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.

Definition emitpf1_stmt : Prop :=
forall (sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
STDOUT0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc ->
K [] ->
(forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_OUT lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDOUTW_A m' 1%nat -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra' sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x919a4) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 1 (zero_lines 1)) K) cf
(MS (mkR (Z_to_bv 64 0x919a4) sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 EMITPF_A) fc None m (seg_rom asegs)).

Definition emitpfk_stmt : Prop :=
forall (k : nat) (sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf -> (1 <= k <= 3)%nat ->
STDOUTW_A m k -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc ->
K [] ->
(forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_OUT lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDOUTW_A m' (S k) -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra' sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x919a4) fc' None m' (seg_rom asegs))) ->
AJ J K cf
(MS (mkR (Z_to_bv 64 0x919a4) sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 EMITPF_A) fc None m (seg_rom asegs)).

Definition fmt_s_msg (fmt : Z) (str : list byte) : list byte :=
if Z.eqb fmt FMT_USAGE then msg_usage str
else if Z.eqb fmt FMT_CANNOT then msg_cannot_open str
else msg_read_error str.

Definition fprintf_s_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo fmt p : Z) (str slack : list byte),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(fmt = FMT_USAGE \/ fmt = FMT_CANNOT \/ fmt = FMT_READERR) ->
a0 = Z_to_bv 64 F_STDERR -> a1 = Z_to_bv 64 fmt -> a2 = Z_to_bv 64 p ->
bytes_at asegs m p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
(- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2^17 ->
unpoisoned asegs m A_SB p (Z.of_nat (length str) + 1) -> 0 <= p -> bv_unsigned sp <= p ->
p + Z.of_nat (length str) + 9 <= 2^47 ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 (fmt_s_msg fmt str)) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FPRINTF_V) fc None m (seg_rom asegs)).

Definition fprintf_u_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
a0 = Z_to_bv 64 F_STDERR -> a1 = Z_to_bv 64 FMT_REFUSED -> a2 = Z_to_bv 64 67108864 ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 msg_refused) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FPRINTF_V) fc None m (seg_rom asegs)).

Definition fwrite_msg (msg : Z) : list byte :=
if Z.eqb msg MSG_SHORT then msg_short else if Z.eqb msg MSG_OVERRUN then msg_overrun else msg_oom.

Definition fwrite_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo msg : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(msg = MSG_SHORT \/ msg = MSG_OVERRUN \/ msg = MSG_OOM) ->
a0 = Z_to_bv 64 msg -> a1 = Z_to_bv 64 (Z.of_nat (length (fwrite_msg msg))) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 F_STDERR ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
(forall g, msg / 8 <= g <= (msg + 31) / 8 -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 (fwrite_msg msg)) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FWRITE_V) fc None m (seg_rom asegs)).
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD.
Import QXup.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QBpc.

Import Qhd4.
Import Qwm6.Mq0.
Import Q2y2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Lemma pristine_sub : forall m lo hi lo' hi', pristine m lo hi -> lo <= lo' -> hi' <= hi -> pristine m lo' hi'.
Proof. intros m lo hi lo' hi' P H1 H2 a Ha. apply P. lia. Qed.

Lemma pris_A_in : forall m lo hi, pris_A m -> In (lo, hi) PRIS_A -> pristine m lo hi.
Proof. intros m lo hi P Hin. unfold pris_A in P. exact (proj1 (Forall_forall _ _) P (lo, hi) Hin). Qed.

Lemma rtc_R_in : forall m a bs, rtc_R m -> In (a, bs) RTC_R -> bytes_at asegs m a bs.
Proof. intros m a bs P Hin. unfold rtc_R in P. exact (proj1 (Forall_forall _ _) P (a, bs) Hin). Qed.
Lemma ro_of_bytes : forall m a cs, cells_wf cs -> bytes_at asegs m a (cells_bytes cs) -> ro_cells asegs m a cs.
Proof. intros m a cs WF B. split; [exact WF | exact B]. Qed.
Ltac rtcR_cell P a bs := apply ro_of_bytes; [cbn; tauto | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; exact (rtc_R_in _ a bs P ltac:(unfold RTC_R; cbn [In]; tauto))].

Ltac pris_get P lo hi :=
let Hf := fresh "PR" in
assert (Hf : pristine _ lo hi) by (apply (pris_A_in _ lo hi P); unfold PRIS_A; cbn [In]; tauto).

Section PrisR.
Context {RC__ : Q6q3.RunConsts}.

Lemma rtc_R_of_HEAPA : forall (HIx : heap_iface_A A4L) A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> rtc_R m.
Proof.
intros HIx A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as RT. cbn [hl_rt_consts A4L] in RT. unfold a4_rt_consts in RT.
unfold rtc_R, RTC_R. rewrite Forall_forall in RT. repeat (apply Forall_cons; [apply RT; cbn [In]; repeat (try (left; reflexivity); right)|]). apply Forall_nil.
Qed.
End PrisR.

Lemma rw_cells_pristine : forall (m : word -> option byte) A bs,
pristine m A (A + Z.of_nat (length bs)) ->
rw_bytes_b asegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
rw_cells asegs m A [CB (length bs) bs].
Proof.
intros m A bs P Hb HA Hhi. apply rw_cells_image0; [| exact Hb | exact HA | exact Hhi].
intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply P. exact Ha.
Qed.

Lemma rw_cells_pristine_recast : forall (m : word -> option byte) A bs cs,
pristine m A (A + Z.of_nat (length bs)) ->
rw_bytes_b asegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs ->
rw_cells asegs m A cs.
Proof.
intros m A bs cs P Hb HA Hhi WF E1 E2.
apply (rw_cells_recast asegs m A [CB (length bs) bs] cs); [| exact WF | cbn; rewrite app_nil_r; exact E1 | cbn; rewrite Nat.add_0_r; exact E2].
apply rw_cells_pristine; assumption.
Qed.

Lemma ro_of_rw : forall m A cs, rw_cells asegs m A cs -> ro_cells asegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Fixpoint img_rw_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom asegs (wa A), wview asegs (fun _ => None) (wa A) with
| Some _, Some _ => img_rw_b (A + 1) n'
| _, _ => false
end
end.

Lemma wview_of_empty : forall m (a : word), wview asegs (fun _ => None) a <> None -> wview asegs m a <> None.
Proof. intros m a H. unfold wview in *. destruct (m a); [discriminate | exact H]. Qed.

Lemma img_rw_b_sound : forall n A m, img_rw_b A n = true ->
forall i, 0 <= i < Z.of_nat n -> (exists b, mrd asegs m (wa (A + i)) = Some b) /\ wview asegs m (wa (A + i)) <> None.
Proof.
induction n as [|n IH]; intros A m Hb i Hi; [lia|].
cbn [img_rw_b] in Hb.
destruct (seg_rom asegs (wa A)) as [b0|] eqn:Er; [|discriminate].
destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. split.
+ unfold mrd. destruct (m (wa A)) as [b|]; [exists b; reflexivity | exists b0; exact Er].
+ apply wview_of_empty. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) m Hb). lia.
Qed.

Lemma img_rw_any : forall A n m, img_rw_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
exists junk, rw_cells asegs m A [CB n junk].
Proof.
intros A n m Hb HA Hhi.
pose proof (img_rw_b_sound n A m Hb) as G.
assert (EX : exists junk, length junk = n /\ forall i, (i < n)%nat -> mrd asegs m (wa (A + Z.of_nat i)) = nth_error junk i).
{ clear HA Hhi Hb. revert A G. induction n as [|n IH]; intros A G.
- exists []. split; [reflexivity | intros i Hi; lia].
- destruct (IH (A + 1) ltac:(intros i Hi; replace (A + 1 + i) with (A + (i + 1)) by lia; apply G; lia)) as (junk & Hl & Hj).
destruct (proj1 (G 0 ltac:(lia))) as (b & Hb0). rewrite Z.add_0_r in Hb0.
exists (b :: junk). split; [cbn; lia|]. intros [|i] Hi; cbn [nth_error].
+ rewrite Z.add_0_r. exact Hb0.
+ replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply Hj. lia. }
destruct EX as (junk & Hl & Hj). exists junk.
split; [split|].
- cbn. rewrite Hl. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hj. lia.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply (proj2 (G i Hi)).
Qed.

Lemma rw_of_ro_img : forall m A cs, ro_cells asegs m A cs -> img_rw_b A (cells_size cs) = true -> rw_cells asegs m A cs.
Proof.
intros m A cs RO Hb. split; [exact RO|]. destruct RO as [Hwf (HA & Hhi & _)].
rewrite (cells_bytes_length cs Hwf) in Hhi.
split; [exact HA|]. split; [exact Hhi|].
intros i Hi. apply (proj2 (img_rw_b_sound _ A m Hb i Hi)).
Qed.

Lemma find_segment_high_A : forall z n, 1 <= n -> 0x645000 <= z -> find_segment asegs z n = None.
Proof.
intros z n Hn Hz. apply QBpc.find_segment_high; [exact Hn|].
assert (E : segs_top asegs <= 0x645000) by (vm_compute; discriminate). lia.
Qed.

Lemma mrd_high_overlay : forall m (a : word) b, 0x645000 <= bv_unsigned a -> mrd asegs m a = Some b -> m a = Some b.
Proof.
intros m a b Ha H. unfold mrd in H. destruct (m a) as [b'|]; [exact H|].
unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1%Z in H. rewrite (find_segment_high_A (bv_unsigned a) 1 ltac:(lia) Ha) in H. discriminate.
Qed.

Lemma wr_at_of_bytes_at_high : forall m A bs, bytes_at asegs m A bs -> 0x645000 <= A -> wr_at asegs m A (Z.of_nat (length bs)).
Proof.
intros m A bs (HA & Hhi & Hb) Hlo. split; [exact HA|]. split; [exact Hhi|].
intros i Hi.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. rewrite E in Hb.
pose proof (mrd_high_overlay m (wa (A + i)) b ltac:(rewrite wa_unsigned by lia; lia) Hb) as Hm.
unfold wview. rewrite Hm. discriminate.
Qed.

Lemma rw_of_ro_high : forall m A cs, ro_cells asegs m A cs -> 0x645000 <= A -> rw_cells asegs m A cs.
Proof.
intros m A cs RO Hlo. split; [exact RO|]. destruct RO as [Hwf Hb].
rewrite <- (cells_bytes_length cs Hwf). apply wr_at_of_bytes_at_high; [exact Hb | exact Hlo].
Qed.

Definition in_ivs (L : list (Z * Z)) (x : Z) : Prop := Exists (fun iv => fst iv <= x < snd iv) L.

Lemma prisl_agree : forall (L : list (Z * Z)) (m m' : word -> option byte),
Forall (fun iv => pristine m (fst iv) (snd iv)) L ->
Forall (fun iv => 0 <= fst iv /\ snd iv <= 2^64) L ->
(forall x, 0 <= x < 2^64 -> in_ivs L x -> m' (wa x) = m (wa x)) ->
Forall (fun iv => pristine m' (fst iv) (snd iv)) L.
Proof.
intros L m m' P R E. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) P _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
pose proof (proj1 (Forall_forall _ _) R _ IN) as [R1 R2]. cbn [fst snd] in R1, R2.
apply E; [lia|]. unfold in_ivs. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
Qed.

Lemma stdio0_agree : forall m m', stdio0 m -> (forall x, 0 <= x < 2^64 -> in_ivs STDIO0_A x -> m' (wa x) = m (wa x)) -> stdio0 m'.
Proof.
intros m m' S E. unfold stdio0. apply (prisl_agree STDIO0_A m m' S); [| exact E].
unfold STDIO0_A. repeat constructor; cbn; lia.
Qed.

Lemma in_stdio0_cases : forall x, in_ivs STDIO0_A x -> 0xea660 <= x < 0xea748 \/ 0xea750 <= x < 0xea838 \/ 0x6435e0 <= x < 0x6439f0 \/ 0x622150 <= x < 0x622180.
Proof.
intros x Hx. unfold in_ivs, STDIO0_A in Hx.
repeat (apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx; lia|]). apply Exists_nil in Hx. destruct Hx.
Qed.

Lemma stdio0_munch : forall m m' W, stdio0 m -> munch W m m' ->
Forall (fun iv => snd iv <= 0xea660 \/ (0xea748 <= fst iv /\ snd iv <= 0xea750) \/ (0xea838 <= fst iv /\ snd iv <= 0x622150) \/ (0x622180 <= fst iv /\ snd iv <= 0x6435e0) \/ 0x6439f0 <= fst iv) W ->
stdio0 m'.
Proof.
intros m m' W S MU FW. eapply stdio0_agree; [exact S|]. intros x Hx HI. apply MU. rewrite wa_unsigned by lia.
apply in_stdio0_cases in HI. clear - FW HI. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [H1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Definition drvA_memS (argv : list (list byte)) (USP : Z) (m : word -> option byte) : Prop := drvA_mem argv USP m /\ stdio0 m.
End Mq1.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei Open.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz QsV0 Qn1e Q9ox QSpR Lib.GwApply QWxq_c1 Qe4Y Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4.
Import QZsi.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import Q0TL QCKW.Mq0.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH QsV0 Qn1e QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mq8.
Import Qujl Q2y2.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition A_GUARD_GOT : Z := 0xe6b80.
Definition A_GUARD : Z := 0x642ea0.

Section DrvOpenA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Definition open_frame (junk16 : list byte) (g s1 s0 ra a2 a3 a4 a5 a6 a7 : word) : list cell :=
[CB 16 junk16; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma open_pre_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g : word) (lo : Z),
a1 = Z_to_bv 64 0 ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo ->
mem_inv asegs m ->
(forall m' junk16,
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp - 96) ->
rw_cells asegs m' (bv_unsigned sp - 96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcc9a4) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp a0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ECALL_PC) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> GG GV ST LO GLO MI HK.
unfold A_GUARD_GOT, A_GUARD, OPEN_A, ECALL_PC in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
carve_frame 96%nat ST.
do 4 step.
do 4 step.
do 2 step.
do 4 step.
step.
step. step.
step.
if_falsex.
do 3 step.

if_falsex.
step. step.
do 4 step.
do 3 step.
step.
step.
do 7 step.
eapply HK; [exact MU | exact WM | assumption | exact ST | exact FR].
Qed.

Lemma open_ret_ok_A :
forall (ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pth x2 x3 x4 x5 x6 x7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g : word) (lo r : Z) junk16,
0 <= r < 2^31 ->
ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp - 96) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo -> bv_unsigned sp < 2^64 ->
rw_cells asegs m (bv_unsigned sp - 96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcc9a4) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp pth t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(Z_to_bv 64 r) pth x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdc758) fc None m (seg_rom asegs)).
Proof.
intros until junk16. intros Hr GV ST LO GLO SPH FR MI RA HK.
unfold A_GUARD in *.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
step.
step. step. step.
if_truex.
step.
rewrite (unsigned_lit r) by lia. rewrite Z.add_0_r, (swrap32_id r) by lia.
step.
do 2 step.
step.
replace (bv_ltu (Z_to_bv 64 r) (Z_to_bv 64 (-4095))) with true
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
cbv iota.
step.
unfold open_frame in FR.
step. step.
step. if_falsex.
step.
rewrite (unsigned_lit r) by lia. rewrite Z.add_0_r, (swrap32_id r) by lia.
do 4 step.
step.
try (replace (bv_unsigned sp - 96 + 96) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
eapply HK; [exact MU | exact WM | exact MI | release_frame FR ST (bv_unsigned sp); exact ST].
Qed.

Lemma open_ret_err_A :
forall (ra sp gp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pth x2 x3 x4 x5 x6 x7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g errv : word) (lo e : Z) junk16,
1 <= e <= 4095 ->
ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp + -96) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo -> bv_unsigned sp < 2^64 ->
rw_cells asegs m (bv_unsigned sp + -96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(bv_unsigned sp + -112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
evt asegs Q (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcc9a4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) pth t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(errno_ret e) pth x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdc758) fc None m (seg_rom asegs)).
Proof.
intros until junk16. intros He GV ST LO GLO SPH FR ER MI RA HK.
unfold A_GUARD, A_TP in *. unfold open_frame in FR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
unfold errno_ret.
step.
step. step. step. if_truex.
step.
rewrite (unsigned_lit_wrap (- e)), Z.add_0_r.
replace ((- e) mod 2 ^ 64) with (- e + 4294967296 * 4294967296) by (Z.div_mod_to_equations; lia).
rewrite swrap32_shift, swrap32_id by lia.
step.
do 2 step.
step.
replace (bv_ltu (Z_to_bv 64 (- e)) (Z_to_bv 64 (-4095))) with false
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
cbv iota.
carve_frame 16%nat ST.
change (6434400 - 164) with 6434236 in ER.
step. stepz. stepz.
step.
step. do 3 step.
stepz.
replace (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- e)))) with e in *.
2: { rewrite unsigned_lit_wrap. replace (0 - (- e) mod 2 ^ 64) with (e + (- 4294967296) * 4294967296) by (Z.div_mod_to_equations; lia).
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
step.
do 3 step. step.
release_frame FR0 ST (bv_unsigned sp + -96).
step. step.
step. if_falsex.
step.
try match goal with |- context [bv_swrap 32 ?x] => replace (bv_swrap 32 x) with (-1) by (rewrite ?unsigned_lit_wrap; vm_compute; reflexivity) end.
do 4 step.
step.
try (replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
eapply HK; [exact MU | exact WM | exact MI | release_frame FR ST (bv_unsigned sp); exact ST | exact ER].
Qed.

Lemma open_file_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (TA TB : TSet)
(g errv : word) (pp lo : Z) (p d : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (length p <= 4095)%nat -> p <> [] ->
path_has_slash p = false -> path_is_dirref p = false -> fs_lookup (m_fs (cfg_model cf)) p = Some d ->
alloc_fd (m_fds (cfg_model cf)) = Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 -> TA [] -> TB [] ->
(forall (e : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
In e openat_errnos ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J TA cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 errv] ->
CNEXT J cf cf' -> m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) (FdFile p (Z_to_bv 64 0)) -> m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J TB cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 3) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J (t_alt2 TA TB) cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until d. intros HCK -> -> -> STR NONUL LEN NE NSL NDR FS AFD FD3 GG GV ER ST LO CEIL SPH APART MI RA HA0 HB0 KA KB.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
apply orb_false_iff in NDR as [NDOT NDD].
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_file F fc asegs J (SYS F fc) R pc mm cf p d TA TB HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; lia | exact NE | exact NDOT | exact FS | rewrite AFD; exact FD3 | exact HA0 | exact HB0 | | ].
-
intros e c1 He HN1 SIO1.
assert (He' : 1 <= e <= 4095).
{ unfold openat_errnos in He. cbn [In] in He.
destruct He as [<-|[<-|[<-|[<-|[]]]]]; unfold ENOMEM, EACCES, EMFILE, ENFILE; lia. }
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := e);
[ exact He' | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply (KA e); [exact He | exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
-
intros c1 HN1 FDS1 FSE1. rewrite AFD in FDS1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next, AFD. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_ok_A with (lo := lo) (r := 3);
[ lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact MI1 | exact RA | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KB; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2
| eapply rw_cells_transport; [exact ER | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | exact I]]
| exact HN1 | exact FDS1 | exact FSE1 ].
Qed.

Lemma open_dot_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (TA TB : TSet)
(g errv : word) (pp lo : Z),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (dot_path ++ [Z_to_bv 8 0]) ->
alloc_fd (m_fds (cfg_model cf)) = Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + 2 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 -> TA [] -> TB [] ->
(forall (e : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
In e openat_errnos ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J TA cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 errv] ->
CNEXT J cf cf' -> m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) FdDir -> m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J TB cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 3) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J (t_alt2 TA TB) cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> STR AFD FD3 GG GV ER ST LO CEIL SPH APART MI RA HA0 HB0 KA KB.
unfold dot_path in *.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_dot F fc asegs J (SYS F fc) R pc mm cf TA TB HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [cbn; intros [E|[]]; discriminate|]; split; [reflexivity|]; split; [reflexivity|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| rewrite AFD; exact FD3 | exact HA0 | exact HB0 | | ].
-
intros e c1 He HN1 SIO1.
assert (He' : 1 <= e <= 4095).
{ unfold openat_errnos in He. cbn [In] in He.
destruct He as [<-|[<-|[<-|[<-|[]]]]]; unfold ENOMEM, EACCES, EMFILE, ENFILE; lia. }
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := e);
[ exact He' | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply (KA e); [exact He | exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
-
intros c1 HN1 FDS1 FSE1. rewrite AFD in FDS1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next, AFD. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_ok_A with (lo := lo) (r := 3);
[ lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact MI1 | exact RA | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KB; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2
| eapply rw_cells_transport; [exact ER | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | exact I]]
| exact HN1 | exact FDS1 | exact FSE1 ].
Qed.

Lemma open_absent_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z) (p : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (length p <= 4095)%nat -> p <> [] ->
path_has_slash p = false -> path_is_dirref p = false -> fs_lookup (m_fs (cfg_model cf)) p = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENOENT)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until p. intros HCK -> -> -> STR NONUL LEN NE NSL NDR FS GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
apply orb_false_iff in NDR as [NDOT NDD].
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_absent F fc asegs J (SYS F fc) R pc mm cf p T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; lia | exact NE | exact NDOT | exact FS | ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENOENT);
[ unfold ENOENT; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

Lemma open_empty_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp [Z_to_bv 8 0] ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENOENT)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> STR GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_empty F fc asegs J (SYS F fc) R pc mm cf T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [intros []|]; split; [reflexivity|]; split; [reflexivity|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENOENT);
[ unfold ENOENT; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

Lemma open_toolong_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z) (p : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (4096 <= length p)%nat ->
path_has_slash p = false -> path_eqb p dotdot_path = false ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENAMETOOLONG)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until p. intros HCK -> -> -> STR NONUL LEN NSL NDD GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_toolong F fc asegs J (SYS F fc) R pc mm cf p T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; exact LEN | ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENAMETOOLONG);
[ unfold ENAMETOOLONG; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6434400 - 164, 6434400 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

End DrvOpenA.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qfub Q1jK QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QsRG.Mq0 QRjH QBxa.Mq5 QMz4.
Import QXup.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq4 QlKV.Mqj.
Import QZsi.
Import Qfub Q1jK QCKW.Mq6.
Import QupI.

Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.

Definition VPRINTF_V : Z := 0x4fd64.
Definition FPRINTF_V : Z := 0x4fd70.
Definition FWRITE_V : Z := 0x4fd58.
Definition FMT_D : Z := 0x14f44.
Definition FMT_USAGE : Z := 0x16263.
Definition FMT_CANNOT : Z := 0x1ef3c.
Definition FMT_READERR : Z := 0x1ef51.
Definition FMT_REFUSED : Z := 0x1a8f3.
Definition MSG_SHORT : Z := 0x214f8.
Definition MSG_OVERRUN : Z := 0x16274.
Definition MSG_OOM : Z := 0x14f30.

Definition PF_STACK_A : Z := 8192.

Definition PFW_OUT (lo sp : Z) : list (Z * Z) := [(lo, sp); (F_STDOUT, F_STDOUT + 232); (STDOUT_BUF, STDOUT_BUF + 1024)].
Definition PFW_ERR (lo sp : Z) : list (Z * Z) := [(lo, sp); (F_STDERR, F_STDERR + 232)].

Definition STDIO_WRITE_A : Z := 0xd5094.

Definition STDOUT0_A (m : word -> option byte) : Prop := pristine m F_STDOUT (F_STDOUT + 232) /\ pristine m 0x645ca0 0x6460b0.

Definition STDERR0_A (m : word -> option byte) : Prop := pristine m F_STDERR (F_STDERR + 232).

Definition STDERRC_A (m : word -> option byte) : Prop := exists wp rp : word, file_clean m F_STDERR wp rp.

Fixpoint zl (k : nat) : list Z := match k with O => [] | S k' => 48 :: 10 :: zl k' end.
Definition so_w (k : nat) : QdZp.stdout_st :=
QdZp.mkStdout true (zl (Nat.pred k)) false false.
Definition STDOUTW_A (m : word -> option byte) (k : nat) : Prop := Qu3b.Mq4.stdout_file m (so_w k).

Definition PFIMG_A (m : word -> option byte) : Prop :=
pris_A m /\ rtc_R m
/\ (exists g : word, bytes_at asegs m 0xe8f90 (le8 (Z_to_bv 64 0x645560)) /\ bytes_at asegs m 0x645560 (le8 g) /\ bytes_at asegs m (A_TP - 16) (le8 g))
/\ bytes_at asegs m 0x6457b3 [Z_to_bv 8 0].

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.

Definition emitpf1_stmt : Prop :=
forall (sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
STDOUT0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc ->
K [] ->
(forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_OUT lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDOUTW_A m' 1%nat -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra' sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x91d7c) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 1 (zero_lines 1)) K) cf
(MS (mkR (Z_to_bv 64 0x91d7c) sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 EMITPF_A) fc None m (seg_rom asegs)).

Definition emitpfk_stmt : Prop :=
forall (k : nat) (sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf -> (1 <= k <= 3)%nat ->
STDOUTW_A m k -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc ->
K [] ->
(forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_OUT lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDOUTW_A m' (S k) -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra' sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 0x91d7c) fc' None m' (seg_rom asegs))) ->
AJ J K cf
(MS (mkR (Z_to_bv 64 0x91d7c) sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 EMITPF_A) fc None m (seg_rom asegs)).

Definition fmt_s_msg (fmt : Z) (str : list byte) : list byte :=
if Z.eqb fmt FMT_USAGE then msg_usage str
else if Z.eqb fmt FMT_CANNOT then msg_cannot_open str
else msg_read_error str.

Definition fprintf_s_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo fmt p : Z) (str slack : list byte),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(fmt = FMT_USAGE \/ fmt = FMT_CANNOT \/ fmt = FMT_READERR) ->
a0 = Z_to_bv 64 F_STDERR -> a1 = Z_to_bv 64 fmt -> a2 = Z_to_bv 64 p ->
bytes_at asegs m p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
(- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length str) < 2^17 ->
unpoisoned asegs m A_SB p (Z.of_nat (length str) + 1) -> 0 <= p -> bv_unsigned sp <= p ->
p + Z.of_nat (length str) + 9 <= 2^47 ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 (fmt_s_msg fmt str)) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FPRINTF_V) fc None m (seg_rom asegs)).

Definition fprintf_u_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
a0 = Z_to_bv 64 F_STDERR -> a1 = Z_to_bv 64 FMT_REFUSED -> a2 = Z_to_bv 64 67108864 ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> frm0 fc -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 msg_refused) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FPRINTF_V) fc None m (seg_rom asegs)).

Definition fwrite_msg (msg : Z) : list byte :=
if Z.eqb msg MSG_SHORT then msg_short else if Z.eqb msg MSG_OVERRUN then msg_overrun else msg_oom.

Definition fwrite_stmt : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (K : TSet) (lo msg : Z),
CK J cf ->
fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(msg = MSG_SHORT \/ msg = MSG_OVERRUN \/ msg = MSG_OOM) ->
a0 = Z_to_bv 64 msg -> a1 = Z_to_bv 64 (Z.of_nat (length (fwrite_msg msg))) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 F_STDERR ->
STDERR0_A m -> PFIMG_A m -> PFRT m ->
(forall g, msg / 8 <= g <= (msg + 31) / 8 -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> PFLO <= lo -> lo + PF_STACK_A <= bv_unsigned sp ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 <= 2^47 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
K [] ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' (cf' : config),
munch (PFW_ERR lo (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> STDERRC_A m' -> fsaved F F' -> (frm0 fc -> frm0 fc') ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J K cf' (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
AJ J (t_emit (W 2 (fwrite_msg msg)) K) cf
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FWRITE_V) fc None m (seg_rom asegs)).
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import QXup.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QBpc.

Import Qhd4.
Import Qwm6.Mq4.
Import QupI.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Lemma pristine_sub : forall m lo hi lo' hi', pristine m lo hi -> lo <= lo' -> hi' <= hi -> pristine m lo' hi'.
Proof. intros m lo hi lo' hi' P H1 H2 a Ha. apply P. lia. Qed.

Lemma pris_A_in : forall m lo hi, pris_A m -> In (lo, hi) PRIS_A -> pristine m lo hi.
Proof. intros m lo hi P Hin. unfold pris_A in P. exact (proj1 (Forall_forall _ _) P (lo, hi) Hin). Qed.

Lemma rtc_R_in : forall m a bs, rtc_R m -> In (a, bs) RTC_R -> bytes_at asegs m a bs.
Proof. intros m a bs P Hin. unfold rtc_R in P. exact (proj1 (Forall_forall _ _) P (a, bs) Hin). Qed.
Lemma ro_of_bytes : forall m a cs, cells_wf cs -> bytes_at asegs m a (cells_bytes cs) -> ro_cells asegs m a cs.
Proof. intros m a cs WF B. split; [exact WF | exact B]. Qed.
Ltac rtcR_cell P a bs := apply ro_of_bytes; [cbn; tauto | cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; exact (rtc_R_in _ a bs P ltac:(unfold RTC_R; cbn [In]; tauto))].

Ltac pris_get P lo hi :=
let Hf := fresh "PR" in
assert (Hf : pristine _ lo hi) by (apply (pris_A_in _ lo hi P); unfold PRIS_A; cbn [In]; tauto).

Section PrisR.
Context {RC__ : Q6q3.RunConsts}.

Lemma rtc_R_of_HEAPA : forall (HIx : heap_iface_A A4L) A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> rtc_R m.
Proof.
intros HIx A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as RT. cbn [hl_rt_consts A4L] in RT. unfold a4_rt_consts in RT.
unfold rtc_R, RTC_R. rewrite Forall_forall in RT. repeat (apply Forall_cons; [apply RT; cbn [In]; repeat (try (left; reflexivity); right)|]). apply Forall_nil.
Qed.
End PrisR.

Lemma rw_cells_pristine : forall (m : word -> option byte) A bs,
pristine m A (A + Z.of_nat (length bs)) ->
rw_bytes_b asegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
rw_cells asegs m A [CB (length bs) bs].
Proof.
intros m A bs P Hb HA Hhi. apply rw_cells_image0; [| exact Hb | exact HA | exact Hhi].
intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply P. exact Ha.
Qed.

Lemma rw_cells_pristine_recast : forall (m : word -> option byte) A bs cs,
pristine m A (A + Z.of_nat (length bs)) ->
rw_bytes_b asegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs ->
rw_cells asegs m A cs.
Proof.
intros m A bs cs P Hb HA Hhi WF E1 E2.
apply (rw_cells_recast asegs m A [CB (length bs) bs] cs); [| exact WF | cbn; rewrite app_nil_r; exact E1 | cbn; rewrite Nat.add_0_r; exact E2].
apply rw_cells_pristine; assumption.
Qed.

Lemma ro_of_rw : forall m A cs, rw_cells asegs m A cs -> ro_cells asegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Fixpoint img_rw_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom asegs (wa A), wview asegs (fun _ => None) (wa A) with
| Some _, Some _ => img_rw_b (A + 1) n'
| _, _ => false
end
end.

Lemma wview_of_empty : forall m (a : word), wview asegs (fun _ => None) a <> None -> wview asegs m a <> None.
Proof. intros m a H. unfold wview in *. destruct (m a); [discriminate | exact H]. Qed.

Lemma img_rw_b_sound : forall n A m, img_rw_b A n = true ->
forall i, 0 <= i < Z.of_nat n -> (exists b, mrd asegs m (wa (A + i)) = Some b) /\ wview asegs m (wa (A + i)) <> None.
Proof.
induction n as [|n IH]; intros A m Hb i Hi; [lia|].
cbn [img_rw_b] in Hb.
destruct (seg_rom asegs (wa A)) as [b0|] eqn:Er; [|discriminate].
destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. split.
+ unfold mrd. destruct (m (wa A)) as [b|]; [exists b; reflexivity | exists b0; exact Er].
+ apply wview_of_empty. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) m Hb). lia.
Qed.

Lemma img_rw_any : forall A n m, img_rw_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
exists junk, rw_cells asegs m A [CB n junk].
Proof.
intros A n m Hb HA Hhi.
pose proof (img_rw_b_sound n A m Hb) as G.
assert (EX : exists junk, length junk = n /\ forall i, (i < n)%nat -> mrd asegs m (wa (A + Z.of_nat i)) = nth_error junk i).
{ clear HA Hhi Hb. revert A G. induction n as [|n IH]; intros A G.
- exists []. split; [reflexivity | intros i Hi; lia].
- destruct (IH (A + 1) ltac:(intros i Hi; replace (A + 1 + i) with (A + (i + 1)) by lia; apply G; lia)) as (junk & Hl & Hj).
destruct (proj1 (G 0 ltac:(lia))) as (b & Hb0). rewrite Z.add_0_r in Hb0.
exists (b :: junk). split; [cbn; lia|]. intros [|i] Hi; cbn [nth_error].
+ rewrite Z.add_0_r. exact Hb0.
+ replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply Hj. lia. }
destruct EX as (junk & Hl & Hj). exists junk.
split; [split|].
- cbn. rewrite Hl. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hj. lia.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply (proj2 (G i Hi)).
Qed.

Lemma rw_of_ro_img : forall m A cs, ro_cells asegs m A cs -> img_rw_b A (cells_size cs) = true -> rw_cells asegs m A cs.
Proof.
intros m A cs RO Hb. split; [exact RO|]. destruct RO as [Hwf (HA & Hhi & _)].
rewrite (cells_bytes_length cs Hwf) in Hhi.
split; [exact HA|]. split; [exact Hhi|].
intros i Hi. apply (proj2 (img_rw_b_sound _ A m Hb i Hi)).
Qed.

Lemma find_segment_high_A : forall z n, 1 <= n -> 0x647000 <= z -> find_segment asegs z n = None.
Proof.
intros z n Hn Hz. apply QBpc.find_segment_high; [exact Hn|].
assert (E : segs_top asegs <= 0x647000) by (vm_compute; discriminate). lia.
Qed.

Lemma mrd_high_overlay : forall m (a : word) b, 0x647000 <= bv_unsigned a -> mrd asegs m a = Some b -> m a = Some b.
Proof.
intros m a b Ha H. unfold mrd in H. destruct (m a) as [b'|]; [exact H|].
unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1%Z in H. rewrite (find_segment_high_A (bv_unsigned a) 1 ltac:(lia) Ha) in H. discriminate.
Qed.

Lemma wr_at_of_bytes_at_high : forall m A bs, bytes_at asegs m A bs -> 0x647000 <= A -> wr_at asegs m A (Z.of_nat (length bs)).
Proof.
intros m A bs (HA & Hhi & Hb) Hlo. split; [exact HA|]. split; [exact Hhi|].
intros i Hi.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
specialize (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. rewrite E in Hb.
pose proof (mrd_high_overlay m (wa (A + i)) b ltac:(rewrite wa_unsigned by lia; lia) Hb) as Hm.
unfold wview. rewrite Hm. discriminate.
Qed.

Lemma rw_of_ro_high : forall m A cs, ro_cells asegs m A cs -> 0x647000 <= A -> rw_cells asegs m A cs.
Proof.
intros m A cs RO Hlo. split; [exact RO|]. destruct RO as [Hwf Hb].
rewrite <- (cells_bytes_length cs Hwf). apply wr_at_of_bytes_at_high; [exact Hb | exact Hlo].
Qed.

Definition in_ivs (L : list (Z * Z)) (x : Z) : Prop := Exists (fun iv => fst iv <= x < snd iv) L.

Lemma prisl_agree : forall (L : list (Z * Z)) (m m' : word -> option byte),
Forall (fun iv => pristine m (fst iv) (snd iv)) L ->
Forall (fun iv => 0 <= fst iv /\ snd iv <= 2^64) L ->
(forall x, 0 <= x < 2^64 -> in_ivs L x -> m' (wa x) = m (wa x)) ->
Forall (fun iv => pristine m' (fst iv) (snd iv)) L.
Proof.
intros L m m' P R E. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) P _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
pose proof (proj1 (Forall_forall _ _) R _ IN) as [R1 R2]. cbn [fst snd] in R1, R2.
apply E; [lia|]. unfold in_ivs. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
Qed.

Lemma stdio0_agree : forall m m', stdio0 m -> (forall x, 0 <= x < 2^64 -> in_ivs STDIO0_A x -> m' (wa x) = m (wa x)) -> stdio0 m'.
Proof.
intros m m' S E. unfold stdio0. apply (prisl_agree STDIO0_A m m' S); [| exact E].
unfold STDIO0_A. repeat constructor; cbn; lia.
Qed.

Lemma in_stdio0_cases : forall x, in_ivs STDIO0_A x -> 0xecd40 <= x < 0xece28 \/ 0xece30 <= x < 0xecf18 \/ 0x645ca0 <= x < 0x6460b0 \/ 0x624810 <= x < 0x624840.
Proof.
intros x Hx. unfold in_ivs, STDIO0_A in Hx.
repeat (apply Exists_cons in Hx; destruct Hx as [Hx|Hx]; [cbn [fst snd] in Hx; lia|]). apply Exists_nil in Hx. destruct Hx.
Qed.

Lemma stdio0_munch : forall m m' W, stdio0 m -> munch W m m' ->
Forall (fun iv => snd iv <= 0xecd40 \/ (0xece28 <= fst iv /\ snd iv <= 0xece30) \/ (0xecf18 <= fst iv /\ snd iv <= 0x624810) \/ (0x624840 <= fst iv /\ snd iv <= 0x645ca0) \/ 0x6460b0 <= fst iv) W ->
stdio0 m'.
Proof.
intros m m' W S MU FW. eapply stdio0_agree; [exact S|]. intros x Hx HI. apply MU. rewrite wa_unsigned by lia.
apply in_stdio0_cases in HI. clear - FW HI. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [H1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Definition drvA_memS (argv : list (list byte)) (USP : Z) (m : word -> option byte) : Prop := drvA_mem argv USP m /\ stdio0 m.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfub. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq5.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition A_GUARD_GOT : Z := 0xe8f90.
Definition A_GUARD : Z := 0x645560.

Section DrvOpenA.
Context {RC__ : Q6q3.RunConsts}.
Variable J : aj_base asegs.
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs J.

Definition open_frame (junk16 : list byte) (g s1 s0 ra a2 a3 a4 a5 a6 a7 : word) : list cell :=
[CB 16 junk16; C8 g; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma open_pre_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g : word) (lo : Z),
a1 = Z_to_bv 64 0 ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo ->
mem_inv asegs m ->
(forall m' junk16,
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp - 96) ->
rw_cells asegs m' (bv_unsigned sp - 96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcf068) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp a0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(Z_to_bv 64 (-100)) a0 (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ECALL_PC) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros -> GG GV ST LO GLO MI HK.
unfold A_GUARD_GOT, A_GUARD, OPEN_A, ECALL_PC in *.
word_range sp SPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
carve_frame 96%nat ST.
do 4 step.
do 4 step.
do 2 step.
do 4 step.
step.
step. step.
step.
if_falsex.
do 3 step.

if_falsex.
step. step.
do 4 step.
do 3 step.
step.
step.
do 7 step.
eapply HK; [exact MU | exact WM | assumption | exact ST | exact FR].
Qed.

Lemma open_ret_ok_A :
forall (ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pth x2 x3 x4 x5 x6 x7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g : word) (lo r : Z) junk16,
0 <= r < 2^31 ->
ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp - 96) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo -> bv_unsigned sp < 2^64 ->
rw_cells asegs m (bv_unsigned sp - 96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcf068) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp pth t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(Z_to_bv 64 r) pth x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdee1c) fc None m (seg_rom asegs)).
Proof.
intros until junk16. intros Hr GV ST LO GLO SPH FR MI RA HK.
unfold A_GUARD in *.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
step.
step. step. step.
if_truex.
step.
rewrite (unsigned_lit r) by lia. rewrite Z.add_0_r, (swrap32_id r) by lia.
step.
do 2 step.
step.
replace (bv_ltu (Z_to_bv 64 r) (Z_to_bv 64 (-4095))) with true
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
cbv iota.
step.
unfold open_frame in FR.
step. step.
step. if_falsex.
step.
rewrite (unsigned_lit r) by lia. rewrite Z.add_0_r, (swrap32_id r) by lia.
do 4 step.
step.
try (replace (bv_unsigned sp - 96 + 96) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
eapply HK; [exact MU | exact WM | exact MI | release_frame FR ST (bv_unsigned sp); exact ST].
Qed.

Lemma open_ret_err_A :
forall (ra sp gp t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pth x2 x3 x4 x5 x6 x7 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (g errv : word) (lo e : Z) junk16,
1 <= e <= 4095 ->
ro_cells asegs m A_GUARD [C8 g] ->
stk asegs m lo (bv_unsigned sp + -96) -> lo + 112 <= bv_unsigned sp -> A_GUARD + 8 <= lo -> bv_unsigned sp < 2^64 ->
rw_cells asegs m (bv_unsigned sp + -96) (open_frame junk16 g s1 s0 ra a2 a3 a4 a5 a6 a7) ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(bv_unsigned sp + -112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
evt asegs Q (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcf068) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) pth t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 A_GUARD)
(errno_ret e) pth x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdee1c) fc None m (seg_rom asegs)).
Proof.
intros until junk16. intros He GV ST LO GLO SPH FR ER MI RA HK.
unfold A_GUARD, A_TP in *. unfold open_frame in FR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
unfold errno_ret.
step.
step. step. step. if_truex.
step.
rewrite (unsigned_lit_wrap (- e)), Z.add_0_r.
replace ((- e) mod 2 ^ 64) with (- e + 4294967296 * 4294967296) by (Z.div_mod_to_equations; lia).
rewrite swrap32_shift, swrap32_id by lia.
step.
do 2 step.
step.
replace (bv_ltu (Z_to_bv 64 (- e)) (Z_to_bv 64 (-4095))) with false
by (symmetry; unfold bv_ltu; rewrite !unsigned_lit_wrap; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
cbv iota.
carve_frame 16%nat ST.
change (6444320 - 164) with 6444156 in ER.
step. stepz. stepz.
step.
step. do 3 step.
stepz.
replace (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (- e)))) with e in *.
2: { rewrite unsigned_lit_wrap. replace (0 - (- e) mod 2 ^ 64) with (e + (- 4294967296) * 4294967296) by (Z.div_mod_to_equations; lia).
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
step.
do 3 step. step.
release_frame FR0 ST (bv_unsigned sp + -96).
step. step.
step. if_falsex.
step.
try match goal with |- context [bv_swrap 32 ?x] => replace (bv_swrap 32 x) with (-1) by (rewrite ?unsigned_lit_wrap; vm_compute; reflexivity) end.
do 4 step.
step.
try (replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned).
eapply HK; [exact MU | exact WM | exact MI | release_frame FR ST (bv_unsigned sp); exact ST | exact ER].
Qed.

Lemma open_file_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (TA TB : TSet)
(g errv : word) (pp lo : Z) (p d : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (length p <= 4095)%nat -> p <> [] ->
path_has_slash p = false -> path_is_dirref p = false -> fs_lookup (m_fs (cfg_model cf)) p = Some d ->
alloc_fd (m_fds (cfg_model cf)) = Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 -> TA [] -> TB [] ->
(forall (e : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
In e openat_errnos ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J TA cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 errv] ->
CNEXT J cf cf' -> m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) (FdFile p (Z_to_bv 64 0)) -> m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J TB cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 3) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J (t_alt2 TA TB) cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until d. intros HCK -> -> -> STR NONUL LEN NE NSL NDR FS AFD FD3 GG GV ER ST LO CEIL SPH APART MI RA HA0 HB0 KA KB.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
apply orb_false_iff in NDR as [NDOT NDD].
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_file F fc asegs J (SYS F fc) R pc mm cf p d TA TB HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; lia | exact NE | exact NDOT | exact FS | rewrite AFD; exact FD3 | exact HA0 | exact HB0 | | ].
-
intros e c1 He HN1 SIO1.
assert (He' : 1 <= e <= 4095).
{ unfold openat_errnos in He. cbn [In] in He.
destruct He as [<-|[<-|[<-|[<-|[]]]]]; unfold ENOMEM, EACCES, EMFILE, ENFILE; lia. }
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := e);
[ exact He' | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply (KA e); [exact He | exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
-
intros c1 HN1 FDS1 FSE1. rewrite AFD in FDS1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next, AFD. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_ok_A with (lo := lo) (r := 3);
[ lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact MI1 | exact RA | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KB; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2
| eapply rw_cells_transport; [exact ER | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | exact I]]
| exact HN1 | exact FDS1 | exact FSE1 ].
Qed.

Lemma open_dot_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (TA TB : TSet)
(g errv : word) (pp lo : Z),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (dot_path ++ [Z_to_bv 8 0]) ->
alloc_fd (m_fds (cfg_model cf)) = Z_to_bv 64 3 -> fd_lookup (m_fds (cfg_model cf)) (Z_to_bv 64 3) = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + 2 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 -> TA [] -> TB [] ->
(forall (e : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
In e openat_errnos ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 e)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J TA cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 errv] ->
CNEXT J cf cf' -> m_fds (cfg_model cf') = fd_insert (m_fds (cfg_model cf)) (Z_to_bv 64 3) FdDir -> m_fs (cfg_model cf') = m_fs (cfg_model cf) ->
AJ J TB cf'
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 3) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J (t_alt2 TA TB) cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> STR AFD FD3 GG GV ER ST LO CEIL SPH APART MI RA HA0 HB0 KA KB.
unfold dot_path in *.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_dot F fc asegs J (SYS F fc) R pc mm cf TA TB HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [cbn; intros [E|[]]; discriminate|]; split; [reflexivity|]; split; [reflexivity|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| rewrite AFD; exact FD3 | exact HA0 | exact HB0 | | ].
-
intros e c1 He HN1 SIO1.
assert (He' : 1 <= e <= 4095).
{ unfold openat_errnos in He. cbn [In] in He.
destruct He as [<-|[<-|[<-|[<-|[]]]]]; unfold ENOMEM, EACCES, EMFILE, ENFILE; lia. }
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := e);
[ exact He' | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply (KA e); [exact He | exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
-
intros c1 HN1 FDS1 FSE1. rewrite AFD in FDS1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next, AFD. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_ok_A with (lo := lo) (r := 3);
[ lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact MI1 | exact RA | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KB; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2
| eapply rw_cells_transport; [exact ER | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia | exact I]]
| exact HN1 | exact FDS1 | exact FSE1 ].
Qed.

Lemma open_absent_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z) (p : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (length p <= 4095)%nat -> p <> [] ->
path_has_slash p = false -> path_is_dirref p = false -> fs_lookup (m_fs (cfg_model cf)) p = None ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENOENT)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until p. intros HCK -> -> -> STR NONUL LEN NE NSL NDR FS GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
apply orb_false_iff in NDR as [NDOT NDD].
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_absent F fc asegs J (SYS F fc) R pc mm cf p T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; lia | exact NE | exact NDOT | exact FS | ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENOENT);
[ unfold ENOENT; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

Lemma open_empty_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp [Z_to_bv 8 0] ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENOENT)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros HCK -> -> -> STR GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_empty F fc asegs J (SYS F fc) R pc mm cf T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [intros []|]; split; [reflexivity|]; split; [reflexivity|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENOENT);
[ unfold ENOENT; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

Lemma open_toolong_cps_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cf : config) (T : TSet)
(g errv : word) (pp lo : Z) (p : list byte),
CK J cf ->
a0 = Z_to_bv 64 pp -> a1 = Z_to_bv 64 0 -> tp = Z_to_bv 64 A_TP ->
bytes_at asegs m pp (p ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) p -> (4096 <= length p)%nat ->
path_has_slash p = false -> path_eqb p dotdot_path = false ->
ro_cells asegs m A_GUARD_GOT [C8 (Z_to_bv 64 A_GUARD)] -> ro_cells asegs m A_GUARD [C8 g] ->
rw_cells asegs m (A_TP - 164) [C4 errv] ->
stk asegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
(pp + Z.of_nat (length p) + 1 <= lo \/ bv_unsigned sp <= pp) ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (cf' : config),
munch [(bv_unsigned sp - 112, bv_unsigned sp); (A_TP - 164, A_TP - 160)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) -> rw_cells asegs m' (A_TP - 164) [C4 (Z_to_bv 64 ENAMETOOLONG)] ->
CNEXT J cf cf' -> same_io cf cf' ->
AJ J T cf' (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
AJ J T cf (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPEN_A) fc None m (seg_rom asegs)).
Proof.
intros until p. intros HCK -> -> -> STR NONUL LEN NSL NDD GG GV ER ST LO CEIL SPH APART MI RA KA.
unfold A_GUARD_GOT, A_GUARD, A_TP in *.
word_range sp SPR. rc_lia_prep. unfold alloc_ceiling in CEIL.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m) as MU.
apply (aj_evt J).
eapply open_pre_A with (lo := lo); [reflexivity | exact GG | exact GV | exact ST | lia | unfold A_GUARD; lia | exact MI |].
intros m1 junk16 MU1 WM1 MI1 ST1 FR1.
transport_after_call asegs m m1 MU1 WM1; try clear MI; clear MU1 WM1.
apply evt_done.
lazymatch goal with |- AJ _ ?TT _ (MS ?R _ ?pc _ _ ?mm ?ro) =>
apply (@aj_ecall F fc asegs J R pc mm ro _ cf TT ecall_fetch ecall_is) end.
lazymatch goal with |- AJ _ _ _ (epend ?R ?pc ?mm ?ro _) =>
eapply (@ajs_open_toolong F fc asegs J (SYS F fc) R pc mm cf p T HCK) end;
[ unfold open_pre; split; [reflexivity|]; split; [apply bv_eq; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact NONUL|]; split; [exact NSL|]; split; [exact NDD|];
(match goal with |- context [QsRG.Mq0.getr ?R 11%bv] => replace (QsRG.Mq0.getr R 11%bv) with (Z_to_bv 64 pp : word) by reflexivity end;
rewrite unsigned_lit by (destruct STR as (B1 & B2 & _); rewrite ?length_app in B2; cbn [length] in B2; lia); exact STR)
| unfold path_max; exact LEN | ].
-
intros c1 HN1 SIO1.
apply (aj_evt J).
lazymatch goal with |- evt _ _ (QsRG.Mq0.mkst ?R ?pc ?mm ?ro) =>
change (QsRG.Mq0.mkst R pc mm ro) with (MS R F pc fc None mm ro) end.
rewrite ecall_next. unfold QsRG.Mq0.regupd. simp_regs.
change (QsRG.Mq0.seg_rom asegs) with (seg_rom asegs).
eapply open_ret_err_A with (lo := lo) (e := ENAMETOOLONG);
[ unfold ENAMETOOLONG; lia | exact GV | exact ST1 | lia | unfold A_GUARD; lia | lia | exact FR1 | exact ER | exact MI1 | exact RA | ].
unfold A_TP. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 ER2.
assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp); (6444320 - 164, 6444320 - 160)] m m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
apply evt_done.
eapply KA; [exact MU' | eapply wmono_trans; [exact WM | exact WM2] | exact MI2
| exact ST2 | exact ER2 | exact HN1 | exact SIO1].
Qed.

End DrvOpenA.
