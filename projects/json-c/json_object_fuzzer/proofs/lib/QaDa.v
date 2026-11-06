(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qhd4 QGcC QCKW Q1jK QPra QsRG Qnhz QBxa QRjH Q9ox QsV0 Qn1e QMz4 QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn QBpc Qwm6 QlKV QsKa Qw5U QpNt Qfub Qujl QjDJ Qirj QWew QupI QnXa QdM4 QscU QOii QtWm Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QGcC.
Import QCKW.Mq5 QCKW.Mq6 QCKW.Mq7 Q1jK QPra.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH Q9ox.Mq2 QsV0 Qn1e QBxa.Mq5 QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QBpc.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QpNt.Mq8.
Import Qfub Qujl.Mq4 QjDJ Qirj QWew QupI.Mq1 QnXa.Mq0 QupI QdM4.Mq4 QdM4.Mq3.
Import QscU QOii QtWm.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= QlES.mkr__zify_pre_hook_0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition TLOOP_A : Z := 0x91d58.
Definition TCALL_RET_A : Z := 0x91d6c.
Definition EMIT_RET_A : Z := 0x91d7c.
Definition TDISP_A : Z := 0x91ce8.
Definition TALLOC_A : Z := 0x91cfc.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma pristine_munch : forall m m' lo hi W, pristine m lo hi -> munch W m m' ->
Forall (fun iv => snd iv <= lo \/ hi <= fst iv) W -> 0 <= lo -> hi <= 2^64 -> pristine m' lo hi.
Proof.
intros m m' lo hi W P MU FW H0 H1 a Ha. rewrite <- (P a Ha). apply MU. rewrite wa_unsigned by lia.
clear - FW Ha. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in FW as [F1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Lemma STDOUTW_agree : forall m m' k, STDOUTW_A m k ->
(forall x, (F_STDOUT <= x < F_STDOUT + 232 \/ STDOUT_BUF <= x < STDOUT_BUF + 1024) -> m' (wa x) = m (wa x)) -> (k <= 4)%nat -> STDOUTW_A m' k.
Proof.
intros m m' k SW E Hk. exact (QscU.Mq4.stdoutw_agree m m' k SW E).
Qed.

Lemma bytes_at_agreeT : forall (m m' : word -> option byte) a bs,
bytes_at asegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
intros m m' a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold mrd in *. rewrite E by lia. apply H3. exact Hi.
Qed.

Section Target.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_MALLOC_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.
Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Notation TSP := (USP - 208).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variables (BB_REST BD_REST : Z).
Variables (BQ_REST BN_REST : Z).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.

Hypothesis OBL_GA_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> GA m.
Hypothesis TGTB : 0 <= TGT_STACK_A /\ LO + TGT_STACK_A <= USP - 208 /\ 0 <= TGT_BB_A /\ 0 <= TGT_BD_A.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.

Definition TRV_BB : Z := 1536 + 4 * TGT_BB_A.

Definition TR_BB : Z := (3 * 67108864 + 45101) + TRV_BB.
Definition TR_BD : Z := 4 * TGT_BD_A.
Definition TR_BQ : Z := (67108864 + 8192) + 16 * TRV_BB.
Hypothesis RESTS : TR_BB <= BB_REST /\ TR_BD <= BD_REST.
Hypothesis RESTS6 : TR_BQ <= BQ_REST /\ 512 + TRV_BB <= 512 * BN_REST /\ TRV_BB <= 2^30.

Notation len := (Z.of_nat (length data)).
Notation cl := (cfglen_of data).
Notation pl := (Z.of_nat (length data) - 6 - cfglen_of data).
Notation payload := (skipn (Z.to_nat (6 + cfglen_of data)) data).
Notation TINVx := (TINV HIx argv USP LO fs LM0).

Definition trun_frame (j0 : list byte) (s5v s6v s7v : word) (buf : Z) : list cell :=
[CB 8 j0; C8 s7v; C8 s6v; C8 s5v; C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 (buf + 6 + cl)); C8 (Z_to_bv 64 cl);
C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 2)); C8 (Z_to_bv 64 TRUN_RET_A)].

Definition OWN (al : Z) : list blk := if pl =? 0 then [] else [(al, pl)].

Lemma lock_of_dm : forall m, drvA_mem argv USP m -> rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)].
Proof.
intros m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0x645820 0x6458a0. unfold T_LOCALE_LOCK_A.
eapply (rw_cells_pristine_recast m 0x645890 (le4 (Z_to_bv 64 0)));
[ eapply pristine_sub; [exact PR | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity|exact I] | reflexivity | reflexivity ].
Qed.

Lemma llvminit_of_dm : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)].
Proof.
intros A LB LM FR B m md HP. pose proof (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) as P. unfold GOT_LLVMINIT.
rtcR_cell P 0xe8e28 (le8 (Z_to_bv 64 0x0)).
Qed.

Lemma PFIMG_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> PFIMG_A m.
Proof.
intros A LB LM FR B m md D HP. split; [exact (dm_pris _ _ _ D) | split; [exact (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) | split]].
- destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & G1 & G2 & G3). cbn [hl_got_guard hl_guard hl_tp hla_base A4L A4H] in G1, G2, G3.
exists g. split; [exact G1 | split; [exact G2 | exact G3]].
- pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL. cbn [hl_libc hla_base A4L A4H] in NL. exact NL.
Qed.

Lemma stderr_clean_of_pristine : forall m, STDERR0_A m -> exists wp rp, file_clean m F_STDERR wp rp.
Proof.
intros m P. unfold STDERR0_A, F_STDERR in *. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
split; [| split; [| split; [| split]]].
- apply (rdn_pristine m (0xecd40 + 140) (word_to_le_bytes 4 (Z_to_bv 64 4294967295))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xecd40 + 40) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xecd40 + 56) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xecd40 + 8) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xecd40 + 16) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
Qed.

Lemma STDOUT_of_W : forall A LB LM FR B m md k, (1 <= k <= 4)%nat -> STDOUTW_A m k -> HEAPAx A LB LM FR B m md ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
(zero_lines (Nat.pred k) = [] /\ exists wp1 rp1, file_clean m 0xece30 wp1 rp1)
\/ (zero_lines (Nat.pred k) <> [] /\ fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ exists wb wp bufp bufsz rp1 can, stdout_pending m wb wp bufp bufsz rp1 can (zero_lines (Nat.pred k)) /\ STDOUT_BUF <= wb /\ wp <= STDOUT_BUF + 1024).
Proof.
intros A LB LM FR B m md k Hk SW HP FDL.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (can & CG & CC & _). cbn [hl_got_guard hl_guard hla_base A4L A4H] in CG, CC.
destruct k as [|[|k]]; [lia| |].
- left. split; [reflexivity|]. exact (QscU.Mq4.stdoutw_clean m SW).
- right. split; [cbn; discriminate|]. split; [exact FDL|].
destruct (QscU.Mq4.stdoutw_pending m (S (S k)) can ltac:(lia) SW (conj (rdn_bytes_at m _ _ CG) (rdn_bytes_at m _ _ CC))) as (wb & wp & bufp & bufsz & rp1 & PEND & R1 & R2).
exists wb, wp, bufp, bufsz, rp1, can. split; [exact PEND| split; [exact R1| exact R2]].
Qed.

Definition dcellL (x : Z) : Prop :=
USP <= x < USP + 2^22 \/ in_pris x \/ A_TP - 168 <= x < A_TP - 164 \/ ATEXIT_A <= x < ATEXIT_A + 304 \/ ADFLAG_A <= x < ADFLAG_A + 1.

Lemma drvA_mem_agreeL : forall m m', drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcellL x -> m' (wa x) = m (wa x)) ->
(forall x, dcellL (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
drvA_mem argv USP m'.
Proof.
intros m m' D EQ WM LOC' MI'. destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC (mid & AT & MIDL)].
pose proof USPF as (U1 & U2 & U3).
assert (PH : ax_phase m' = ax_phase m) by (apply ax_phase_agree; apply EQ; [unfold ADFLAG_A; lia | unfold dcellL; repeat (lazymatch goal with |- _ \/ _ => right end); unfold ADFLAG_A; lia]).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agreeT; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF. apply EQ; [lia | apply HD; lia]. }
assert (RWT : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x) -> rw_cells asegs m' A cs).
{ intros A cs [RO (W1 & W2 & W3)] HD. split; [apply ROT; assumption|]. split; [exact W1|]. split; [exact W2|]. intros i Hi.
apply WM; [| apply W3; exact Hi]. rewrite wa_unsigned by lia. apply HD. lia. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S0 | exact EQA]]. apply ROT; [exact A0|]. cbn. intros; left; lia.
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S1 | exact EQA]]. apply ROT; [exact A1|]. cbn. intros; left; lia.
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64) by (unfold PRIS_A in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia|]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. cbn. intros; right; right; left; lia.
- exact LOC'.
- exists mid. split; [| exact MIDL]. unfold atexit_cells in AT |- *. rewrite PH. apply RWT; [exact AT|]. rewrite (atexit_cellsK_size _ _ MIDL). unfold ATEXIT_A. intros; right; right; right; left; unfold ATEXIT_A; lia.
Qed.

Lemma dcellL_cases : forall x, dcellL x ->
USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x647000 /\ cs_wide x /\ ~ a4_volatile x /\ ~ (T_LOCCELL_A <= x < T_LOCCELL_A + 8)
/\ ~ (0x614810 <= x < 0x624840 /\ x <> 0x624810) /\ ~ (0xecd40 <= x < 0xece28) /\ ~ (0xece30 <= x < 0xecf18) /\ ~ (0x645ca0 <= x < 0x6460b0)).
Proof.
intros x [H|[H|[H|[H|H]]]].
- left; exact H.
- right. unfold in_pris, PRIS_A in H. unfold T_LOCCELL_A, cs_wide, a4_volatile, A_TP.
repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn [fst snd] in H; lia|]). apply Exists_nil in H. destruct H.
- right. unfold T_LOCCELL_A, A_TP, cs_wide, a4_volatile in *. lia.
- right. unfold T_LOCCELL_A, ATEXIT_A, cs_wide, a4_volatile, A_TP in *. lia.
- right. unfold T_LOCCELL_A, ADFLAG_A, cs_wide, a4_volatile, A_TP in *. lia.
Qed.

Lemma drvA_mem_presx : forall LBM SPv m m',
drvA_mem argv USP m -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
alloc_ceiling <= SPv <= USP -> drvA_mem argv USP m'.
Proof.
intros LBM SPv m m' D PRES LOC' MI' HS. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1, HS.
assert (CL : forall x, dcellL x -> client_addrx A4H (xtgt_A SPv) LBM SPv x).
{ intros x HC. pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & _)]; [left; lia|].
right; left. split; [apply OBL_CS_WIDE; exact X2|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB. intros [V|[V|V]]; [exact (X3 V) | exact (X4 V) | lia]. }
eapply drvA_mem_agreeL; [exact D | | | exact LOC' | exact MI'].
- intros x Hx HC. apply (proj1 (PRES x Hx (CL x HC))).
- intros x HC Hw. pose proof (u64_range x) as R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(lia) (CL _ HC))). exact Hw.
Qed.

Lemma drvA_mem_presT : forall LBM SPv m m',
drvA_mem argv USP m -> heap_pres A4H LBM SPv m m' -> mem_inv asegs m' -> SPv <= USP -> drvA_mem argv USP m'.
Proof.
intros LBM SPv m m' D PRES MI' HS.
assert (CL : forall x, dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> client_addr A4H LBM SPv x).
{ intros x [HC|HC].
- pose proof (dcellL_cases x HC) as [X|(X1 & X2 & _)]; [left; lia | right; left; apply OBL_CS_WIDE; exact X2].
- right; left. apply OBL_CS_WIDE. unfold cs_wide, T_LOCCELL_A, A_TP in *. lia. }
eapply drvA_mem_agreeL; [exact D | | | | exact MI'].
- intros x Hx HC. apply PRES; [lia | apply CL; left; exact HC].
- intros x HC Hw. pose proof (u64_range x) as R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(lia) (CL _ (or_introl HC)))). exact Hw.
- eapply (heap_pres_rw_cells A4H); [exact PRES | exact (dm_loc _ _ _ D) |]. right; left. intros a Ha. apply OBL_CS_WIDE. cbn in Ha. unfold cs_wide, T_LOCCELL_A, A_TP in *. lia.
Qed.

Definition twin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( (LO <= fst iv /\ snd iv <= USP - 48)
\/ (0xecd40 <= fst iv /\ snd iv <= 0xece28) \/ (0xece30 <= fst iv /\ snd iv <= 0xecf18) \/ (0x645ca0 <= fst iv /\ snd iv <= 0x6460b0)
\/ (0x614810 <= fst iv /\ snd iv <= 0x624810) \/ (0x624810 + 1 <= fst iv /\ snd iv <= 0x624840)
\/ (0x647000 <= fst iv /\ snd iv <= USP - 48) ).

Lemma drvA_mem_munchT : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall twin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x647000 /\ ~ (0x614810 <= x < 0x624840 /\ x <> 0x624810) /\ ~ (0xecd40 <= x < 0xece28) /\ ~ (0xece30 <= x < 0xecf18) /\ ~ (0x645ca0 <= x < 0x6460b0))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right; lia] |].
right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold twin in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply drvA_mem_agreeL; [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold twin in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma pristine_presx : forall LBM SPv m m' lo hi, pristine m lo hi -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' ->
(forall a, lo <= a < hi -> cs_wide a /\ ~ a4_volatile a /\ ~ (T_LOCCELL_A <= a < T_LOCCELL_A + 8) /\ a < 0x647000) ->
0 <= lo -> alloc_ceiling <= SPv -> pristine m' lo hi.
Proof.
intros LBM SPv m m' lo hi P PRES OK H0 HS a Ha. destruct (OK a Ha) as (O1 & O2 & O3 & O4). rc_lia_prep. unfold alloc_ceiling in HS.
rewrite <- (P a Ha). refine (proj1 (PRES a ltac:(lia) _)). right; left. split; [apply OBL_CS_WIDE; exact O1|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB. intros [V|[V|V]]; [exact (O2 V) | exact (O3 V) | lia].
Qed.

Lemma pristine_pres : forall LBM SPv m m' lo hi, pristine m lo hi -> heap_pres A4H LBM SPv m m' ->
(forall a, lo <= a < hi -> cs_wide a) -> 0 <= lo -> hi <= 2^64 -> pristine m' lo hi.
Proof.
intros LBM SPv m m' lo hi P PRES OK H0 H1 a Ha. rewrite <- (P a Ha). refine (proj1 (PRES a ltac:(lia) _)). right; left. apply OBL_CS_WIDE. apply OK. exact Ha.
Qed.

Lemma STDOUTW_presx : forall LBM SPv m m' k, STDOUTW_A m k -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' -> (k <= 4)%nat ->
alloc_ceiling <= SPv -> STDOUTW_A m' k.
Proof.
intros LBM SPv m m' k SW PRES Hk HS. rc_lia_prep. unfold alloc_ceiling in HS. eapply STDOUTW_agree; [exact SW | | exact Hk].
intros x Hx. unfold F_STDOUT, STDOUT_BUF in Hx. refine (proj1 (PRES x ltac:(lia) _)). right; left. split; [apply OBL_CS_WIDE; unfold cs_wide; lia|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB, a4_volatile, T_LOCCELL_A, A_TP. lia.
Qed.

Lemma STDOUTW_pres : forall LBM SPv m m' k, STDOUTW_A m k -> heap_pres A4H LBM SPv m m' -> (k <= 4)%nat -> STDOUTW_A m' k.
Proof.
intros LBM SPv m m' k SW PRES Hk. eapply STDOUTW_agree; [exact SW | | exact Hk].
intros x Hx. unfold F_STDOUT, STDOUT_BUF in Hx. refine (proj1 (PRES x ltac:(lia) _)). right; left. apply OBL_CS_WIDE; unfold cs_wide; lia.
Qed.

Lemma aef_presx : forall LBM SPv m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros LBM SPv m m' b H PRES. eapply (heap_presx_rw_cells A4H); [exact PRES | exact H |]. right; left. intros a Ha. cbn in Ha.
split; [apply OBL_CS_WIDE; unfold cs_wide, AEF_FLAG_A in *; lia|]. unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB, a4_volatile, T_LOCCELL_A, A_TP, AEF_FLAG_A in *. lia.
Qed.
Lemma aef_pres : forall LBM SPv m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> heap_pres A4H LBM SPv m m' -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros LBM SPv m m' b H PRES. eapply (heap_pres_rw_cells A4H); [exact PRES | exact H |]. right; left. intros a Ha. cbn in Ha.
apply OBL_CS_WIDE; unfold cs_wide, AEF_FLAG_A in *; lia.
Qed.
Lemma aef_munch : forall W m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= AEF_FLAG_A \/ AEF_FLAG_A + 1 <= fst iv) W -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros W m m' b H MU WM FW. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. clear - FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [H1 FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma drvA_mem_register : forall m m' mid, drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcellL x -> (x < ADFLAG_A \/ ADFLAG_A + 1 <= x) -> (x < ATEXIT_A \/ ATEXIT_A + 304 <= x) -> m' (wa x) = m (wa x)) ->
(forall x, dcellL (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
rw_cells asegs m' ATEXIT_A (atexit_cellsK 2 mid) -> length mid = 240%nat ->
(exists b, m' (Z_to_bv 64 ADFLAG_A) = Some b) ->
drvA_mem argv USP m'.
Proof.
intros m m' mid D EQ WM LOC' MI' AT2 MIDL (b & FLG). destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC _].
pose proof USPF as (U1 & U2 & U3).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia | unfold ADFLAG_A; lia | unfold ATEXIT_A; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x /\ (x < ADFLAG_A \/ ADFLAG_A + 1 <= x) /\ (x < ATEXIT_A \/ ATEXIT_A + 304 <= x)) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agreeT; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF.
destruct (HD x ltac:(lia)) as (D1 & D2 & D3). apply EQ; [lia | exact D1 | exact D2 | exact D3]. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S0 | exact EQA]]. apply ROT; [exact A0|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A. split; [unfold dcellL; left; lia | lia].
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S1 | exact EQA]]. apply ROT; [exact A1|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A. split; [unfold dcellL; left; lia | lia].
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64 /\ (hi <= ADFLAG_A \/ ADFLAG_A + 1 <= lo) /\ (hi <= ATEXIT_A \/ ATEXIT_A + 304 <= lo))
by (unfold PRIS_A in IN; unfold ADFLAG_A, ATEXIT_A; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia| | lia | lia]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A, A_TP in *. split; [unfold dcellL; right; right; left; unfold A_TP; lia | lia].
- exact LOC'.
- exists mid. split; [| exact MIDL]. unfold atexit_cells, ax_phase. rewrite FLG. exact AT2.
Qed.

Lemma flag_written : forall m, rw_cells asegs m ADAPTER_FLAG [C1 (Z_to_bv 8 1)] -> exists b, m (Z_to_bv 64 ADFLAG_A) = Some b.
Proof.
intros m [[WF (B0 & B1 & B2)] _]. specialize (B2 0%nat ltac:(cbn; lia)). unfold mrd in B2. cbn [cells_bytes cbytes app nth Z.of_nat] in B2.
rewrite Z.add_0_r in B2. unfold ADAPTER_FLAG in B2. unfold ADFLAG_A.
destruct (m (wa 0x624810)) as [b|] eqn:E; [exists b; exact E|].
exfalso. vm_compute in B2. discriminate B2.
Qed.

Lemma lb_remove_zero : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> lb_remove 0 LB = LB.
Proof.
intros A LB LM FR B m md HP.
assert (NZ : forall b, In b LB -> blk_addr b <> 0).
{ intros [a n] Hin. cbn. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & Hp & _). lia. }
clear HP. induction LB as [|b LB IH]; [reflexivity|]. cbn [lb_remove].
replace (blk_addr b =? 0) with false by (symmetry; apply Z.eqb_neq; apply NZ; left; reflexivity).
rewrite IH; [reflexivity|]. intros b' H'. apply NZ. right. exact H'.
Qed.

Lemma CALLS14 : (1 <= calls_of data <= 4)%nat.
Proof. unfold calls_of. destruct (Z.to_nat (cfglen_of data)); [lia|]. pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)). lia. Qed.

Lemma neq13 : Z_to_bv 64 1 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 1) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.
Lemma CFDS_1 : forall fds, CFDS fds0 fds -> fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros fds [_ H]. rewrite (H _ neq13). exact FD1. Qed.
Lemma vm_only_fds : forall md md', model_vm_only (cfg_model md) (cfg_model md') -> m_fds (cfg_model md') = m_fds (cfg_model md).
Proof. intros md md' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
Lemma vm_only_fs : forall md md', model_vm_only (cfg_model md) (cfg_model md') -> m_fs (cfg_model md') = m_fs (cfg_model md).
Proof. intros md md' (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.

Lemma heapA_munchT : forall A LB LM B m m' md W,
HEAPAx A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (forall a, fst iv <= a < snd iv -> cs_wide a))) W ->
HEAPAx A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | H2].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
Qed.

Lemma heapA_munchT6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n))) W ->
HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | [H2 | (b & n & HIN & H2 & H3)]].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
- right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma tr_enter : forall A LB LM FR (B : bud6) m md,
HEAPA6 A LB LM FR B m md -> 16 * TRV_BB <= QZsi.bQ B -> TRV_BB <= QZsi.bB B -> TRV_BB <= 512 * QZsi.bN B -> TR_BD <= QZsi.bD B ->
TR_BD <= 134217728 * QZsi.bM B ->
HEAPAx A LB LM FR (Bud TRV_BB TR_BD (QZsi.bM B)) m md.
Proof.
intros A LB LM FR B m md HP HQ HB HN HD HM. eapply (heapa5_enter A4L H6); [exact HP|].
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP) as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof RESTS6 as (R1 & R2 & R3). pose proof TGTB as (G1 & G2 & G3 & G4).
unfold blink. cbn [bB bD bM]. unfold TRV_BB, TR_BD in *. lia.
Qed.

Hypothesis LM0S : Z.of_nat (length LM0) < 8.

Section Loop.
Variables (buf cap : Z) (x5 x6 x7 x8 x9 x10 x11 : word) (K : TSet).
Hypothesis KN : K [].
Hypothesis Hcap : 65536 <= cap <= 2^26.
Hypothesis Hlen : len < cap.
Hypothesis FIT : 6 + cl <= len.

Hypothesis KOK : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (LK : list blk) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
TINVx 0 buf cap LK m' md' A' B' (zero_lines (Nat.pred (calls_of data))) ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp' (Z_to_bv 64 A_TP) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 cl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET_A) fc' None m' (seg_rom asegs)).

Record TI (i : nat) (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) : Prop := MKTI {
ti_mem  : drvA_mem argv USP m;
ti_heap : HEAPAx A (OWN al ++ (buf, cap) :: LK) LM0 [] B m md;
ti_bud  : Z.of_nat (calls_of data - i) * TGT_BB_A + 1024 <= bB B /\ Z.of_nat (calls_of data - i) * TGT_BD_A <= bD B;
ti_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
ti_pay  : bytes_at asegs m al payload;
ti_al   : (pl = 0 /\ al = EMPTY_A /\ ow = 0) \/ (0 < pl /\ ow = al);
ti_out  : match i with O => STDOUT0_A m | S _ => STDOUTW_A m i end;
ti_err  : STDERR0_A m;
ti_fds  : CFDS fds0 (m_fds (cfg_model md));
ti_fs   : m_fs (cfg_model md) = fs;
ti_stk  : stk asegs m LO TSP;
ti_frame: exists j0, rw_cells asegs m TSP (trun_frame j0 x5 x6 x7 buf);
ti_mfr  : exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN));
ti_aef  : rw_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]     }.

Definition tloop_stmt (i j : nat) : Prop :=
forall (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI i al ow LK m md A B -> frm0 fc ->
RZAx A md (match i with O => t_emit (W 1 (zero_lines 1)) K | S _ => K end)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 TLOOP_A) fc None m (seg_rom asegs)).

Lemma tloop_after : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
forall (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI (S i) al ow LK m md A B -> frm0 fc ->
RZAx A md K
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 EMIT_RET_A) fc None m (seg_rom asegs)).
Proof.
intros i j Hj Hij IH. intros until fc. intros TIH FRM.
pose proof TIH as [D HP HBUD (errv & ERR) PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS4.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold trun_frame in FRt.
d5_enter.
unfold EMIT_RET_A.
step. step. if_truex.
step. rewrite (unsigned_lit (Z.of_nat j)) by lia. rewrite swrap32_id by lia. step.

destruct (Nat.eq_dec j 1) as [J1|J2].
2:{
if_truex. evt_done5. replace (Z.of_nat j + -1) with (Z.of_nat (j - 1)) by lia.
apply (IH ltac:(lia) al ow LK m md A B); [exact TIH | exact FRM]. }

subst j. if_falsex. step. step. evt_done5.
assert (Hi : S i = calls_of data) by lia.
destruct HBUD as [HB1 HB2]. rewrite <- Hi in HB1, HB2. rewrite Nat.sub_diag in HB1, HB2. cbn [Z.of_nat] in HB1, HB2.

assert (EPI : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 : word) (F' : bvmap 5 word) (fc' : bv 32),
drvA_mem argv USP m' -> HEAPAx A' ((buf, cap) :: LK) LM0 [] B' m' md' -> 512 <= bB B' ->
(exists e, rw_cells asegs m' (A_TP - 164) [C4 e]) ->
STDOUTW_A m' (S i) -> STDERR0_A m' -> CFDS fds0 (m_fds (cfg_model md')) -> m_fs (cfg_model md') = fs ->
stk asegs m' LO TSP -> rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf) ->
rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN)) ->
rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 0)] ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 0x91d98) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 pl) (Z_to_bv 64 al) r w1 w2 w3 w4 w5 w6 w7
(Z_to_bv 64 ow) (Z_to_bv 64 (-1)) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 q3 q4 q5 q6)
F' (ret_pc (Z_to_bv 64 0x91d98)) fc' None m' (seg_rom asegs))).
{ intros m' md' A' B' q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 F' fc' D' HP' HB' ERR' SW' ERRP' Hfds' Hfs' ST' FRt' MFR' AEF'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.        unfold trun_frame in FRt'.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x91d98)) with (Z_to_bv 64 0x91d98 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. step.
match goal with |- context [Z_to_bv 64 (Z.land ?e 78)] => replace (Z_to_bv 64 (Z.land e 78)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
do 9 step. step. step.
evt_done5.
replace (ret_pc (Z_to_bv 64 TRUN_RET_A)) with (Z_to_bv 64 TRUN_RET_A : word) by (symmetry; apply ret_pc_even; [unfold TRUN_RET_A; lia| reflexivity]).
replace (TSP + 80) with SP by lia.
apply (KOK m' md' A' B' LK). rewrite <- Hi.
release_frame FRt' ST' (TSP + 80). replace (TSP + 80) with SP in ST' by lia.
constructor.
- exact D'.
- exact HP'.
- exact HB'.
- exact ERR'.
- exact ST'.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. exact MFR'.
- eapply (STDOUT_of_W A' _ _ _ _ m' md' (S i)); [lia | exact SW' | exact HP' | exact (CFDS_1 _ Hfds')].
- apply stderr_clean_of_pristine. exact ERRP'.
- exact Hfs'.
- lia.
- intros _. apply ro_of_rw. exact AEF'. }
assert (POST : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (cd : Z) (LBx : list blk) ms' (r : word),
ret_state A4H (Z_to_bv 64 0x91d98) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) (Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 ow) (Z_to_bv 64 (-1))
(Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') -> stk asegs m' LO TSP -> heap_pres A4H LBx TSP m m' ->
rw_cells asegs m' (A_TP - 164) [C4 errv] ->
HEAPAx A' ((buf, cap) :: LK) LM0 [] (charge B 512 cd) m' md' ->
RZAx A' md' K ms').
{ intros m' md' A' cd LBx ms' r RS VM ST' PRES ERR' HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
apply (EPI m' md' A' (charge B 512 cd)).
- eapply (drvA_mem_presT _ TSP m m'); [exact D | exact PRES | exact MI' | lia].
- exact HP'.
- cbn [bB charge]. lia.
- exists errv. exact ERR'.
- eapply STDOUTW_pres; [exact OUT | exact PRES | lia].
- unfold STDERR0_A, F_STDERR in *. eapply pristine_pres; [exact ERRP | exact PRES | intros; unfold cs_wide; lia | lia | lia].
- rewrite (vm_only_fds _ _ VM). exact Hfds.
- rewrite (vm_only_fs _ _ VM). exact Hfs.
- exact ST'.
- unfold trun_frame. eapply (heap_pres_rw_cells A4H); [exact PRES | exact FRt | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact PRES | exact MFR | left; cbn; lia].
- eapply aef_pres; [exact AEF | exact PRES]. }
destruct AL as [(A1 & A2 & A3)|(A1 & A2)].
-
subst ow. unfold OWN in HP. replace (pl =? 0) with true in HP by (symmetry; apply Z.eqb_eq; lia). cbn [app] in HP.
eapply (OBL_FREE_NN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A ((buf, cap) :: LK) LM0 [] B 0 LO errv UWptr HP);
[ left; reflexivity
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| lia | cbn [Z.eqb]; lia | ].
intros ms' m' md' A' r RS VM ST' PRES ERR' HP' REQ'. rewrite (lb_remove_zero _ _ _ _ _ _ _ HP) in PRES, HP'.
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR', PRES.
eapply POST; [exact RS | exact VM | exact ST' | exact PRES | exact ERR' | exact HP'].
-
subst ow. unfold OWN in HP. replace (pl =? 0) with false in HP by (symmetry; apply Z.eqb_neq; lia). cbn [app] in HP.
eapply (OBL_FREE_NN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A ((al, pl) :: (buf, cap) :: LK) LM0 [] B al LO errv UWptr HP);
[ right; exists pl; left; reflexivity
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| lia | destruct (al =? 0); cbn [uw_cost]; lia | ].
intros ms' m' md' A' r RS VM ST' PRES ERR' HP' REQ'.
replace (lb_remove al ((al, pl) :: (buf, cap) :: LK)) with ((buf, cap) :: LK) in * by (cbn [lb_remove blk_addr fst]; rewrite Z.eqb_refl; reflexivity).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR', PRES.
eapply POST; [exact RS | exact VM | exact ST' | exact PRES | exact ERR' | exact HP'].
Qed.

Lemma tloop_step : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
tloop_stmt i j.
Proof.
intros i j Hj Hij IH. unfold tloop_stmt. intros until fc. intros TIH FRM.
destruct TIH as [D HP HBUD (errv & ERR) PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS4.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INB : In (buf, cap) ((OWN al ++ (buf, cap) :: LK) ++ LM0)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP INB) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP INB) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.

assert (ALF : 0 < al /\ al + pl <= rc_ceil /\ (pl = 0 \/ (In (al, pl) (OWN al ++ (buf, cap) :: LK) /\ (al + pl <= 0x10000 \/ 0x647000 <= al)))).
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2)].
- subst al. unfold EMPTY_A. split; [lia | split; [lia | left; exact A1]].
- assert (INO : In (al, pl) (OWN al ++ (buf, cap) :: LK)).
{ apply in_or_app; left. unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left; reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ al pl HP ltac:(apply in_or_app; left; exact INO)) as (_ & _ & Apos & Ahi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ al pl HP ltac:(apply in_or_app; left; exact INO)) as Aimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Aimg. unfold alloc_ceiling in Ahi.
split; [lia | split; [lia | right; split; [exact INO | lia]]]. }
destruct ALF as (AL1 & AL2 & AL3).
unfold trun_frame in FRt.
assert (PLEN : Z.of_nat (length payload) = pl) by (rewrite length_skipn; lia).
d5_enter.
unfold TLOOP_A, ADAPTER_FLAG. unfold ADAPTER_FLAG in AL.

pose proof (conj PAY ERR) as KEEP. clear PAY ERR.
pose proof (munch_refl [(AEF_FLAG_A, AEF_FLAG_A + 1)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. unfold AEF_FLAG_A in MU1, AEF.
step. stepz.
step. step. step. evt_done5.
destruct KEEP as [PAY ERR].
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (D1 : drvA_mem argv USP mx) by (eapply drvA_mem_munchT; [exact D | exact MU1 | exact WM1 | exact MI |]; unfold twin; ivs_lia) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HP1 : HEAPAx A (OWN al ++ (buf, cap) :: LK) LM0 [] B mx md)
by (eapply heapA_munchT; [exact HP | exact MU1 | exact WM1 | exact MI |]; constructor; [| constructor]; cbn [fst snd]; split; [lia | right; intros; unfold cs_wide; lia]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (ERR1 : rw_cells asegs mx (A_TP - 164) [C4 errv]) by (eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]; cbn [disjoint_from cells_size csize Nat.add]; unfold A_TP; lia) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (PAY1 : bytes_at asegs mx al payload)
by (eapply bytes_at_transport; [exact PAY | exact MU1 |]; rewrite length_skipn; cbn [disjoint_from]; unfold EMPTY_A in AL; split; [lia | exact I]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (ERRP1 : STDERR0_A mx) by (unfold STDERR0_A, F_STDERR in *; eapply pristine_munch; [exact ERRP | exact MU1 | ivs_lia | lia | lia]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OUT1 : match i with O => STDOUT0_A mx | S _ => STDOUTW_A mx i end);
[ destruct i as [|ipp];
[ unfold STDOUT0_A, F_STDOUT in *; destruct OUT as [O1 O2]; split;
[ eapply pristine_munch; [exact O1 | exact MU1 | ivs_lia | lia | lia] | eapply pristine_munch; [exact O2 | exact MU1 | ivs_lia | lia | lia] ]
| eapply STDOUTW_agree; [exact OUT | intros x Hx; apply MU1; unfold F_STDOUT, STDOUT_BUF in Hx; rewrite wa_unsigned by lia; cbn [outside fst snd]; lia | lia] ]
| ]
end.
unfold ADAPTER_FLAG.
assert (BB1 : TGT_BB_A <= bB B /\ TGT_BD_A <= bD B).
{ destruct HBUD as [HB1 HB2]. assert (X : 1 <= Z.of_nat (calls_of data - i)) by lia. nia. }
eapply (TGT (Z_to_bv 64 TCALL_RET_A) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 al) (Z_to_bv 64 pl) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6
F fc _ md _ A (OWN al ++ (buf, cap) :: LK) LM0 B al pl LO payload errv);
[ exact HP1 | exact (proj1 BB1) | exact (proj2 BB1) | exact PAY1 | exact PLEN | lia | lia | unfold alloc_ceiling; lia
| destruct AL3 as [X|[X _]]; [left; exact X | right; exact X]
| exact LM0S
| exact (dm_loc _ _ _ D1) | exact (lock_of_dm _ D1) | exact (OBL_GA_of _ _ _ _ _ _ _ D1 HP1)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | exact (proj2 TOPF) | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR1 | reflexivity | unfold TCALL_RET_A; rewrite unsigned_lit by lia; reflexivity | reflexivity | exact FRM | reflexivity | reflexivity | ].

intros ms' m' md' A' B' errv' gp' LK' RSW VM ST' PRESX LOCC' LOCK' ERR' GA' HP' HBB HBD.
destruct RSW as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS & FRM').
specialize (FRM' FRM). cbn [hl_tp A4H] in ERR'. rewrite unsigned_lit in ST', PRESX by lia.
rewrite <- app_assoc in HP'. cbn [app] in HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (AEF' : rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 1)]) by (eapply aef_presx; [unfold AEF_FLAG_A; exact AEF | exact PRESX]).

cbn [hl_segs hla_base A4L A4H] in MI'.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presx _ TSP _ m'); [exact D1 | exact PRESX | exact LOCC' | exact MI' | lia]).
assert (PAY' : bytes_at asegs m' al payload).
{ destruct AL3 as [A0|(INO & AIMG)].
- destruct PAY1 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
- eapply (heap_presx_bytes_at A4H); [exact PRESX | exact PAY1 |]. right; right. exists (al, pl). split; [apply in_or_app; left; exact INO | cbn; rewrite length_skipn; lia]. }
assert (ERRP' : STDERR0_A m').
{ unfold STDERR0_A, F_STDERR in *. eapply pristine_presx; [exact ERRP1 | exact PRESX | | lia | lia].
intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia. }
assert (OUT' : match i with O => STDOUT0_A m' | S _ => STDOUTW_A m' i end).
{ destruct i as [|i'].
- unfold STDOUT0_A, F_STDOUT in *. destruct OUT1 as [O1 O2]. split.
+ eapply pristine_presx; [exact O1 | exact PRESX | | lia | lia]. intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia.
+ eapply pristine_presx; [exact O2 | exact PRESX | | lia | lia]. intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia.
- eapply STDOUTW_presx; [exact OUT1 | exact PRESX | lia | lia]. }
assert (FRt' : rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf)) by (unfold trun_frame; eapply (heap_presx_rw_cells A4H); [exact PRESX | exact FRt | left; lia]).
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) by (eapply (heap_presx_rw_cells A4H); [exact PRESX | exact MFR | left; lia]).
pose proof (vm_only_fds _ _ VM) as FDS'. pose proof (vm_only_fs _ _ VM) as FS'.
cbn [hl_segs hla_base A4L A4H] in MI'.
d5_enter.
replace (ret_pc (Z_to_bv 64 TCALL_RET_A)) with (Z_to_bv 64 TCALL_RET_A : word) by (symmetry; apply ret_pc_even; [unfold TCALL_RET_A; lia| reflexivity]).
unfold TCALL_RET_A, ADAPTER_FLAG. step.

pose proof (conj PAY' ERR') as KEEP. clear PAY' ERR'.
pose proof (munch_refl [(AEF_FLAG_A, AEF_FLAG_A + 1)] m') as MU3. pose proof (wmono_refl asegs m') as WM3. unfold AEF_FLAG_A in MU3, AEF'.
stepz.
step. step. apply evt_done.
destruct KEEP as [PAY' ERR'].
change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (D3 : drvA_mem argv USP mx) by (eapply drvA_mem_munchT; [exact D' | exact MU3 | exact WM3 | exact MI' |]; unfold twin; ivs_lia) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (HP3 : HEAPAx A' (OWN al ++ (buf, cap) :: LK ++ LK') LM0 [] B' mx md')
by (eapply heapA_munchT; [exact HP' | exact MU3 | exact WM3 | exact MI' |]; constructor; [| constructor]; cbn [fst snd]; split; [lia | right; intros; unfold cs_wide; lia]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (ERR3 : rw_cells asegs mx (A_TP - 164) [C4 errv']) by (eapply rw_cells_transport; [exact ERR' | exact MU3 | exact WM3 |]; cbn [disjoint_from cells_size csize Nat.add]; unfold A_TP; lia) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (PAY3 : bytes_at asegs mx al payload)
by (eapply bytes_at_transport; [exact PAY' | exact MU3 |]; rewrite length_skipn; cbn [disjoint_from]; unfold EMPTY_A in AL; split; [lia | exact I]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (ERRP3 : STDERR0_A mx) by (unfold STDERR0_A, F_STDERR in *; eapply pristine_munch; [exact ERRP' | exact MU3 | ivs_lia | lia | lia]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (OUT3 : match i with O => STDOUT0_A mx | S _ => STDOUTW_A mx i end);
[ destruct i as [|ipp];
[ unfold STDOUT0_A, F_STDOUT in *; destruct OUT' as [O1 O2]; split;
[ eapply pristine_munch; [exact O1 | exact MU3 | ivs_lia | lia | lia] | eapply pristine_munch; [exact O2 | exact MU3 | ivs_lia | lia | lia] ]
| eapply STDOUTW_agree; [exact OUT' | intros x Hx; apply MU3; unfold F_STDOUT, STDOUT_BUF in Hx; rewrite wa_unsigned by lia; cbn [outside fst snd]; lia | lia] ]
| ]
end.
clear D' HP' ERRP' OUT' D1 HP1 ERRP1 OUT1 PAY1 ERR1 MU1 WM1 MU3 WM3.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] => rename mx into m3 end.

assert (AFTER : forall (m2 : word -> option byte) (F2 : bvmap 5 word) (fc2 : bv 32) (cf2 : config) (ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 : word),
munch (PFW_OUT LO TSP) m3 m2 -> wmono asegs m3 m2 -> mem_inv asegs m2 -> stk asegs m2 LO TSP ->
STDOUTW_A m2 (S i) -> (frm0 fc' -> frm0 fc2) ->
(forall LBx Bx mx, HEAPAx A' LBx LM0 [] Bx mx md' -> HEAPAx A' LBx LM0 [] Bx mx cf2) -> same_io md' cf2 ->
RZAx A' cf2 K
(MS (mkR ra' (Z_to_bv 64 TSP) gp' (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 pl) (Z_to_bv 64 al) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 q3 q4 q5 q6)
F2 (Z_to_bv 64 EMIT_RET_A) fc2 None m2 (seg_rom asegs))).
{ intros m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 HPX [SX1 SX2].
refine (tloop_after i j Hj Hij IH al ow (LK ++ LK') m2 cf2 A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 _ (FRM2 FRM')).
unfold PFW_OUT, F_STDOUT, STDOUT_BUF in MU2.
constructor.
- eapply drvA_mem_munchT; [exact D3 | exact MU2 | exact WM2 | exact MI2 |]. unfold twin. ivs_lia.
- apply HPX. eapply heapA_munchT; [exact HP3 | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia] | split; [lia | right; intros; unfold cs_wide; lia]].
- destruct HBUD as [HB1 HB2]. replace (Z.of_nat (calls_of data - S i)) with (Z.of_nat (calls_of data - i) - 1) by lia. nia.
- exists errv'. eapply rw_cells_transport; [exact ERR3 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- destruct AL3 as [A0|(INO & AIMG)].
+ destruct PAY3 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
+ eapply bytes_at_transport; [exact PAY3 | exact MU2 |]. rewrite length_skipn. cbn [disjoint_from]. repeat split; lia.
- exact AL.
- exact SW2.
- unfold STDERR0_A, F_STDERR in *. eapply pristine_munch; [exact ERRP3 | exact MU2 | ivs_lia | lia | lia].
- rewrite SX1, FDS'. exact Hfds.
- rewrite SX2, FS'. exact Hfs.
- exact ST2.
- exists j0. unfold trun_frame. eapply rw_cells_transport; [exact FRt' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. eapply rw_cells_transport; [exact MFR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
- eapply aef_munch; [exact AEF' | exact MU2 | exact WM2 | unfold PFW_OUT, F_STDOUT, STDOUT_BUF, AEF_FLAG_A; ivs_lia]. }

pose proof (PFIMG_of _ _ _ _ _ _ _ D3 HP3) as IMG'. pose proof (OBL_PFRT _ _ _ _ _ _ _ HP3) as RT'. pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP3) as HCK3.
destruct i as [|i'].
-
eapply PF1; [exact HCK3 | rewrite FDS'; exact (CFDS_1 _ Hfds) | exact OUT3 | exact IMG' | exact RT'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | pose proof OBL_PFLO; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI' | exact FRM' | exact KN |].
intros ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F2 fc2 m2 cf2 MU2 WM2 MI2 ST2 SW2 FS2 FRM2 HN2 SIO2.
rewrite unsigned_lit in MU2, ST2 by lia.
refine (AFTER m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 (fun _ _ _ HX => heapA_cfg_next A4L HIx _ _ _ _ _ _ _ _ HX HN2) SIO2 _). gp5_solve.
-
eapply (PFK (S i')); [exact HCK3 | lia | exact OUT3 | exact IMG' | exact RT'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | pose proof OBL_PFLO; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI' | exact FRM' | exact KN |].
intros ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F2 fc2 m2 cf2 MU2 WM2 MI2 ST2 SW2 FS2 FRM2 HN2 SIO2.
rewrite unsigned_lit in MU2, ST2 by lia.
refine (AFTER m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 (fun _ _ _ HX => heapA_cfg_next A4L HIx _ _ _ _ _ _ _ _ HX HN2) SIO2 _). gp5_solve.
Qed.
Lemma tloop_all : forall j i, (1 <= j)%nat -> (i + j = calls_of data)%nat -> tloop_stmt i j.
Proof.
induction j as [|j IHj]; intros i Hj Hij; [lia|].
apply tloop_step; [exact Hj | exact Hij |]. intros H2. replace (S j - 1)%nat with j by lia. apply IHj; lia.
Qed.

Definition twin2 (iv : Z * Z) : Prop := twin iv \/ (fst iv <= snd iv /\ snd iv <= 0x10000).
Lemma drvA_mem_munchT2 : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall twin2 W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x647000 /\ ~ (0x614810 <= x < 0x624840 /\ x <> 0x624810) /\ ~ (0xecd40 <= x < 0xece28) /\ ~ (0xece30 <= x < 0xecf18) /\ ~ (0x645ca0 <= x < 0x6460b0))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right; lia] |].
right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold twin2, twin in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [H1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply drvA_mem_agreeL; [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold twin2, twin in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [H1 FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Record PRE1 (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKP1 {
p_mem  : drvA_mem argv USP m1;
p_heap : HEAPA6 A [(buf, cap)] LM0 [] B m1 md;
p_req  : reqA A <= 2^20 + 2 * cap;
p_bud  : TR_BQ <= QZsi.bQ B /\ TR_BB <= QZsi.bB B /\ 512 + TRV_BB <= 512 * QZsi.bN B /\ TR_BD <= QZsi.bD B
/\ TR_BD <= 134217728 * QZsi.bM B;
p_errno: exists errv, rw_cells asegs m1 (A_TP - 164) [C4 errv];
p_blk  : exists junk, rw_cells asegs m1 buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk];
p_out  : STDOUT0_A m1;
p_err  : STDERR0_A m1;
p_fds  : CFDS fds0 (m_fds (cfg_model md));
p_fs   : m_fs (cfg_model md) = fs;
p_stk  : stk asegs m1 LO TSP;
p_frame: exists j0, rw_cells asegs m1 TSP (trun_frame j0 x5 x6 x7 buf);
p_mfr  : exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m1 SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN));
p_aef  : rw_cells asegs m1 AEF_FLAG_A [C1 (Z_to_bv 8 0)]     }.

Lemma seg_empty : forall (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A B -> frm0 fc -> pl = 0 ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91d48) fc None m1 (seg_rom asegs)).
Proof.
intros until fc. intros P FRM PL0. destruct P as [D HP6 REQ HBUD (errv & ERR) (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) MFR AEF0].
destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold TR_BQ in HQ1. unfold TR_BB in HB1.
pose proof (tr_enter _ _ _ _ _ _ _ HP6 ltac:(unfold TRV_BB in *; lia) ltac:(unfold TRV_BB in *; lia) ltac:(lia) HB2 HM1) as HP.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof CALLS14 as CALLS. pose proof TGTB as (G1 & G2 & G3 & G4).
d5_enter.
step. step. step. step. evt_done5.
unfold ADAPTER_FLAG. replace (6440976 + 16) with EMPTY_A by reflexivity.
apply (tloop_all (calls_of data) 0 ltac:(lia) eq_refl EMPTY_A 0 [] m1 md A (Bud TRV_BB TR_BD (QZsi.bM B))); [| exact FRM].
constructor; [exact D | | | exists errv; exact ERR | | left; split; [exact PL0 | split; reflexivity] | exact OUT | exact ERRP | exact Hfds | exact Hfs | exact ST | exists j0; exact FRt | exact MFR | exact AEF0].
- unfold OWN. rewrite PL0. cbn [Z.eqb app]. exact HP.
- cbn [bB bD]. unfold TRV_BB, TR_BD. rewrite Nat.sub_0_r.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BB_A ltac:(lia) ltac:(lia)) as X1.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BD_A ltac:(lia) ltac:(lia)) as X2. lia.
- replace (skipn (Z.to_nat (6 + cfglen_of data)) data) with (@nil byte) by (symmetry; apply skipn_all2; lia).
unfold EMPTY_A. split; [cbn; lia|]. split; [cbn; lia|]. intros k Hk. cbn in Hk. lia.
Qed.

Lemma seg_alloc : forall (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A B -> frm0 fc -> 0 < pl ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 TALLOC_A) fc None m1 (seg_rom asegs)).
Proof.
intros until fc. intros P FRM PLP. destruct P as [D HP6 REQ HBUD (errv & ERR) (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF0].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
unfold trun_frame in FRt. destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold TR_BQ in HQ1. unfold TR_BB in HB1.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). pose proof RESTS6 as (RSa & RSb & RSc).
assert (TRV0 : 0 <= TRV_BB) by (unfold TRV_BB; lia).
assert (ACP : acostA pl <= 3 * 67108864 + 45101) by (unfold acostA; destruct (Z.leb_spec pl 64512); lia).
d5_enter.
unfold TALLOC_A. step. step. evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md _ A [(buf, cap)] LM0 [] B pl LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | lia | cbn [uw_cost]; unfold TR_BD in HB2; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk2 & NB) HP6' REQ'.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _). unfold alloc_ceiling in Rhi.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(left; reflexivity)) as Rimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Rimg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP') as ND. cbn [map blk_addr fst app] in ND.
assert (NE : r <> buf) by (inversion ND; subst; cbn in *; intros E; subst; tauto).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r pl buf cap HP' ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presT _ TSP m1 m'); [exact D | exact PRES | exact MI' | lia]).
assert (BLK' : rw_cells asegs m' buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact BLK |]. right; right. exists (buf, cap). split; [left; reflexivity | cbn; lia]. }

pose proof BLK' as [[[WFb _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].
assert (SRC : bytes_at asegs m' (buf + 6 + cl) payload).
{ destruct BA as (B1 & B2 & B3). split; [lia|]. split; [rewrite length_skipn; lia|]. intros k Hk. rewrite length_skipn in Hk.
replace (buf + 6 + cl + Z.of_nat k) with (buf + Z.of_nat (Z.to_nat (6 + cl) + k)) by lia. rewrite B3 by lia.
rewrite nth_error_skipn. reflexivity. }
assert (OUT' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT in *. destruct OUT as [O1 O2]. split; (eapply pristine_pres; [eassumption | exact PRES | intros; unfold cs_wide; lia | lia | lia]). }
assert (ERRP' : STDERR0_A m').
{ unfold STDERR0_A, F_STDERR in *. eapply pristine_pres; [exact ERRP | exact PRES | intros; unfold cs_wide; lia | lia | lia]. }
assert (FRt' : rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf)) by (unfold trun_frame; eapply (heap_pres_rw_cells A4H); [exact PRES | exact FRt | left; lia]).
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) by (eapply (heap_pres_rw_cells A4H); [exact PRES | exact MFR | left; lia]).
assert (AEF' : rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 0)]) by (eapply aef_pres; [exact AEF0 | exact PRES]).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP') as RT'.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(apply in_or_app; left; left; reflexivity)) as RAPP.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as BAPP.
cbn [hl_sb A4L] in RAPP, BAPP.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x91d04)) with (Z_to_bv 64 0x91d04 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step. step. step. step.

change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
assert (APP : 64 < pl -> app_mem r pl /\ app_mem (buf + 6 + cl) pl).
{ intros Hn64. unfold A_SB in RAPP, BAPP. replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in RAPP, BAPP by reflexivity.
unfold app_mem, A_SB, A_HMB. split; (split; [lia|]); [destruct RAPP as [X|X]; [left; lia | right; lia] | destruct BAPP as [X|X]; [left; lia | right; lia]]. }
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := r) (s := buf + 6 + cl) (n := pl) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | right; left; reflexivity | lia | lia | lia]
| exact RT'
| lia | lia | lia | lia
| exact APP
| lia | lia
| reflexivity | reflexivity | reflexivity | lia | lia
| exact NB | exact SRC | rewrite length_skipn; lia
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
clear APP. rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 DST2 SRC2 ST2.
replace (ret_pc (Z_to_bv 64 0x91d18)) with (Z_to_bv 64 0x91d18 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (HP26 : HEAPA6 A' ((r, pl) :: [(buf, cap)]) LM0 [] (QZsi.chargeQ (QZsi.charge B (acostA pl) (uw_cost UWptr) 1) (pl + 8192)) m2 md').
{ eapply heapA_munchT6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling.
- split; [lia | right; right; exists r, pl; split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }

assert (HP2 : HEAPAx A' ((r, pl) :: [(buf, cap)]) LM0 [] (Bud TRV_BB TR_BD (QZsi.bM B)) m2 md').
{ pose proof (tr_enter _ _ _ _ _ _ _ HP26) as E. cbn [QZsi.bQ QZsi.bB QZsi.bN QZsi.bD QZsi.bM QZsi.charge QZsi.chargeQ uw_cost] in E.
apply E; lia. }
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP2) as HCK2.      step. step. step. step. evt_done5.
apply (tloop_all (calls_of data) 0 ltac:(lia) eq_refl r r [] m2 md' A' (Bud TRV_BB TR_BD (QZsi.bM B))); [| exact FRM].
constructor.
- eapply drvA_mem_munchT2; [exact D' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold twin2, twin; cbn [fst snd]; [destruct Rimg as [X|X]; [right; lia | left; lia] | left; lia].
- unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app]. exact HP2.
- cbn [bB bD]. unfold TRV_BB, TR_BD. rewrite Nat.sub_0_r.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BB_A ltac:(lia) ltac:(lia)) as X1.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BD_A ltac:(lia) ltac:(lia)) as X2. lia.
- exists errv'. eapply rw_cells_transport; [exact ERR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- destruct DST2 as [[_ BA2] _]. cbn [cells_bytes cbytes app] in BA2. rewrite app_nil_r in BA2. exact BA2.
- right. split; [lia | reflexivity].
- unfold STDOUT0_A, F_STDOUT in *. destruct OUT' as [O1 O2]. split; (eapply pristine_munch; [eassumption | exact MU2 | ivs_lia | lia | lia]).
- unfold STDERR0_A, F_STDERR in *. eapply pristine_munch; [exact ERRP' | exact MU2 | ivs_lia | lia | lia].
- rewrite (vm_only_fds _ _ VM). exact Hfds.
- rewrite (vm_only_fs _ _ VM). exact Hfs.
- exact ST2.
- exists j0. unfold trun_frame. eapply rw_cells_transport; [exact FRt' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. eapply rw_cells_transport; [exact MFR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
- eapply rw_cells_transport; [exact AEF' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold AEF_FLAG_A. repeat split; first [lia | destruct Rimg as [X|X]; lia].
Qed.
End Loop.

Theorem trun_ok : trun_stmt H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST.
Proof.
unfold trun_stmt. intros until fc. intros HI FIT FRM KN KOK.
destruct HI as [[D S0] HP6 REQ Hcap Hlen (junk & BLK) (errv & ERR) ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) Hfds Hfs (HQ1 & HB1 & HN1 & HB2 & HM1)].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof RESTS as [RB1 RB2]. pose proof RESTS6 as (RSa & RSb & RSc).
rc_lia_prep. unfold alloc_ceiling in L1. unfold A_TP in ERR.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.

unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xecd40, 0xece28) ltac:(cbn; tauto)) as PE. pose proof (proj1 (Forall_forall _ _) S0 (0xece30, 0xecf18) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x645ca0, 0x6460b0) ltac:(cbn; tauto)) as PO2. pose proof (proj1 (Forall_forall _ _) S0 (0x624810, 0x624840) ltac:(cbn; tauto)) as PA.
cbn [fst snd] in PE, PO1, PO2, PA.
assert (FLAG : rw_cells asegs m ADAPTER_FLAG [C1 (Z_to_bv 8 0)]).
{ unfold ADAPTER_FLAG. eapply (rw_cells_pristine_recast m 0x624810 [Z_to_bv 8 0]);
[eapply pristine_sub; [exact PA | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity | exact I] | reflexivity | reflexivity]. }
pose proof (llvminit_of_dm _ _ _ _ _ _ _ HP) as GOTC. unfold GOT_LLVMINIT in GOTC.

assert (AEFc : rw_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]).
{ unfold AEF_FLAG_A. eapply (rw_cells_pristine_recast m 0x624814 [Z_to_bv 8 0]);
[eapply pristine_sub; [exact PA | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity | exact I] | reflexivity | reflexivity]. }
unfold AEF_FLAG_A in AEFc.
destruct (dm_atexit _ _ _ D) as (mid & ATX & MIDL).
assert (PH1 : ax_phase m = 1).
{ unfold ax_phase. replace (m (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) by (symmetry; exact (PA ADFLAG_A ltac:(unfold ADFLAG_A; lia))). reflexivity. }
unfold atexit_cells in ATX. rewrite PH1 in ATX. unfold atexit_cellsK, ATEXIT_A in ATX. cbn [Z.eqb Pos.eqb] in ATX.
pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL0. cbn [hl_libc hla_base A4L A4H] in NL0.
assert (NL : ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)]) by (unfold NEEDLOCKS_A; split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact NL0]). clear NL0. unfold NEEDLOCKS_A in NL.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(USP - 208, USP - 128); (ADAPTER_FLAG, ADAPTER_FLAG + 1)] m) as MU.
unfold ADAPTER_FLAG in FLAG, MU. unfold A_TP in ERR.
pose proof (conj BLK ERR) as KEEP. clear BLK.
d5_enter.
unfold TRUN_A. carve_frame 80%nat ST.

replace (USP + -128 + -80) with (USP + -208) in * by lia.
do 10 step.
do 3 step.
step. step.
step.
step. step.
change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_truex.
step. stepz.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (atexit_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc LO mid);
[ exact MI | rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | exact MIDL
| unfold atexit_cellsK, ATEXIT_A; cbn [Z.eqb Pos.eqb]; exact ATX | exact NL | unfold AEF_GUARD_A; reflexivity ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3 & ST3 & AT3).
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold ATEXIT_A in MUc.
destruct KEEP as [BLK ERR0].
lazymatch type of MU with munch _ _ ?m2 =>
lazymatch type of MUc with munch ?Wc _ _ =>
lazymatch type of MU with munch ?W0 _ _ =>
assert (MU' : munch (W0 ++ Wc) m m3) by (eapply QjDJ.munch_join; [exact MU | exact MUc | |]; intros x Hx; cbn [outside app] in Hx |- *; lia);
assert (WM' : wmono asegs m m3) by (eapply wmono_trans; [exact WM | exact WMc]);
cbn [app] in MU'; clear ATX MU WM; transport_after_call rsegs m2 m3 MUc WMc
end end end.
clear MUc WMc. rename MU' into MU. rename WM' into WM.
replace (ret_pc (Z_to_bv 64 0x91d34)) with (Z_to_bv 64 0x91d34 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_truex.
step. step.
step. if_truex.

assert (P1 : PRE1 buf cap s5 s6 s7 m3 md A B).
{ pose proof (USPF) as (U1' & _). constructor.
- eapply (drvA_mem_register m m3 mid); [exact D | | | | exact MI3 | exact AT3 | exact MIDL | ].
+ intros x Hx HC HF HA. apply MU. rewrite wa_unsigned by lia.
pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; unfold ADFLAG_A, ATEXIT_A in *; cbn [outside fst snd app]; lia.
+ intros x HC Hw. apply WM. exact Hw.
+ eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. repeat split; lia.
+ eapply flag_written. exact FLAG.
- eapply heapA_munchT6; [exact HP6 | exact MU | exact WM | exact MI3 |].
unfold alloc_ceiling. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia | first [left; lia | right; left; intros; unfold cs_wide; lia]]).
- exact REQ.
- repeat split; lia.
- exists errv. eapply rw_cells_transport; [exact ERR0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- exists junk. eapply rw_cells_transport; [exact BLK | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?length_app. repeat split; first [lia | destruct Bimg as [X|X]; lia].
- unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]).
- unfold STDERR0_A, F_STDERR. eapply pristine_munch; [exact PE | exact MU | ivs_lia | lia | lia].
- exact Hfds.
- exact Hfs.
- exact ST3.
- eexists. unfold trun_frame. exact FR.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. exact MFR.
- unfold AEF_FLAG_A. exact AEFc. }

assert (BLK3 : rw_cells asegs m3 buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?length_app. repeat split; first [lia | destruct Bimg as [X|X]; lia]. }
pose proof BLK3 as [[[WFb _] BAb] _]. cbn [cells_bytes cbytes app] in BAb. apply bytes_at_app in BAb as [BAb _].
pose proof (bytes_at_read asegs _ buf data 2 1 BAb ltac:(lia) ltac:(lia)) as HR2.
change (Z.to_nat 2) with 2%nat in HR2. rewrite (nth_read 2%nat data (Z_to_bv 8 0)) in HR2 by lia.
pose proof (bv_unsigned_in_range 8 (nth 2 data (Z_to_bv 8 0))) as R2. unfold bv_modulus in R2. cbn in R2. fold (hb data 2) in R2.

assert (DISPATCH : forall (mx : word -> option byte) (rav q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w3 q3 q4 q5 q6 : word) (pcz : Z),
PRE1 buf cap s5 s6 s7 mx md A B -> (pcz = 0x91d44 \/ pcz = 0x91cf8) ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR rav (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) q0 q1 q2
(Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 cl) w3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 pcz) fc None mx (seg_rom asegs))).
{ intros mx rav q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w3 q3 q4 q5 q6 pcz P1x Hpc.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ (p_heap _ _ _ _ _ _ _ _ _ P1x))) as HCKx.
d5_enter.
destruct (Z.eq_dec pl 0) as [PL0|PLP].
- destruct Hpc as [-> | ->]; step; [if_falsex | if_truex]; evt_done5;
(eapply (seg_empty buf cap s5 s6 s7 s8 s9 s10 s11 K KN Hcap Hlen FIT KOK); [exact P1x | exact FRM | exact PL0]).
- destruct Hpc as [-> | ->]; step; [if_truex | if_falsex]; evt_done5; unfold TALLOC_A;
(eapply (seg_alloc buf cap s5 s6 s7 s8 s9 s10 s11 K KN Hcap Hlen FIT KOK); [exact P1x | exact FRM | lia]). }
step.
destruct (Z.eq_dec cl 0) as [CL0|CLP].
-
if_truex. step. evt_done5.
replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat (calls_of data)) : word) by (unfold calls_of; rewrite CL0; reflexivity).
eapply DISPATCH; [exact P1 | left; reflexivity].
-
if_falsex. step. step. step. evt_done5.
unfold zxb. fold (hb data 2).
match goal with |- context [Z_to_bv 64 ?e] =>
lazymatch e with context [Z.land] =>
replace e with (Z.of_nat (calls_of data));
[| unfold calls_of; destruct (Z.to_nat (cfglen_of data)) eqn:E; [lia|];
rewrite !unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4;
pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)); lia] end end.
eapply DISPATCH; [exact P1 | right; reflexivity].
Qed.
End Target.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGcC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS67.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS67. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPra.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLlx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLlx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTmr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTmr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtWm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtWm.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= QlES.mkr__zify_pre_hook_0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition TLOOP_A : Z := 0x91980.
Definition TCALL_RET_A : Z := 0x91994.
Definition EMIT_RET_A : Z := 0x919a4.
Definition TDISP_A : Z := 0x91910.
Definition TALLOC_A : Z := 0x91924.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma pristine_munch : forall m m' lo hi W, pristine m lo hi -> munch W m m' ->
Forall (fun iv => snd iv <= lo \/ hi <= fst iv) W -> 0 <= lo -> hi <= 2^64 -> pristine m' lo hi.
Proof.
intros m m' lo hi W P MU FW H0 H1 a Ha. rewrite <- (P a Ha). apply MU. rewrite wa_unsigned by lia.
clear - FW Ha. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in FW as [F1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW].
Qed.

Lemma STDOUTW_agree : forall m m' k, STDOUTW_A m k ->
(forall x, (F_STDOUT <= x < F_STDOUT + 232 \/ STDOUT_BUF <= x < STDOUT_BUF + 1024) -> m' (wa x) = m (wa x)) -> (k <= 4)%nat -> STDOUTW_A m' k.
Proof.
intros m m' k SW E Hk. exact (QscU.Mq2.stdoutw_agree m m' k SW E).
Qed.

Lemma bytes_at_agreeT : forall (m m' : word -> option byte) a bs,
bytes_at asegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at asegs m' a bs.
Proof.
intros m m' a bs (H1 & H2 & H3) E. split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold mrd in *. rewrite E by lia. apply H3. exact Hi.
Qed.

Section Target.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_MALLOC_N6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CLIENT_FRAME : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.
Hypothesis OBL_CLIENT_FRAME6 : forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Notation TSP := (USP - 208).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variables (BB_REST BD_REST : Z).
Variables (BQ_REST BN_REST : Z).

Variable GA : (word -> option byte) -> Prop.
Variables (TGT_STACK_A TGT_BB_A TGT_BD_A : Z).
Hypothesis TGT : target_A_stmt HIx GA TGT_STACK_A TGT_BB_A TGT_BD_A.

Hypothesis OBL_GA_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> GA m.
Hypothesis TGTB : 0 <= TGT_STACK_A /\ LO + TGT_STACK_A <= USP - 208 /\ 0 <= TGT_BB_A /\ 0 <= TGT_BD_A.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis PF1 : emitpf1_stmt Jx PFRT PFLO.
Hypothesis PFK : emitpfk_stmt Jx PFRT PFLO.

Definition TRV_BB : Z := 1536 + 4 * TGT_BB_A.

Definition TR_BB : Z := (3 * 67108864 + 45101) + TRV_BB.
Definition TR_BD : Z := 4 * TGT_BD_A.
Definition TR_BQ : Z := (67108864 + 8192) + 16 * TRV_BB.
Hypothesis RESTS : TR_BB <= BB_REST /\ TR_BD <= BD_REST.
Hypothesis RESTS6 : TR_BQ <= BQ_REST /\ 512 + TRV_BB <= 512 * BN_REST /\ TRV_BB <= 2^30.

Notation len := (Z.of_nat (length data)).
Notation cl := (cfglen_of data).
Notation pl := (Z.of_nat (length data) - 6 - cfglen_of data).
Notation payload := (skipn (Z.to_nat (6 + cfglen_of data)) data).
Notation TINVx := (TINV HIx argv USP LO fs LM0).

Definition trun_frame (j0 : list byte) (s5v s6v s7v : word) (buf : Z) : list cell :=
[CB 8 j0; C8 s7v; C8 s6v; C8 s5v; C8 (Z_to_bv 64 pl); C8 (Z_to_bv 64 (buf + 6 + cl)); C8 (Z_to_bv 64 cl);
C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 (buf + 2)); C8 (Z_to_bv 64 TRUN_RET_A)].

Definition OWN (al : Z) : list blk := if pl =? 0 then [] else [(al, pl)].

Lemma lock_of_dm : forall m, drvA_mem argv USP m -> rw_cells asegs m T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)].
Proof.
intros m D. pose proof (dm_pris _ _ _ D) as P. pris_get P 0x643160 0x6431e0. unfold T_LOCALE_LOCK_A.
eapply (rw_cells_pristine_recast m 0x6431d0 (le4 (Z_to_bv 64 0)));
[ eapply pristine_sub; [exact PR | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity|exact I] | reflexivity | reflexivity ].
Qed.

Lemma llvminit_of_dm : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)].
Proof.
intros A LB LM FR B m md HP. pose proof (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) as P. unfold GOT_LLVMINIT.
rtcR_cell P 0xe6a28 (le8 (Z_to_bv 64 0x0)).
Qed.

Lemma PFIMG_of : forall A LB LM FR B m md, drvA_mem argv USP m -> HEAPAx A LB LM FR B m md -> PFIMG_A m.
Proof.
intros A LB LM FR B m md D HP. split; [exact (dm_pris _ _ _ D) | split; [exact (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) | split]].
- destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (g & G1 & G2 & G3). cbn [hl_got_guard hl_guard hl_tp hla_base A4L A4H] in G1, G2, G3.
exists g. split; [exact G1 | split; [exact G2 | exact G3]].
- pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL. cbn [hl_libc hla_base A4L A4H] in NL. exact NL.
Qed.

Lemma stderr_clean_of_pristine : forall m, STDERR0_A m -> exists wp rp, file_clean m F_STDERR wp rp.
Proof.
intros m P. unfold STDERR0_A, F_STDERR in *. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
split; [| split; [| split; [| split]]].
- apply (rdn_pristine m (0xea660 + 140) (word_to_le_bytes 4 (Z_to_bv 64 4294967295))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea660 + 40) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea660 + 56) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea660 + 8) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea660 + 16) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
Qed.

Lemma STDOUT_of_W : forall A LB LM FR B m md k, (1 <= k <= 4)%nat -> STDOUTW_A m k -> HEAPAx A LB LM FR B m md ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
(zero_lines (Nat.pred k) = [] /\ exists wp1 rp1, file_clean m 0xea750 wp1 rp1)
\/ (zero_lines (Nat.pred k) <> [] /\ fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ exists wb wp bufp bufsz rp1 can, stdout_pending m wb wp bufp bufsz rp1 can (zero_lines (Nat.pred k)) /\ STDOUT_BUF <= wb /\ wp <= STDOUT_BUF + 1024).
Proof.
intros A LB LM FR B m md k Hk SW HP FDL.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP) as (can & CG & CC & _). cbn [hl_got_guard hl_guard hla_base A4L A4H] in CG, CC.
destruct k as [|[|k]]; [lia| |].
- left. split; [reflexivity|]. exact (QscU.Mq2.stdoutw_clean m SW).
- right. split; [cbn; discriminate|]. split; [exact FDL|].
destruct (QscU.Mq2.stdoutw_pending m (S (S k)) can ltac:(lia) SW (conj (rdn_bytes_at m _ _ CG) (rdn_bytes_at m _ _ CC))) as (wb & wp & bufp & bufsz & rp1 & PEND & R1 & R2).
exists wb, wp, bufp, bufsz, rp1, can. split; [exact PEND| split; [exact R1| exact R2]].
Qed.

Definition dcellL (x : Z) : Prop :=
USP <= x < USP + 2^22 \/ in_pris x \/ A_TP - 168 <= x < A_TP - 164 \/ ATEXIT_A <= x < ATEXIT_A + 304 \/ ADFLAG_A <= x < ADFLAG_A + 1.

Lemma drvA_mem_agreeL : forall m m', drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcellL x -> m' (wa x) = m (wa x)) ->
(forall x, dcellL (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
drvA_mem argv USP m'.
Proof.
intros m m' D EQ WM LOC' MI'. destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC (mid & AT & MIDL)].
pose proof USPF as (U1 & U2 & U3).
assert (PH : ax_phase m' = ax_phase m) by (apply ax_phase_agree; apply EQ; [unfold ADFLAG_A; lia | unfold dcellL; repeat (lazymatch goal with |- _ \/ _ => right end); unfold ADFLAG_A; lia]).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agreeT; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF. apply EQ; [lia | apply HD; lia]. }
assert (RWT : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x) -> rw_cells asegs m' A cs).
{ intros A cs [RO (W1 & W2 & W3)] HD. split; [apply ROT; assumption|]. split; [exact W1|]. split; [exact W2|]. intros i Hi.
apply WM; [| apply W3; exact Hi]. rewrite wa_unsigned by lia. apply HD. lia. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S0 | exact EQA]]. apply ROT; [exact A0|]. cbn. intros; left; lia.
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S1 | exact EQA]]. apply ROT; [exact A1|]. cbn. intros; left; lia.
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64) by (unfold PRIS_A in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia|]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. cbn. intros; right; right; left; lia.
- exact LOC'.
- exists mid. split; [| exact MIDL]. unfold atexit_cells in AT |- *. rewrite PH. apply RWT; [exact AT|]. rewrite (atexit_cellsK_size _ _ MIDL). unfold ATEXIT_A. intros; right; right; right; left; unfold ATEXIT_A; lia.
Qed.

Lemma dcellL_cases : forall x, dcellL x ->
USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x645000 /\ cs_wide x /\ ~ a4_volatile x /\ ~ (T_LOCCELL_A <= x < T_LOCCELL_A + 8)
/\ ~ (0x612150 <= x < 0x622180 /\ x <> 0x622150) /\ ~ (0xea660 <= x < 0xea748) /\ ~ (0xea750 <= x < 0xea838) /\ ~ (0x6435e0 <= x < 0x6439f0)).
Proof.
intros x [H|[H|[H|[H|H]]]].
- left; exact H.
- right. unfold in_pris, PRIS_A in H. unfold T_LOCCELL_A, cs_wide, a4_volatile, A_TP.
repeat (apply Exists_cons in H; destruct H as [H|H]; [cbn [fst snd] in H; lia|]). apply Exists_nil in H. destruct H.
- right. unfold T_LOCCELL_A, A_TP, cs_wide, a4_volatile in *. lia.
- right. unfold T_LOCCELL_A, ATEXIT_A, cs_wide, a4_volatile, A_TP in *. lia.
- right. unfold T_LOCCELL_A, ADFLAG_A, cs_wide, a4_volatile, A_TP in *. lia.
Qed.

Lemma drvA_mem_presx : forall LBM SPv m m',
drvA_mem argv USP m -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
alloc_ceiling <= SPv <= USP -> drvA_mem argv USP m'.
Proof.
intros LBM SPv m m' D PRES LOC' MI' HS. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1, HS.
assert (CL : forall x, dcellL x -> client_addrx A4H (xtgt_A SPv) LBM SPv x).
{ intros x HC. pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & _)]; [left; lia|].
right; left. split; [apply OBL_CS_WIDE; exact X2|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB. intros [V|[V|V]]; [exact (X3 V) | exact (X4 V) | lia]. }
eapply drvA_mem_agreeL; [exact D | | | exact LOC' | exact MI'].
- intros x Hx HC. apply (proj1 (PRES x Hx (CL x HC))).
- intros x HC Hw. pose proof (u64_range x) as R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(lia) (CL _ HC))). exact Hw.
Qed.

Lemma drvA_mem_presT : forall LBM SPv m m',
drvA_mem argv USP m -> heap_pres A4H LBM SPv m m' -> mem_inv asegs m' -> SPv <= USP -> drvA_mem argv USP m'.
Proof.
intros LBM SPv m m' D PRES MI' HS.
assert (CL : forall x, dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> client_addr A4H LBM SPv x).
{ intros x [HC|HC].
- pose proof (dcellL_cases x HC) as [X|(X1 & X2 & _)]; [left; lia | right; left; apply OBL_CS_WIDE; exact X2].
- right; left. apply OBL_CS_WIDE. unfold cs_wide, T_LOCCELL_A, A_TP in *. lia. }
eapply drvA_mem_agreeL; [exact D | | | | exact MI'].
- intros x Hx HC. apply PRES; [lia | apply CL; left; exact HC].
- intros x HC Hw. pose proof (u64_range x) as R.
rewrite <- (Z_to_bv_bv_unsigned x) in Hw |- *. apply (proj2 (PRES (bv_unsigned x) ltac:(lia) (CL _ (or_introl HC)))). exact Hw.
- eapply (heap_pres_rw_cells A4H); [exact PRES | exact (dm_loc _ _ _ D) |]. right; left. intros a Ha. apply OBL_CS_WIDE. cbn in Ha. unfold cs_wide, T_LOCCELL_A, A_TP in *. lia.
Qed.

Definition twin (iv : Z * Z) : Prop :=
fst iv <= snd iv /\
( (LO <= fst iv /\ snd iv <= USP - 48)
\/ (0xea660 <= fst iv /\ snd iv <= 0xea748) \/ (0xea750 <= fst iv /\ snd iv <= 0xea838) \/ (0x6435e0 <= fst iv /\ snd iv <= 0x6439f0)
\/ (0x612150 <= fst iv /\ snd iv <= 0x622150) \/ (0x622150 + 1 <= fst iv /\ snd iv <= 0x622180)
\/ (0x645000 <= fst iv /\ snd iv <= USP - 48) ).

Lemma drvA_mem_munchT : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall twin W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x645000 /\ ~ (0x612150 <= x < 0x622180 /\ x <> 0x622150) /\ ~ (0xea660 <= x < 0xea748) /\ ~ (0xea750 <= x < 0xea838) /\ ~ (0x6435e0 <= x < 0x6439f0))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right; lia] |].
right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold twin in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply drvA_mem_agreeL; [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold twin in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[H1 H2] FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma pristine_presx : forall LBM SPv m m' lo hi, pristine m lo hi -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' ->
(forall a, lo <= a < hi -> cs_wide a /\ ~ a4_volatile a /\ ~ (T_LOCCELL_A <= a < T_LOCCELL_A + 8) /\ a < 0x645000) ->
0 <= lo -> alloc_ceiling <= SPv -> pristine m' lo hi.
Proof.
intros LBM SPv m m' lo hi P PRES OK H0 HS a Ha. destruct (OK a Ha) as (O1 & O2 & O3 & O4). rc_lia_prep. unfold alloc_ceiling in HS.
rewrite <- (P a Ha). refine (proj1 (PRES a ltac:(lia) _)). right; left. split; [apply OBL_CS_WIDE; exact O1|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB. intros [V|[V|V]]; [exact (O2 V) | exact (O3 V) | lia].
Qed.

Lemma pristine_pres : forall LBM SPv m m' lo hi, pristine m lo hi -> heap_pres A4H LBM SPv m m' ->
(forall a, lo <= a < hi -> cs_wide a) -> 0 <= lo -> hi <= 2^64 -> pristine m' lo hi.
Proof.
intros LBM SPv m m' lo hi P PRES OK H0 H1 a Ha. rewrite <- (P a Ha). refine (proj1 (PRES a ltac:(lia) _)). right; left. apply OBL_CS_WIDE. apply OK. exact Ha.
Qed.

Lemma STDOUTW_presx : forall LBM SPv m m' k, STDOUTW_A m k -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' -> (k <= 4)%nat ->
alloc_ceiling <= SPv -> STDOUTW_A m' k.
Proof.
intros LBM SPv m m' k SW PRES Hk HS. rc_lia_prep. unfold alloc_ceiling in HS. eapply STDOUTW_agree; [exact SW | | exact Hk].
intros x Hx. unfold F_STDOUT, STDOUT_BUF in Hx. refine (proj1 (PRES x ltac:(lia) _)). right; left. split; [apply OBL_CS_WIDE; unfold cs_wide; lia|].
unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB, a4_volatile, T_LOCCELL_A, A_TP. lia.
Qed.

Lemma STDOUTW_pres : forall LBM SPv m m' k, STDOUTW_A m k -> heap_pres A4H LBM SPv m m' -> (k <= 4)%nat -> STDOUTW_A m' k.
Proof.
intros LBM SPv m m' k SW PRES Hk. eapply STDOUTW_agree; [exact SW | | exact Hk].
intros x Hx. unfold F_STDOUT, STDOUT_BUF in Hx. refine (proj1 (PRES x ltac:(lia) _)). right; left. apply OBL_CS_WIDE; unfold cs_wide; lia.
Qed.

Lemma aef_presx : forall LBM SPv m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> heap_presx A4H (xtgt_A SPv) LBM SPv m m' -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros LBM SPv m m' b H PRES. eapply (heap_presx_rw_cells A4H); [exact PRES | exact H |]. right; left. intros a Ha. cbn in Ha.
split; [apply OBL_CS_WIDE; unfold cs_wide, AEF_FLAG_A in *; lia|]. unfold xtgt_A. cbn [hl_volatile A4H]. unfold A_SB, a4_volatile, T_LOCCELL_A, A_TP, AEF_FLAG_A in *. lia.
Qed.
Lemma aef_pres : forall LBM SPv m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> heap_pres A4H LBM SPv m m' -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros LBM SPv m m' b H PRES. eapply (heap_pres_rw_cells A4H); [exact PRES | exact H |]. right; left. intros a Ha. cbn in Ha.
apply OBL_CS_WIDE; unfold cs_wide, AEF_FLAG_A in *; lia.
Qed.
Lemma aef_munch : forall W m m' b, rw_cells asegs m AEF_FLAG_A [C1 b] -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= AEF_FLAG_A \/ AEF_FLAG_A + 1 <= fst iv) W -> rw_cells asegs m' AEF_FLAG_A [C1 b].
Proof.
intros W m m' b H MU WM FW. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. clear - FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [H1 FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Lemma drvA_mem_register : forall m m' mid, drvA_mem argv USP m ->
(forall x, 0 <= x < 2^64 -> dcellL x -> (x < ADFLAG_A \/ ADFLAG_A + 1 <= x) -> (x < ATEXIT_A \/ ATEXIT_A + 304 <= x) -> m' (wa x) = m (wa x)) ->
(forall x, dcellL (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None) ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> mem_inv asegs m' ->
rw_cells asegs m' ATEXIT_A (atexit_cellsK 2 mid) -> length mid = 240%nat ->
(exists b, m' (Z_to_bv 64 ADFLAG_A) = Some b) ->
drvA_mem argv USP m'.
Proof.
intros m m' mid D EQ WM LOC' MI' AT2 MIDL (b & FLG). destruct D as [MI ARGC (p0 & A0 & S0) ARG1 PR (tid & TID & TIDR) LOC _].
pose proof USPF as (U1 & U2 & U3).
assert (EQA : forall x, USP <= x < USP + 2^22 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)) by (intros; apply EQ; [lia | left; lia | unfold ADFLAG_A; lia | unfold ATEXIT_A; lia]).
assert (ROT : forall A cs, ro_cells asegs m A cs ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> dcellL x /\ (x < ADFLAG_A \/ ADFLAG_A + 1 <= x) /\ (x < ATEXIT_A \/ ATEXIT_A + 304 <= x)) -> ro_cells asegs m' A cs).
{ intros A cs [WF BA] HD. split; [exact WF|]. eapply bytes_at_agreeT; [exact BA|]. intros x Hx.
rewrite cells_bytes_length in Hx by exact WF. destruct BA as (B0 & B1 & _). rewrite cells_bytes_length in B1 by exact WF.
destruct (HD x ltac:(lia)) as (D1 & D2 & D3). apply EQ; [lia | exact D1 | exact D2 | exact D3]. }
constructor.
- exact MI'.
- exact ARGC.
- exists p0. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S0 | exact EQA]]. apply ROT; [exact A0|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A. split; [unfold dcellL; left; lia | lia].
- intros H2. destruct (ARG1 H2) as (p1 & A1 & S1). exists p1. split; [| eapply (@argstr_agree RC__ USP LO data USPF LOF); [exact S1 | exact EQA]]. apply ROT; [exact A1|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A. split; [unfold dcellL; left; lia | lia].
- unfold pris_A in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PR _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0.
assert (R : 0 <= lo /\ hi <= 2^64 /\ (hi <= ADFLAG_A \/ ADFLAG_A + 1 <= lo) /\ (hi <= ATEXIT_A \/ ATEXIT_A + 304 <= lo))
by (unfold PRIS_A in IN; unfold ADFLAG_A, ATEXIT_A; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN).
apply EQ; [lia| | lia | lia]. right; left. unfold in_pris. apply Exists_exists. exists (lo, hi). split; [exact IN | cbn; lia].
- exists tid. split; [| exact TIDR]. apply ROT; [exact TID|]. intros x Hx. cbn in Hx. unfold ADFLAG_A, ATEXIT_A, A_TP in *. split; [unfold dcellL; right; right; left; unfold A_TP; lia | lia].
- exact LOC'.
- exists mid. split; [| exact MIDL]. unfold atexit_cells, ax_phase. rewrite FLG. exact AT2.
Qed.

Lemma flag_written : forall m, rw_cells asegs m ADAPTER_FLAG [C1 (Z_to_bv 8 1)] -> exists b, m (Z_to_bv 64 ADFLAG_A) = Some b.
Proof.
intros m [[WF (B0 & B1 & B2)] _]. specialize (B2 0%nat ltac:(cbn; lia)). unfold mrd in B2. cbn [cells_bytes cbytes app nth Z.of_nat] in B2.
rewrite Z.add_0_r in B2. unfold ADAPTER_FLAG in B2. unfold ADFLAG_A.
destruct (m (wa 0x622150)) as [b|] eqn:E; [exists b; exact E|].
exfalso. vm_compute in B2. discriminate B2.
Qed.

Lemma lb_remove_zero : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> lb_remove 0 LB = LB.
Proof.
intros A LB LM FR B m md HP.
assert (NZ : forall b, In b LB -> blk_addr b <> 0).
{ intros [a n] Hin. cbn. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & Hp & _). lia. }
clear HP. induction LB as [|b LB IH]; [reflexivity|]. cbn [lb_remove].
replace (blk_addr b =? 0) with false by (symmetry; apply Z.eqb_neq; apply NZ; left; reflexivity).
rewrite IH; [reflexivity|]. intros b' H'. apply NZ. right. exact H'.
Qed.

Lemma CALLS14 : (1 <= calls_of data <= 4)%nat.
Proof. unfold calls_of. destruct (Z.to_nat (cfglen_of data)); [lia|]. pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)). lia. Qed.

Lemma neq13 : Z_to_bv 64 1 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 1) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.
Lemma CFDS_1 : forall fds, CFDS fds0 fds -> fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros fds [_ H]. rewrite (H _ neq13). exact FD1. Qed.
Lemma vm_only_fds : forall md md', model_vm_only (cfg_model md) (cfg_model md') -> m_fds (cfg_model md') = m_fds (cfg_model md).
Proof. intros md md' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
Lemma vm_only_fs : forall md md', model_vm_only (cfg_model md) (cfg_model md') -> m_fs (cfg_model md') = m_fs (cfg_model md).
Proof. intros md md' (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.

Lemma heapA_munchT : forall A LB LM B m m' md W,
HEAPAx A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (forall a, fst iv <= a < snd iv -> cs_wide a))) W ->
HEAPAx A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | H2].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
Qed.

Lemma heapA_munchT6 : forall A LB LM (B : bud6) m m' md W,
HEAPA6 A LB LM [] B m md -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (fun iv => fst iv <= snd iv /\ (alloc_ceiling <= fst iv \/ (forall a, fst iv <= a < snd iv -> cs_wide a)
\/ (exists b n, In (b, n) LB /\ b <= fst iv /\ snd iv <= b + n))) W ->
HEAPA6 A LB LM [] B m' md.
Proof.
intros A LB LM B m m' md W HP MU WM MI' FW.
eapply OBL_CLIENT_FRAME6; [exact HP | | intros x Hx; apply WM; exact Hx | exact MI'].
intros a Ha NC _ _. apply MU. rewrite wa_unsigned by lia.
clear - FW NC Ha OBL_CS_WIDE. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [[H1 HC] FW]. cbn [outside fst snd] in *. split; [| apply IH; exact FW].
intros [X1 X2]. apply NC. destruct HC as [H2 | [H2 | (b & n & HIN & H2 & H3)]].
- left. lia.
- right; left. apply OBL_CS_WIDE. apply H2. lia.
- right; right. exists (b, n). split; [apply in_or_app; left; exact HIN | cbn; lia].
Qed.

Lemma tr_enter : forall A LB LM FR (B : bud6) m md,
HEAPA6 A LB LM FR B m md -> 16 * TRV_BB <= QZsi.bQ B -> TRV_BB <= QZsi.bB B -> TRV_BB <= 512 * QZsi.bN B -> TR_BD <= QZsi.bD B ->
TR_BD <= 134217728 * QZsi.bM B ->
HEAPAx A LB LM FR (Bud TRV_BB TR_BD (QZsi.bM B)) m md.
Proof.
intros A LB LM FR B m md HP HQ HB HN HD HM. eapply (heapa5_enter A4L H6); [exact HP|].
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP) as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof RESTS6 as (R1 & R2 & R3). pose proof TGTB as (G1 & G2 & G3 & G4).
unfold blink. cbn [bB bD bM]. unfold TRV_BB, TR_BD in *. lia.
Qed.

Hypothesis LM0S : Z.of_nat (length LM0) < 8.

Section Loop.
Variables (buf cap : Z) (x5 x6 x7 x8 x9 x10 x11 : word) (K : TSet).
Hypothesis KN : K [].
Hypothesis Hcap : 65536 <= cap <= 2^26.
Hypothesis Hlen : len < cap.
Hypothesis FIT : 6 + cl <= len.

Hypothesis KOK : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (LK : list blk) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
TINVx 0 buf cap LK m' md' A' B' (zero_lines (Nat.pred (calls_of data))) ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp' (Z_to_bv 64 A_TP) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 cl) (Z_to_bv 64 (buf + 6 + cl)) (Z_to_bv 64 pl)
x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET_A) fc' None m' (seg_rom asegs)).

Record TI (i : nat) (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) : Prop := MKTI {
ti_mem  : drvA_mem argv USP m;
ti_heap : HEAPAx A (OWN al ++ (buf, cap) :: LK) LM0 [] B m md;
ti_bud  : Z.of_nat (calls_of data - i) * TGT_BB_A + 1024 <= bB B /\ Z.of_nat (calls_of data - i) * TGT_BD_A <= bD B;
ti_errno: exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
ti_pay  : bytes_at asegs m al payload;
ti_al   : (pl = 0 /\ al = EMPTY_A /\ ow = 0) \/ (0 < pl /\ ow = al);
ti_out  : match i with O => STDOUT0_A m | S _ => STDOUTW_A m i end;
ti_err  : STDERR0_A m;
ti_fds  : CFDS fds0 (m_fds (cfg_model md));
ti_fs   : m_fs (cfg_model md) = fs;
ti_stk  : stk asegs m LO TSP;
ti_frame: exists j0, rw_cells asegs m TSP (trun_frame j0 x5 x6 x7 buf);
ti_mfr  : exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN));
ti_aef  : rw_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]     }.

Definition tloop_stmt (i j : nat) : Prop :=
forall (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI i al ow LK m md A B -> frm0 fc ->
RZAx A md (match i with O => t_emit (W 1 (zero_lines 1)) K | S _ => K end)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 TLOOP_A) fc None m (seg_rom asegs)).

Lemma tloop_after : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
forall (al ow : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TI (S i) al ow LK m md A B -> frm0 fc ->
RZAx A md K
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 al) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 EMIT_RET_A) fc None m (seg_rom asegs)).
Proof.
intros i j Hj Hij IH. intros until fc. intros TIH FRM.
pose proof TIH as [D HP HBUD (errv & ERR) PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS4.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold trun_frame in FRt.
d5_enter.
unfold EMIT_RET_A.
step. step. if_truex.
step. rewrite (unsigned_lit (Z.of_nat j)) by lia. rewrite swrap32_id by lia. step.

destruct (Nat.eq_dec j 1) as [J1|J2].
2:{
if_truex. evt_done5. replace (Z.of_nat j + -1) with (Z.of_nat (j - 1)) by lia.
apply (IH ltac:(lia) al ow LK m md A B); [exact TIH | exact FRM]. }

subst j. if_falsex. step. step. evt_done5.
assert (Hi : S i = calls_of data) by lia.
destruct HBUD as [HB1 HB2]. rewrite <- Hi in HB1, HB2. rewrite Nat.sub_diag in HB1, HB2. cbn [Z.of_nat] in HB1, HB2.

assert (EPI : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 : word) (F' : bvmap 5 word) (fc' : bv 32),
drvA_mem argv USP m' -> HEAPAx A' ((buf, cap) :: LK) LM0 [] B' m' md' -> 512 <= bB B' ->
(exists e, rw_cells asegs m' (A_TP - 164) [C4 e]) ->
STDOUTW_A m' (S i) -> STDERR0_A m' -> CFDS fds0 (m_fds (cfg_model md')) -> m_fs (cfg_model md') = fs ->
stk asegs m' LO TSP -> rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf) ->
rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN)) ->
rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 0)] ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 0x919c0) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 pl) (Z_to_bv 64 al) r w1 w2 w3 w4 w5 w6 w7
(Z_to_bv 64 ow) (Z_to_bv 64 (-1)) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 q3 q4 q5 q6)
F' (ret_pc (Z_to_bv 64 0x919c0)) fc' None m' (seg_rom asegs))).
{ intros m' md' A' B' q0 q1 q2 r w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 F' fc' D' HP' HB' ERR' SW' ERRP' Hfds' Hfs' ST' FRt' MFR' AEF'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.        unfold trun_frame in FRt'.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x919c0)) with (Z_to_bv 64 0x919c0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. step.
match goal with |- context [Z_to_bv 64 (Z.land ?e 78)] => replace (Z_to_bv 64 (Z.land e 78)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity) end.
do 9 step. step. step.
evt_done5.
replace (ret_pc (Z_to_bv 64 TRUN_RET_A)) with (Z_to_bv 64 TRUN_RET_A : word) by (symmetry; apply ret_pc_even; [unfold TRUN_RET_A; lia| reflexivity]).
replace (TSP + 80) with SP by lia.
apply (KOK m' md' A' B' LK). rewrite <- Hi.
release_frame FRt' ST' (TSP + 80). replace (TSP + 80) with SP in ST' by lia.
constructor.
- exact D'.
- exact HP'.
- exact HB'.
- exact ERR'.
- exact ST'.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. exact MFR'.
- eapply (STDOUT_of_W A' _ _ _ _ m' md' (S i)); [lia | exact SW' | exact HP' | exact (CFDS_1 _ Hfds')].
- apply stderr_clean_of_pristine. exact ERRP'.
- exact Hfs'.
- lia.
- intros _. apply ro_of_rw. exact AEF'. }
assert (POST : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (cd : Z) (LBx : list blk) ms' (r : word),
ret_state A4H (Z_to_bv 64 0x919c0) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) (Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 ow) (Z_to_bv 64 (-1))
(Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat 1 + -1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') -> stk asegs m' LO TSP -> heap_pres A4H LBx TSP m m' ->
rw_cells asegs m' (A_TP - 164) [C4 errv] ->
HEAPAx A' ((buf, cap) :: LK) LM0 [] (charge B 512 cd) m' md' ->
RZAx A' md' K ms').
{ intros m' md' A' cd LBx ms' r RS VM ST' PRES ERR' HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
apply (EPI m' md' A' (charge B 512 cd)).
- eapply (drvA_mem_presT _ TSP m m'); [exact D | exact PRES | exact MI' | lia].
- exact HP'.
- cbn [bB charge]. lia.
- exists errv. exact ERR'.
- eapply STDOUTW_pres; [exact OUT | exact PRES | lia].
- unfold STDERR0_A, F_STDERR in *. eapply pristine_pres; [exact ERRP | exact PRES | intros; unfold cs_wide; lia | lia | lia].
- rewrite (vm_only_fds _ _ VM). exact Hfds.
- rewrite (vm_only_fs _ _ VM). exact Hfs.
- exact ST'.
- unfold trun_frame. eapply (heap_pres_rw_cells A4H); [exact PRES | exact FRt | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact PRES | exact MFR | left; cbn; lia].
- eapply aef_pres; [exact AEF | exact PRES]. }
destruct AL as [(A1 & A2 & A3)|(A1 & A2)].
-
subst ow. unfold OWN in HP. replace (pl =? 0) with true in HP by (symmetry; apply Z.eqb_eq; lia). cbn [app] in HP.
eapply (OBL_FREE_NN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A ((buf, cap) :: LK) LM0 [] B 0 LO errv UWptr HP);
[ left; reflexivity
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| lia | cbn [Z.eqb]; lia | ].
intros ms' m' md' A' r RS VM ST' PRES ERR' HP' REQ'. rewrite (lb_remove_zero _ _ _ _ _ _ _ HP) in PRES, HP'.
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR', PRES.
eapply POST; [exact RS | exact VM | exact ST' | exact PRES | exact ERR' | exact HP'].
-
subst ow. unfold OWN in HP. replace (pl =? 0) with false in HP by (symmetry; apply Z.eqb_neq; lia). cbn [app] in HP.
eapply (OBL_FREE_NN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A ((al, pl) :: (buf, cap) :: LK) LM0 [] B al LO errv UWptr HP);
[ right; exists pl; left; reflexivity
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| lia | destruct (al =? 0); cbn [uw_cost]; lia | ].
intros ms' m' md' A' r RS VM ST' PRES ERR' HP' REQ'.
replace (lb_remove al ((al, pl) :: (buf, cap) :: LK)) with ((buf, cap) :: LK) in * by (cbn [lb_remove blk_addr fst]; rewrite Z.eqb_refl; reflexivity).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H] in ERR', PRES.
eapply POST; [exact RS | exact VM | exact ST' | exact PRES | exact ERR' | exact HP'].
Qed.

Lemma tloop_step : forall i j, (1 <= j)%nat -> (i + j = calls_of data)%nat ->
((2 <= j)%nat -> tloop_stmt (S i) (j - 1)) ->
tloop_stmt i j.
Proof.
intros i j Hj Hij IH. unfold tloop_stmt. intros until fc. intros TIH FRM.
destruct TIH as [D HP HBUD (errv & ERR) PAY AL OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS4.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INB : In (buf, cap) ((OWN al ++ (buf, cap) :: LK) ++ LM0)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP INB) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP INB) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.

assert (ALF : 0 < al /\ al + pl <= rc_ceil /\ (pl = 0 \/ (In (al, pl) (OWN al ++ (buf, cap) :: LK) /\ (al + pl <= 0x10000 \/ 0x645000 <= al)))).
{ destruct AL as [(A1 & A2 & A3)|(A1 & A2)].
- subst al. unfold EMPTY_A. split; [lia | split; [lia | left; exact A1]].
- assert (INO : In (al, pl) (OWN al ++ (buf, cap) :: LK)).
{ apply in_or_app; left. unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left; reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ al pl HP ltac:(apply in_or_app; left; exact INO)) as (_ & _ & Apos & Ahi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ al pl HP ltac:(apply in_or_app; left; exact INO)) as Aimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Aimg. unfold alloc_ceiling in Ahi.
split; [lia | split; [lia | right; split; [exact INO | lia]]]. }
destruct ALF as (AL1 & AL2 & AL3).
unfold trun_frame in FRt.
assert (PLEN : Z.of_nat (length payload) = pl) by (rewrite length_skipn; lia).
d5_enter.
unfold TLOOP_A, ADAPTER_FLAG. unfold ADAPTER_FLAG in AL.

pose proof (conj PAY ERR) as KEEP. clear PAY ERR.
pose proof (munch_refl [(AEF_FLAG_A, AEF_FLAG_A + 1)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. unfold AEF_FLAG_A in MU1, AEF.
step. stepz.
step. step. step. evt_done5.
destruct KEEP as [PAY ERR].
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (D1 : drvA_mem argv USP mx) by (eapply drvA_mem_munchT; [exact D | exact MU1 | exact WM1 | exact MI |]; unfold twin; ivs_lia) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HP1 : HEAPAx A (OWN al ++ (buf, cap) :: LK) LM0 [] B mx md)
by (eapply heapA_munchT; [exact HP | exact MU1 | exact WM1 | exact MI |]; constructor; [| constructor]; cbn [fst snd]; split; [lia | right; intros; unfold cs_wide; lia]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (ERR1 : rw_cells asegs mx (A_TP - 164) [C4 errv]) by (eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]; cbn [disjoint_from cells_size csize Nat.add]; unfold A_TP; lia) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (PAY1 : bytes_at asegs mx al payload)
by (eapply bytes_at_transport; [exact PAY | exact MU1 |]; rewrite length_skipn; cbn [disjoint_from]; unfold EMPTY_A in AL; split; [lia | exact I]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (ERRP1 : STDERR0_A mx) by (unfold STDERR0_A, F_STDERR in *; eapply pristine_munch; [exact ERRP | exact MU1 | ivs_lia | lia | lia]) end.
lazymatch goal with |- RZAx _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OUT1 : match i with O => STDOUT0_A mx | S _ => STDOUTW_A mx i end);
[ destruct i as [|ipp];
[ unfold STDOUT0_A, F_STDOUT in *; destruct OUT as [O1 O2]; split;
[ eapply pristine_munch; [exact O1 | exact MU1 | ivs_lia | lia | lia] | eapply pristine_munch; [exact O2 | exact MU1 | ivs_lia | lia | lia] ]
| eapply STDOUTW_agree; [exact OUT | intros x Hx; apply MU1; unfold F_STDOUT, STDOUT_BUF in Hx; rewrite wa_unsigned by lia; cbn [outside fst snd]; lia | lia] ]
| ]
end.
unfold ADAPTER_FLAG.
assert (BB1 : TGT_BB_A <= bB B /\ TGT_BD_A <= bD B).
{ destruct HBUD as [HB1 HB2]. assert (X : 1 <= Z.of_nat (calls_of data - i)) by lia. nia. }
eapply (TGT (Z_to_bv 64 TCALL_RET_A) (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 pl) (Z_to_bv 64 al) (Z_to_bv 64 al) (Z_to_bv 64 pl) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 ow) s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 t3 t4 t5 t6
F fc _ md _ A (OWN al ++ (buf, cap) :: LK) LM0 B al pl LO payload errv);
[ exact HP1 | exact (proj1 BB1) | exact (proj2 BB1) | exact PAY1 | exact PLEN | lia | lia | unfold alloc_ceiling; lia
| destruct AL3 as [X|[X _]]; [left; exact X | right; exact X]
| exact LM0S
| exact (dm_loc _ _ _ D1) | exact (lock_of_dm _ D1) | exact (OBL_GA_of _ _ _ _ _ _ _ D1 HP1)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | exact (proj2 TOPF) | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR1 | reflexivity | unfold TCALL_RET_A; rewrite unsigned_lit by lia; reflexivity | reflexivity | exact FRM | reflexivity | reflexivity | ].

intros ms' m' md' A' B' errv' gp' LK' RSW VM ST' PRESX LOCC' LOCK' ERR' GA' HP' HBB HBD.
destruct RSW as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS & FRM').
specialize (FRM' FRM). cbn [hl_tp A4H] in ERR'. rewrite unsigned_lit in ST', PRESX by lia.
rewrite <- app_assoc in HP'. cbn [app] in HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (AEF' : rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 1)]) by (eapply aef_presx; [unfold AEF_FLAG_A; exact AEF | exact PRESX]).

cbn [hl_segs hla_base A4L A4H] in MI'.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presx _ TSP _ m'); [exact D1 | exact PRESX | exact LOCC' | exact MI' | lia]).
assert (PAY' : bytes_at asegs m' al payload).
{ destruct AL3 as [A0|(INO & AIMG)].
- destruct PAY1 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
- eapply (heap_presx_bytes_at A4H); [exact PRESX | exact PAY1 |]. right; right. exists (al, pl). split; [apply in_or_app; left; exact INO | cbn; rewrite length_skipn; lia]. }
assert (ERRP' : STDERR0_A m').
{ unfold STDERR0_A, F_STDERR in *. eapply pristine_presx; [exact ERRP1 | exact PRESX | | lia | lia].
intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia. }
assert (OUT' : match i with O => STDOUT0_A m' | S _ => STDOUTW_A m' i end).
{ destruct i as [|i'].
- unfold STDOUT0_A, F_STDOUT in *. destruct OUT1 as [O1 O2]. split.
+ eapply pristine_presx; [exact O1 | exact PRESX | | lia | lia]. intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia.
+ eapply pristine_presx; [exact O2 | exact PRESX | | lia | lia]. intros a Ha. unfold cs_wide, a4_volatile, T_LOCCELL_A, A_TP. lia.
- eapply STDOUTW_presx; [exact OUT1 | exact PRESX | lia | lia]. }
assert (FRt' : rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf)) by (unfold trun_frame; eapply (heap_presx_rw_cells A4H); [exact PRESX | exact FRt | left; lia]).
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) by (eapply (heap_presx_rw_cells A4H); [exact PRESX | exact MFR | left; lia]).
pose proof (vm_only_fds _ _ VM) as FDS'. pose proof (vm_only_fs _ _ VM) as FS'.
cbn [hl_segs hla_base A4L A4H] in MI'.
d5_enter.
replace (ret_pc (Z_to_bv 64 TCALL_RET_A)) with (Z_to_bv 64 TCALL_RET_A : word) by (symmetry; apply ret_pc_even; [unfold TCALL_RET_A; lia| reflexivity]).
unfold TCALL_RET_A, ADAPTER_FLAG. step.

pose proof (conj PAY' ERR') as KEEP. clear PAY' ERR'.
pose proof (munch_refl [(AEF_FLAG_A, AEF_FLAG_A + 1)] m') as MU3. pose proof (wmono_refl asegs m') as WM3. unfold AEF_FLAG_A in MU3, AEF'.
stepz.
step. step. apply evt_done.
destruct KEEP as [PAY' ERR'].
change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (D3 : drvA_mem argv USP mx) by (eapply drvA_mem_munchT; [exact D' | exact MU3 | exact WM3 | exact MI' |]; unfold twin; ivs_lia) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (HP3 : HEAPAx A' (OWN al ++ (buf, cap) :: LK ++ LK') LM0 [] B' mx md')
by (eapply heapA_munchT; [exact HP' | exact MU3 | exact WM3 | exact MI' |]; constructor; [| constructor]; cbn [fst snd]; split; [lia | right; intros; unfold cs_wide; lia]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (ERR3 : rw_cells asegs mx (A_TP - 164) [C4 errv']) by (eapply rw_cells_transport; [exact ERR' | exact MU3 | exact WM3 |]; cbn [disjoint_from cells_size csize Nat.add]; unfold A_TP; lia) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (PAY3 : bytes_at asegs mx al payload)
by (eapply bytes_at_transport; [exact PAY' | exact MU3 |]; rewrite length_skipn; cbn [disjoint_from]; unfold EMPTY_A in AL; split; [lia | exact I]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (ERRP3 : STDERR0_A mx) by (unfold STDERR0_A, F_STDERR in *; eapply pristine_munch; [exact ERRP' | exact MU3 | ivs_lia | lia | lia]) end.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] =>
assert (OUT3 : match i with O => STDOUT0_A mx | S _ => STDOUTW_A mx i end);
[ destruct i as [|ipp];
[ unfold STDOUT0_A, F_STDOUT in *; destruct OUT' as [O1 O2]; split;
[ eapply pristine_munch; [exact O1 | exact MU3 | ivs_lia | lia | lia] | eapply pristine_munch; [exact O2 | exact MU3 | ivs_lia | lia | lia] ]
| eapply STDOUTW_agree; [exact OUT' | intros x Hx; apply MU3; unfold F_STDOUT, STDOUT_BUF in Hx; rewrite wa_unsigned by lia; cbn [outside fst snd]; lia | lia] ]
| ]
end.
clear D' HP' ERRP' OUT' D1 HP1 ERRP1 OUT1 PAY1 ERR1 MU1 WM1 MU3 WM3.
lazymatch goal with |- context [MS _ _ _ _ None ?mx (seg_rom _)] => rename mx into m3 end.

assert (AFTER : forall (m2 : word -> option byte) (F2 : bvmap 5 word) (fc2 : bv 32) (cf2 : config) (ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 : word),
munch (PFW_OUT LO TSP) m3 m2 -> wmono asegs m3 m2 -> mem_inv asegs m2 -> stk asegs m2 LO TSP ->
STDOUTW_A m2 (S i) -> (frm0 fc' -> frm0 fc2) ->
(forall LBx Bx mx, HEAPAx A' LBx LM0 [] Bx mx md' -> HEAPAx A' LBx LM0 [] Bx mx cf2) -> same_io md' cf2 ->
RZAx A' cf2 K
(MS (mkR ra' (Z_to_bv 64 TSP) gp' (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 pl) (Z_to_bv 64 al) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 ow) (Z_to_bv 64 0) (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) x8 x9 x10 x11 q3 q4 q5 q6)
F2 (Z_to_bv 64 EMIT_RET_A) fc2 None m2 (seg_rom asegs))).
{ intros m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 HPX [SX1 SX2].
refine (tloop_after i j Hj Hij IH al ow (LK ++ LK') m2 cf2 A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 _ (FRM2 FRM')).
unfold PFW_OUT, F_STDOUT, STDOUT_BUF in MU2.
constructor.
- eapply drvA_mem_munchT; [exact D3 | exact MU2 | exact WM2 | exact MI2 |]. unfold twin. ivs_lia.
- apply HPX. eapply heapA_munchT; [exact HP3 | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia] | split; [lia | right; intros; unfold cs_wide; lia]].
- destruct HBUD as [HB1 HB2]. replace (Z.of_nat (calls_of data - S i)) with (Z.of_nat (calls_of data - i) - 1) by lia. nia.
- exists errv'. eapply rw_cells_transport; [exact ERR3 | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- destruct AL3 as [A0|(INO & AIMG)].
+ destruct PAY3 as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|]. intros k Hk. exfalso. rewrite length_skipn in Hk. lia.
+ eapply bytes_at_transport; [exact PAY3 | exact MU2 |]. rewrite length_skipn. cbn [disjoint_from]. repeat split; lia.
- exact AL.
- exact SW2.
- unfold STDERR0_A, F_STDERR in *. eapply pristine_munch; [exact ERRP3 | exact MU2 | ivs_lia | lia | lia].
- rewrite SX1, FDS'. exact Hfds.
- rewrite SX2, FS'. exact Hfs.
- exact ST2.
- exists j0. unfold trun_frame. eapply rw_cells_transport; [exact FRt' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. eapply rw_cells_transport; [exact MFR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
- eapply aef_munch; [exact AEF' | exact MU2 | exact WM2 | unfold PFW_OUT, F_STDOUT, STDOUT_BUF, AEF_FLAG_A; ivs_lia]. }

pose proof (PFIMG_of _ _ _ _ _ _ _ D3 HP3) as IMG'. pose proof (OBL_PFRT _ _ _ _ _ _ _ HP3) as RT'. pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP3) as HCK3.
destruct i as [|i'].
-
eapply PF1; [exact HCK3 | rewrite FDS'; exact (CFDS_1 _ Hfds) | exact OUT3 | exact IMG' | exact RT'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | pose proof OBL_PFLO; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI' | exact FRM' | exact KN |].
intros ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F2 fc2 m2 cf2 MU2 WM2 MI2 ST2 SW2 FS2 FRM2 HN2 SIO2.
rewrite unsigned_lit in MU2, ST2 by lia.
refine (AFTER m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 (fun _ _ _ HX => heapA_cfg_next A4L HIx _ _ _ _ _ _ _ _ HX HN2) SIO2 _). gp5_solve.
-
eapply (PFK (S i')); [exact HCK3 | lia | exact OUT3 | exact IMG' | exact RT'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | pose proof OBL_PFLO; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI' | exact FRM' | exact KN |].
intros ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F2 fc2 m2 cf2 MU2 WM2 MI2 ST2 SW2 FS2 FRM2 HN2 SIO2.
rewrite unsigned_lit in MU2, ST2 by lia.
refine (AFTER m2 F2 fc2 cf2 ra' q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 MU2 WM2 MI2 ST2 SW2 FRM2 (fun _ _ _ HX => heapA_cfg_next A4L HIx _ _ _ _ _ _ _ _ HX HN2) SIO2 _). gp5_solve.
Qed.
Lemma tloop_all : forall j i, (1 <= j)%nat -> (i + j = calls_of data)%nat -> tloop_stmt i j.
Proof.
induction j as [|j IHj]; intros i Hj Hij; [lia|].
apply tloop_step; [exact Hj | exact Hij |]. intros H2. replace (S j - 1)%nat with j by lia. apply IHj; lia.
Qed.

Definition twin2 (iv : Z * Z) : Prop := twin iv \/ (fst iv <= snd iv /\ snd iv <= 0x10000).
Lemma drvA_mem_munchT2 : forall m m' W, drvA_mem argv USP m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall twin2 W -> drvA_mem argv USP m'.
Proof.
intros m m' W D MU WM MI' FW. pose proof LOF as [L1 L2]. pose proof USPF as (U1 & U2 & U3). rc_lia_prep. unfold alloc_ceiling in L1.
assert (AG : forall x, 0 <= x < 2^64 -> dcellL x \/ (T_LOCCELL_A <= x < T_LOCCELL_A + 8) -> m' (wa x) = m (wa x)).
{ intros x Hx HC. apply MU. rewrite wa_unsigned by lia.
assert (X : USP <= x < USP + 2^22 \/ (0x10000 <= x < 0x645000 /\ ~ (0x612150 <= x < 0x622180 /\ x <> 0x622150) /\ ~ (0xea660 <= x < 0xea748) /\ ~ (0xea750 <= x < 0xea838) /\ ~ (0x6435e0 <= x < 0x6439f0))).
{ destruct HC as [HC|HC]; [pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; [left; lia | right; lia] |].
right. unfold T_LOCCELL_A, A_TP in HC. lia. }
clear - FW X Hx L1 L2 H U2 U3. unfold twin2, twin in FW. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in FW as [H1 FW]. cbn [outside fst snd] in *. split; [lia | apply IH; exact FW]. }
eapply drvA_mem_agreeL; [exact D | intros x Hx HC; apply AG; [exact Hx | left; exact HC] | intros x _ Hw; apply WM; exact Hw | | exact MI'].
eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. clear - FW L1 L2 H U2 U3. unfold twin2, twin in FW.
induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [H1 FW]. cbn [disjoint_from fst snd] in *.
split; [lia | apply IH; exact FW].
Qed.

Record PRE1 (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) : Prop := MKP1 {
p_mem  : drvA_mem argv USP m1;
p_heap : HEAPA6 A [(buf, cap)] LM0 [] B m1 md;
p_req  : reqA A <= 2^20 + 2 * cap;
p_bud  : TR_BQ <= QZsi.bQ B /\ TR_BB <= QZsi.bB B /\ 512 + TRV_BB <= 512 * QZsi.bN B /\ TR_BD <= QZsi.bD B
/\ TR_BD <= 134217728 * QZsi.bM B;
p_errno: exists errv, rw_cells asegs m1 (A_TP - 164) [C4 errv];
p_blk  : exists junk, rw_cells asegs m1 buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk];
p_out  : STDOUT0_A m1;
p_err  : STDERR0_A m1;
p_fds  : CFDS fds0 (m_fds (cfg_model md));
p_fs   : m_fs (cfg_model md) = fs;
p_stk  : stk asegs m1 LO TSP;
p_frame: exists j0, rw_cells asegs m1 TSP (trun_frame j0 x5 x6 x7 buf);
p_mfr  : exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m1 SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN));
p_aef  : rw_cells asegs m1 AEF_FLAG_A [C1 (Z_to_bv 8 0)]     }.

Lemma seg_empty : forall (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A B -> frm0 fc -> pl = 0 ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 0x91970) fc None m1 (seg_rom asegs)).
Proof.
intros until fc. intros P FRM PL0. destruct P as [D HP6 REQ HBUD (errv & ERR) (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) MFR AEF0].
destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold TR_BQ in HQ1. unfold TR_BB in HB1.
pose proof (tr_enter _ _ _ _ _ _ _ HP6 ltac:(unfold TRV_BB in *; lia) ltac:(unfold TRV_BB in *; lia) ltac:(lia) HB2 HM1) as HP.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof CALLS14 as CALLS. pose proof TGTB as (G1 & G2 & G3 & G4).
d5_enter.
step. step. step. step. evt_done5.
unfold ADAPTER_FLAG. replace (6431056 + 16) with EMPTY_A by reflexivity.
apply (tloop_all (calls_of data) 0 ltac:(lia) eq_refl EMPTY_A 0 [] m1 md A (Bud TRV_BB TR_BD (QZsi.bM B))); [| exact FRM].
constructor; [exact D | | | exists errv; exact ERR | | left; split; [exact PL0 | split; reflexivity] | exact OUT | exact ERRP | exact Hfds | exact Hfs | exact ST | exists j0; exact FRt | exact MFR | exact AEF0].
- unfold OWN. rewrite PL0. cbn [Z.eqb app]. exact HP.
- cbn [bB bD]. unfold TRV_BB, TR_BD. rewrite Nat.sub_0_r.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BB_A ltac:(lia) ltac:(lia)) as X1.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BD_A ltac:(lia) ltac:(lia)) as X2. lia.
- replace (skipn (Z.to_nat (6 + cfglen_of data)) data) with (@nil byte) by (symmetry; apply skipn_all2; lia).
unfold EMPTY_A. split; [cbn; lia|]. split; [cbn; lia|]. intros k Hk. cbn in Hk. lia.
Qed.

Lemma seg_alloc : forall (m1 : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PRE1 m1 md A B -> frm0 fc -> 0 < pl ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR ra (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
F (Z_to_bv 64 TALLOC_A) fc None m1 (seg_rom asegs)).
Proof.
intros until fc. intros P FRM PLP. destruct P as [D HP6 REQ HBUD (errv & ERR) (junk & BLK) OUT ERRP Hfds Hfs ST (j0 & FRt) (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) AEF0].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof TGTB as (G1 & G2 & G3 & G4).
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
unfold trun_frame in FRt. destruct HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1). unfold TR_BQ in HQ1. unfold TR_BB in HB1.
pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (BB0 & BD0 & BN0 & BM0 & BQ0). pose proof RESTS6 as (RSa & RSb & RSc).
assert (TRV0 : 0 <= TRV_BB) by (unfold TRV_BB; lia).
assert (ACP : acostA pl <= 3 * 67108864 + 45101) by (unfold acostA; destruct (Z.leb_spec pl 64512); lia).
d5_enter.
unfold TALLOC_A. step. step. evt_done5.
eapply (OBL_MALLOC_N6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md _ A [(buf, cap)] LM0 [] B pl LO errv UWptr HP6);
[ rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | lia
| cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]
| lia | lia | cbn [uw_cost]; unfold TR_BD in HB2; lia | lia | lia | ].
intros ms' m' md' A' r errv' RS VM ST' PRES ERR' Hr (junk2 & NB) HP6' REQ'.
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6') as HP'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.      pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(left; reflexivity)) as (_ & _ & Rpos & Rhi & _). unfold alloc_ceiling in Rhi.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(left; reflexivity)) as Rimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Rimg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP') as ND. cbn [map blk_addr fst app] in ND.
assert (NE : r <> buf) by (inversion ND; subst; cbn in *; intros E; subst; tauto).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r pl buf cap HP' ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
assert (D' : drvA_mem argv USP m') by (eapply (drvA_mem_presT _ TSP m1 m'); [exact D | exact PRES | exact MI' | lia]).
assert (BLK' : rw_cells asegs m' buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact BLK |]. right; right. exists (buf, cap). split; [left; reflexivity | cbn; lia]. }

pose proof BLK' as [[[WFb _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].
assert (SRC : bytes_at asegs m' (buf + 6 + cl) payload).
{ destruct BA as (B1 & B2 & B3). split; [lia|]. split; [rewrite length_skipn; lia|]. intros k Hk. rewrite length_skipn in Hk.
replace (buf + 6 + cl + Z.of_nat k) with (buf + Z.of_nat (Z.to_nat (6 + cl) + k)) by lia. rewrite B3 by lia.
rewrite nth_error_skipn. reflexivity. }
assert (OUT' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT in *. destruct OUT as [O1 O2]. split; (eapply pristine_pres; [eassumption | exact PRES | intros; unfold cs_wide; lia | lia | lia]). }
assert (ERRP' : STDERR0_A m').
{ unfold STDERR0_A, F_STDERR in *. eapply pristine_pres; [exact ERRP | exact PRES | intros; unfold cs_wide; lia | lia | lia]. }
assert (FRt' : rw_cells asegs m' TSP (trun_frame j0 x5 x6 x7 buf)) by (unfold trun_frame; eapply (heap_pres_rw_cells A4H); [exact PRES | exact FRt | left; lia]).
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) by (eapply (heap_pres_rw_cells A4H); [exact PRES | exact MFR | left; lia]).
assert (AEF' : rw_cells asegs m' AEF_FLAG_A [C1 (Z_to_bv 8 0)]) by (eapply aef_pres; [exact AEF0 | exact PRES]).
pose proof (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP') as RT'.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ r pl HP' ltac:(apply in_or_app; left; left; reflexivity)) as RAPP.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ buf cap HP' ltac:(apply in_or_app; left; right; left; reflexivity)) as BAPP.
cbn [hl_sb A4L] in RAPP, BAPP.
d5_enter.
replace (ret_pc (Z_to_bv 64 0x9192c)) with (Z_to_bv 64 0x9192c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_falsex.
step. step. step. step.

change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
assert (APP : 64 < pl -> app_mem r pl /\ app_mem (buf + 6 + cl) pl).
{ intros Hn64. unfold A_SB in RAPP, BAPP. replace ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in RAPP, BAPP by reflexivity.
unfold app_mem, A_SB, A_HMB. split; (split; [lia|]); [destruct RAPP as [X|X]; [left; lia | right; lia] | destruct BAPP as [X|X]; [left; lia | right; lia]]. }
eapply (imemcpy_sound region_is_poisoned_sound_U) with (d := r) (s := buf + 6 + cl) (n := pl) (lo := LO);
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | left; reflexivity | lia | lia | lia]
| intros _; eapply (unpoisoned_of_blk HIx); [exact HP' | right; left; reflexivity | lia | lia | lia]
| exact RT'
| lia | lia | lia | lia
| exact APP
| lia | lia
| reflexivity | reflexivity | reflexivity | lia | lia
| exact NB | exact SRC | rewrite length_skipn; lia
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI' | rewrite unsigned_lit by lia; reflexivity | ].
clear APP. rewrite !unsigned_lit by lia.
intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 MU2 WM2 MI2 DST2 SRC2 ST2.
replace (ret_pc (Z_to_bv 64 0x91940)) with (Z_to_bv 64 0x91940 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (HP26 : HEAPA6 A' ((r, pl) :: [(buf, cap)]) LM0 [] (QZsi.chargeQ (QZsi.charge B (acostA pl) (uw_cost UWptr) 1) (pl + 8192)) m2 md').
{ eapply heapA_munchT6; [exact HP6' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling.
- split; [lia | right; right; exists r, pl; split; [left; reflexivity | lia]].
- split; [lia | left; lia]. }

assert (HP2 : HEAPAx A' ((r, pl) :: [(buf, cap)]) LM0 [] (Bud TRV_BB TR_BD (QZsi.bM B)) m2 md').
{ pose proof (tr_enter _ _ _ _ _ _ _ HP26) as E. cbn [QZsi.bQ QZsi.bB QZsi.bN QZsi.bD QZsi.bM QZsi.charge QZsi.chargeQ uw_cost] in E.
apply E; lia. }
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP2) as HCK2.      step. step. step. step. evt_done5.
apply (tloop_all (calls_of data) 0 ltac:(lia) eq_refl r r [] m2 md' A' (Bud TRV_BB TR_BD (QZsi.bM B))); [| exact FRM].
constructor.
- eapply drvA_mem_munchT2; [exact D' | exact MU2 | exact WM2 | exact MI2 |].
constructor; [| constructor; [| constructor]]; unfold twin2, twin; cbn [fst snd]; [destruct Rimg as [X|X]; [right; lia | left; lia] | left; lia].
- unfold OWN. replace (pl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app]. exact HP2.
- cbn [bB bD]. unfold TRV_BB, TR_BD. rewrite Nat.sub_0_r.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BB_A ltac:(lia) ltac:(lia)) as X1.
pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat (calls_of data)) 4 TGT_BD_A ltac:(lia) ltac:(lia)) as X2. lia.
- exists errv'. eapply rw_cells_transport; [exact ERR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- destruct DST2 as [[_ BA2] _]. cbn [cells_bytes cbytes app] in BA2. rewrite app_nil_r in BA2. exact BA2.
- right. split; [lia | reflexivity].
- unfold STDOUT0_A, F_STDOUT in *. destruct OUT' as [O1 O2]. split; (eapply pristine_munch; [eassumption | exact MU2 | ivs_lia | lia | lia]).
- unfold STDERR0_A, F_STDERR in *. eapply pristine_munch; [exact ERRP' | exact MU2 | ivs_lia | lia | lia].
- rewrite (vm_only_fds _ _ VM). exact Hfds.
- rewrite (vm_only_fs _ _ VM). exact Hfs.
- exact ST2.
- exists j0. unfold trun_frame. eapply rw_cells_transport; [exact FRt' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. eapply rw_cells_transport; [exact MFR' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia.
- eapply rw_cells_transport; [exact AEF' | exact MU2 | exact WM2 |]. cbn [disjoint_from cells_size csize Nat.add]. unfold AEF_FLAG_A. repeat split; first [lia | destruct Rimg as [X|X]; lia].
Qed.
End Loop.

Theorem trun_ok : trun_stmt H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST.
Proof.
unfold trun_stmt. intros until fc. intros HI FIT FRM KN KOK.
destruct HI as [[D S0] HP6 REQ Hcap Hlen (junk & BLK) (errv & ERR) ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) Hfds Hfs (HQ1 & HB1 & HN1 & HB2 & HM1)].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof RESTS as [RB1 RB2]. pose proof RESTS6 as (RSa & RSb & RSc).
rc_lia_prep. unfold alloc_ceiling in L1. unfold A_TP in ERR.
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
pose proof CALLS14 as CALLS.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.

unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xea660, 0xea748) ltac:(cbn; tauto)) as PE. pose proof (proj1 (Forall_forall _ _) S0 (0xea750, 0xea838) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x6435e0, 0x6439f0) ltac:(cbn; tauto)) as PO2. pose proof (proj1 (Forall_forall _ _) S0 (0x622150, 0x622180) ltac:(cbn; tauto)) as PA.
cbn [fst snd] in PE, PO1, PO2, PA.
assert (FLAG : rw_cells asegs m ADAPTER_FLAG [C1 (Z_to_bv 8 0)]).
{ unfold ADAPTER_FLAG. eapply (rw_cells_pristine_recast m 0x622150 [Z_to_bv 8 0]);
[eapply pristine_sub; [exact PA | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity | exact I] | reflexivity | reflexivity]. }
pose proof (llvminit_of_dm _ _ _ _ _ _ _ HP) as GOTC. unfold GOT_LLVMINIT in GOTC.

assert (AEFc : rw_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]).
{ unfold AEF_FLAG_A. eapply (rw_cells_pristine_recast m 0x622154 [Z_to_bv 8 0]);
[eapply pristine_sub; [exact PA | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia | cbn; split; [reflexivity | exact I] | reflexivity | reflexivity]. }
unfold AEF_FLAG_A in AEFc.
destruct (dm_atexit _ _ _ D) as (mid & ATX & MIDL).
assert (PH1 : ax_phase m = 1).
{ unfold ax_phase. replace (m (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) by (symmetry; exact (PA ADFLAG_A ltac:(unfold ADFLAG_A; lia))). reflexivity. }
unfold atexit_cells in ATX. rewrite PH1 in ATX. unfold atexit_cellsK, ATEXIT_A in ATX. cbn [Z.eqb Pos.eqb] in ATX.
pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL0. cbn [hl_libc hla_base A4L A4H] in NL0.
assert (NL : ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)]) by (unfold NEEDLOCKS_A; split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact NL0]). clear NL0. unfold NEEDLOCKS_A in NL.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(USP - 208, USP - 128); (ADAPTER_FLAG, ADAPTER_FLAG + 1)] m) as MU.
unfold ADAPTER_FLAG in FLAG, MU. unfold A_TP in ERR.
pose proof (conj BLK ERR) as KEEP. clear BLK.
d5_enter.
unfold TRUN_A. carve_frame 80%nat ST.

replace (USP + -128 + -80) with (USP + -208) in * by lia.
do 10 step.
do 3 step.
step. step.
step.
step. step.
change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_truex.
step. stepz.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (atexit_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc LO mid);
[ exact MI | rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | exact MIDL
| unfold atexit_cellsK, ATEXIT_A; cbn [Z.eqb Pos.eqb]; exact ATX | exact NL | unfold AEF_GUARD_A; reflexivity ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3 & ST3 & AT3).
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold ATEXIT_A in MUc.
destruct KEEP as [BLK ERR0].
lazymatch type of MU with munch _ _ ?m2 =>
lazymatch type of MUc with munch ?Wc _ _ =>
lazymatch type of MU with munch ?W0 _ _ =>
assert (MU' : munch (W0 ++ Wc) m m3) by (eapply QjDJ.Mq0.munch_join; [exact MU | exact MUc | |]; intros x Hx; cbn [outside app] in Hx |- *; lia);
assert (WM' : wmono asegs m m3) by (eapply wmono_trans; [exact WM | exact WMc]);
cbn [app] in MU'; clear ATX MU WM; transport_after_call rsegs m2 m3 MUc WMc
end end end.
clear MUc WMc. rename MU' into MU. rename WM' into WM.
replace (ret_pc (Z_to_bv 64 0x9195c)) with (Z_to_bv 64 0x9195c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_truex.
step. step.
step. if_truex.

assert (P1 : PRE1 buf cap s5 s6 s7 m3 md A B).
{ pose proof (USPF) as (U1' & _). constructor.
- eapply (drvA_mem_register m m3 mid); [exact D | | | | exact MI3 | exact AT3 | exact MIDL | ].
+ intros x Hx HC HF HA. apply MU. rewrite wa_unsigned by lia.
pose proof (dcellL_cases x HC) as [X|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8)]; unfold ADFLAG_A, ATEXIT_A in *; cbn [outside fst snd app]; lia.
+ intros x HC Hw. apply WM. exact Hw.
+ eapply rw_cells_transport; [exact (dm_loc _ _ _ D) | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold T_LOCCELL_A, A_TP. repeat split; lia.
+ eapply flag_written. exact FLAG.
- eapply heapA_munchT6; [exact HP6 | exact MU | exact WM | exact MI3 |].
unfold alloc_ceiling. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; (split; [lia | first [left; lia | right; left; intros; unfold cs_wide; lia]]).
- exact REQ.
- repeat split; lia.
- exists errv. eapply rw_cells_transport; [exact ERR0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold A_TP. repeat split; lia.
- exists junk. eapply rw_cells_transport; [exact BLK | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?length_app. repeat split; first [lia | destruct Bimg as [X|X]; lia].
- unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]).
- unfold STDERR0_A, F_STDERR. eapply pristine_munch; [exact PE | exact MU | ivs_lia | lia | lia].
- exact Hfds.
- exact Hfs.
- exact ST3.
- eexists. unfold trun_frame. exact FR.
- exists j8, y7, y6, y5, y4, y3, y2, y1, y0. exact MFR.
- unfold AEF_FLAG_A. exact AEFc. }

assert (BLK3 : rw_cells asegs m3 buf [CB (length data) data; CB (Z.to_nat (cap - len)) junk]).
{ eapply rw_cells_transport; [exact BLK | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?length_app. repeat split; first [lia | destruct Bimg as [X|X]; lia]. }
pose proof BLK3 as [[[WFb _] BAb] _]. cbn [cells_bytes cbytes app] in BAb. apply bytes_at_app in BAb as [BAb _].
pose proof (bytes_at_read asegs _ buf data 2 1 BAb ltac:(lia) ltac:(lia)) as HR2.
change (Z.to_nat 2) with 2%nat in HR2. rewrite (nth_read 2%nat data (Z_to_bv 8 0)) in HR2 by lia.
pose proof (bv_unsigned_in_range 8 (nth 2 data (Z_to_bv 8 0))) as R2. unfold bv_modulus in R2. cbn in R2. fold (hb data 2) in R2.

assert (DISPATCH : forall (mx : word -> option byte) (rav q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w3 q3 q4 q5 q6 : word) (pcz : Z),
PRE1 buf cap s5 s6 s7 mx md A B -> (pcz = 0x9196c \/ pcz = 0x91920) ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR rav (Z_to_bv 64 TSP) gp (Z_to_bv 64 A_TP) q0 q1 q2
(Z_to_bv 64 pl) (Z_to_bv 64 (buf + 6 + cl)) r0 r1 r2 r3 r4 r5 r6 r7
(Z_to_bv 64 cl) w3 (Z_to_bv 64 ADAPTER_FLAG) (Z_to_bv 64 (Z.of_nat (calls_of data))) s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F (Z_to_bv 64 pcz) fc None mx (seg_rom asegs))).
{ intros mx rav q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 w3 q3 q4 q5 q6 pcz P1x Hpc.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ (hr_view H6 _ _ _ _ _ _ _ (p_heap _ _ _ _ _ _ _ _ _ P1x))) as HCKx.
d5_enter.
destruct (Z.eq_dec pl 0) as [PL0|PLP].
- destruct Hpc as [-> | ->]; step; [if_falsex | if_truex]; evt_done5;
(eapply (seg_empty buf cap s5 s6 s7 s8 s9 s10 s11 K KN Hcap Hlen FIT KOK); [exact P1x | exact FRM | exact PL0]).
- destruct Hpc as [-> | ->]; step; [if_truex | if_falsex]; evt_done5; unfold TALLOC_A;
(eapply (seg_alloc buf cap s5 s6 s7 s8 s9 s10 s11 K KN Hcap Hlen FIT KOK); [exact P1x | exact FRM | lia]). }
step.
destruct (Z.eq_dec cl 0) as [CL0|CLP].
-
if_truex. step. evt_done5.
replace (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat (calls_of data)) : word) by (unfold calls_of; rewrite CL0; reflexivity).
eapply DISPATCH; [exact P1 | left; reflexivity].
-
if_falsex. step. step. step. evt_done5.
unfold zxb. fold (hb data 2).
match goal with |- context [Z_to_bv 64 ?e] =>
lazymatch e with context [Z.land] =>
replace e with (Z.of_nat (calls_of data));
[| unfold calls_of; destruct (Z.to_nat (cfglen_of data)) eqn:E; [lia|];
rewrite !unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2^2) with 4;
pose proof (Z.mod_pos_bound (hb data 2) 4 ltac:(lia)); lia] end end.
eapply DISPATCH; [exact P1 | right; reflexivity].
Qed.
End Target.
End RC__1.
