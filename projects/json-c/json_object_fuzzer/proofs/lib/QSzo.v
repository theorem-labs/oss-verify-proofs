(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qhd4 QGcC QCKW Q1jK QsRG Qnhz QBxa QRjH Q9ox QsV0 Qn1e QMz4 QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn QBpc Qwm6 QlKV QsKa Qw5U QpNt Qfub Qujl Qirj QupI QnXa QdM4 QscU QOii QtWm QaDa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QbFI.
Import Qhd4.
Import QGcC.
Import QCKW.Mq5 QCKW.Mq6 QCKW.Mq7 Q1jK.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH Q9ox.Mq2 QsV0 Qn1e QBxa.Mq5 QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QBpc.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg Qw5U QpNt.Mq8.
Import Qfub Qujl.Mq4 Qirj QupI.Mq1 QnXa.Mq0 QupI QdM4.Mq4 QdM4.Mq3.
Import QscU QOii QtWm QaDa.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition USAGE_A : Z := 0x91b68.
Definition OPENFAIL_A : Z := 0x91c60.
Definition READERR_A : Z := 0x91bfc.
Definition DIE2_A : Z := 0x91c58.

Lemma neq23 : Z_to_bv 64 2 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 2) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma msg_shadow_zero : forall (HIx : heap_iface_A A4L) A LB LM FR B m md msg g,
HEAPA A4L HIx A LB LM FR B m md -> (msg = MSG_SHORT \/ msg = MSG_OVERRUN) -> msg / 8 <= g <= (msg + 31) / 8 ->
bytes_at asegs m (g + A_SB) [Z_to_bv 8 0].
Proof.
intros HIx A LB LM FR B m md msg g HP Hm Hg.
assert (R : 0x2000 <= g /\ g + 1 <= 0xc8e00) by (unfold MSG_SHORT, MSG_OVERRUN in Hm; destruct Hm as [-> | ->]; cbn in Hg; lia).
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP ltac:(cbn; lia) ltac:(cbn; lia)) as SH. cbn [hl_sb hl_reg_globals A4L] in SH.
destruct Hm as [-> | ->]; unfold MSG_SHORT, MSG_OVERRUN in Hg; cbn in Hg.
- rewrite (img_shadow_val_outside tokA_reg_globals 17055 17061 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
- rewrite (img_shadow_val_outside tokA_reg_globals 11342 11348 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
Qed.

Lemma stdout_clean_of_pristine : forall m, STDOUT0_A m -> exists wp rp, file_clean m F_STDOUT wp rp.
Proof.
intros m [P _]. unfold F_STDOUT in *. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
split; [| split; [| split; [| split]]].
- apply (rdn_pristine m (0xece30 + 140) (word_to_le_bytes 4 (Z_to_bv 64 4294967295))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xece30 + 40) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xece30 + 56) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xece30 + 8) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xece30 + 16) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
Qed.

Lemma stderr_ptr_cells : forall (HIx : heap_iface_A A4L) A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md ->
ro_cells asegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_P)] /\ ro_cells asegs m STDERR_P [C8 (Z_to_bv 64 F_STDERR)].
Proof.
intros HIx A LB LM FR B m md HP. pose proof (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) as P.
unfold GOT_STDERR, STDERR_P, F_STDERR. split.
- rtcR_cell P 0xe8e20 (le8 (Z_to_bv 64 0xe80b0)).
- rtcR_cell P 0xe80b0 (le8 (Z_to_bv 64 0xecd40)).
Qed.

Lemma bytes_at_func : forall (m : word -> option byte) a bs1 bs2,
bytes_at asegs m a bs1 -> bytes_at asegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs1)) as [LT|GE].
- rewrite <- (H1 i LT), <- (H2 i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
Lemma ro_C8_inj : forall (m : word -> option byte) a (v1 v2 : word), ro_cells asegs m a [C8 v1] -> ro_cells asegs m a [C8 v2] -> v1 = v2.
Proof.
intros m a v1 v2 [_ B1] [_ B2]. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
pose proof (bytes_at_func m a _ _ B1 B2 ltac:(rewrite !length_le8; reflexivity)) as E.
rewrite <- (le_bytes_to_word_le8 v1), <- (le_bytes_to_word_le8 v2), E. reflexivity.
Qed.

Section Leaf.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.
Variable reqA : ASA A4L HIx -> Z.
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
Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Lemma CFDS_2 : forall fds, CFDS fds0 fds -> fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros fds [_ H]. rewrite (H _ neq23). exact FD2. Qed.

Lemma die2_ok : forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_mem argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
STDOUT0_A m -> STDERRC_A m ->
pristine m ADFLAG_A (ADFLAG_A + 48) ->
RZAx A md (t_exit (exit_code 2) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 DIE2_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros D HP ST OUT0 (wp2 & rp2 & FC2) PAD.
assert (AEF0 : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]).
{ intros E. exfalso. unfold ax_phase in E. replace (m (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD ADFLAG_A ltac:(unfold ADFLAG_A; lia))). discriminate E. }
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
d5_enter.
unfold DIE2_A. step. step. apply evt_done.
destruct (exit_facts HIx argv USP A LB LM0 [] _ m md D HP AEF0) as ((tid & g0 & g1 & g5 & g6 & g7 & dso & ob & junkM & mid & XC) & SG & SHW & FC0).
destruct (stdout_clean_of_pristine m OUT0) as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1. unfold F_STDERR in FC2.
rewrite <- (exit_code_and_255 2) by lia.
eapply (exit_clean_A Jx SYS) with (lo := LO);
[ exact HCK | exact MI
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact XC | exact SG | exact FC0 | exact FC1 | exact FC2 ].
Qed.

Theorem leaf_refused_ok : leaf_refused_stmt H6 argv USP LO fs LM0 fds0.
Proof.
unfold leaf_refused_stmt. intros until fc. intros [D S0] HP ST Hfds Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xecd40, 0xece28) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xece30, 0xecf18) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x645ca0, 0x6460b0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
d5_enter.
unfold REFUSED_A. do 2 step. step. do 3 step.
step.
apply evt_done. unfold t_die.
assert (FDL2 : fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (Hfds _ neq23); exact FD2).
eapply FPU with (lo := LO);
[ exact HCK | exact FDL2 | reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A LB LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 597044)) with (Z_to_bv 64 597044 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
rewrite <- Hfs, <- SIO2. eapply die2_ok; [exact D' | exact HP' | exact ST' | exact OUT0' | exact ERRC | exact PAD'].
Qed.

Lemma arg_unpoisoned : forall A LB LM FR B m md p str,
HEAPAx A LB LM FR B m md -> argstr m USP p str -> unpoisoned asegs m A_SB p (Z.of_nat (length str) + 1).
Proof.

intros A LB LM FR B m md p str HP (B1 & B2 & B3 & [B4a [B4b B4c]] & _).
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
set (n := Z.of_nat (length str)) in *.
set (a := p / 64 * 64). set (e := (p + n) / 64 * 64 + 64).
assert (AE : p - 63 <= a <= p /\ p + n < e <= p + n + 64 /\ e <= 2^47 /\ a mod 8 = 0 /\ e mod 8 = 0) by (unfold a, e; Z.div_mod_to_equations; lia).
destruct AE as (A1 & A2 & A3 & A4 & A5).
pose proof (heapA_shadow_stack A4L HIx _ _ _ _ _ _ _ a (e - a) HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SH.
unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
assert (G : forall g, a / 8 <= g < e / 8 -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]).
{ intros g Hg. destruct SH as (S1 & S2 & S3). rewrite repeat_length in S2, S3.
specialize (S3 (Z.to_nat (g - a / 8)) ltac:(Z.div_mod_to_equations; lia)).
rewrite Z2Nat.id in S3 by (Z.div_mod_to_equations; lia).
split; [unfold A_SB; Z.div_mod_to_equations; lia|]. split; [cbn; unfold A_SB in *; Z.div_mod_to_equations; lia|].
intros i Hi. cbn in Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
replace (g + A_SB) with (a / 8 + A_SB + (g - a / 8)) by lia. rewrite S3.
rewrite nth_error_repeat; [reflexivity | Z.div_mod_to_equations; lia]. }
eapply (unpoisoned_of_zero_shadow2 asegs m A_SB p (n + 1) (a / 8) (e / 8) G);
[unfold A_SB, a; Z.div_mod_to_equations; lia | unfold A_SB, e; Z.div_mod_to_equations; lia | lia | lia | unfold A_SB; Z.div_mod_to_equations; lia].
Qed.

Theorem leaf_hdr_ok : leaf_hdr_stmt H6 argv USP LO fs LM0 fds0.
Proof.
unfold leaf_hdr_stmt. intros until fc. intros Hpc [D S0] HP HB (errv & ERR) ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) Hfds Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xecd40, 0xece28) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xece30, 0xecf18) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x645ca0, 0x6460b0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
pose proof (CFDS_2 _ Hfds) as FDL2.
unfold A_TP in ERR.

assert (K : forall (q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (cf' : config),
munch (PFW_ERR LO (bv_unsigned (Z_to_bv 64 SP))) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' LO (bv_unsigned (Z_to_bv 64 SP)) -> STDERRC_A m' -> CNEXT Jx md cf' -> same_io md cf' ->
RZAx A cf' (t_exit (exit_code 2) fs)
(MS (mkR (Z_to_bv 64 TAIL_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 2) (Z_to_bv 64 buf) r0 r1 r2 r3 r4 r5 r6 r7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F' (ret_pc (Z_to_bv 64 TAIL_A)) fc' None m' (seg_rom asegs))).
{ intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A [(buf, cap)] LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
assert (ERR' : rw_cells asegs m' (A_TP - 164) [C4 errv]).
{ unfold A_TP. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact MFR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
replace (ret_pc (Z_to_bv 64 TAIL_A)) with (Z_to_bv 64 TAIL_A : word) by (symmetry; apply ret_pc_even; [unfold TAIL_A; lia| reflexivity]).
eapply (aj5_conseq HIx); [| apply t_emit_W_nil; apply t_exit_has_nil].
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 2 buf cap [] m' cf' A B []).
destruct (stdout_clean_of_pristine m' OUT0') as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1.
constructor; [exact D' | exact HP' | exact HB | exists errv; exact ERR' | exact ST' | exists j8, y7, y6, y5, y4, y3, y2, y1, y0; exact MFR'
| left; split; [reflexivity | exists wp1, rp1; exact FC1] | exact ERRC | rewrite SIO2; exact Hfs | lia
| intros E; exfalso; unfold ax_phase in E; replace (m' (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD' ADFLAG_A ltac:(unfold ADFLAG_A; lia))); discriminate E]. }
destruct Hpc as [[-> ->] | [-> ->]].
-
d5_enter.
unfold HDR_SHORT_A. do 2 step. step. do 3 step. step. step. step.
apply evt_done. unfold t_die.
eapply FWR with (lo := LO) (msg := MSG_SHORT);
[ exact HCK | exact FDL2 | left; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| intros g Hg; eapply (msg_shadow_zero HIx); [exact HP | left; reflexivity | exact Hg]
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
refine (K q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' (conj SIO1 SIO2) _). gp5_solve.
-
d5_enter.
unfold HDR_OVERRUN_A. do 2 step. step. do 3 step. step. step.
apply evt_done. unfold t_die.
eapply FWR with (lo := LO) (msg := MSG_OVERRUN);
[ exact HCK | exact FDL2 | right; left; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| intros g Hg; eapply (msg_shadow_zero HIx); [exact HP | right; reflexivity | exact Hg]
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
refine (K q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' (conj SIO1 SIO2) _). gp5_solve.
Qed.

Definition PATHMSG_A : Z := 0x91c10.
Definition leaf_pathmsg_stmt : Prop :=
forall (fmt : Z) (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(fmt = FMT_CANNOT \/ fmt = FMT_READERR) ->
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (fmt_s_msg fmt (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 F_STDERR) (Z_to_bv 64 fmt) a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PATHMSG_A) fc None m (seg_rom asegs)).

Lemma leaf_pathmsg_ok : leaf_pathmsg_stmt.
Proof.
unfold leaf_pathmsg_stmt. intros until fc. intros Hfmt [D S0] HP ST ARGC2 A1 FDL2 FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xecd40, 0xece28) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xece30, 0xecf18) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x645ca0, 0x6460b0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.

destruct (dm_arg1 _ _ _ D ARGC2) as (p1 & A1' & STR).
pose proof (ro_C8_inj m (USP + 16) _ _ A1 A1') as E1. subst p1w. clear A1.
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & (slack & SB5 & SB6)).
pose proof (arg_unpoisoned _ _ _ _ _ m md p1 _ HP STR) as UP.
assert (BAS : bytes_at asegs m p1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack)).
{ replace (nth 1 argv [] ++ Z_to_bv 8 0 :: slack) with ((nth 1 argv [] ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app. split; [exact SB1|]. rewrite length_app. cbn [length]. replace (p1 + Z.of_nat (length (nth 1 argv []) + 1)) with (p1 + Z.of_nat (length (nth 1 argv [])) + 1) by lia. exact SB5. }
d5_enter.
unfold PATHMSG_A. step. step. step.
apply evt_done. unfold t_die.
eapply FPS with (lo := LO) (p := p1) (slack := slack);
[ exact HCK | exact FDL2 | destruct Hfmt as [-> | ->]; [right; left | right; right]; reflexivity
| reflexivity | reflexivity | reflexivity
| exact BAS | exact SB2 | exact SB6 | exact SB4b | exact UP | lia | rewrite unsigned_lit by lia; lia | lia
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A LB LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 597044)) with (Z_to_bv 64 597044 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
rewrite <- SIO2. eapply die2_ok; [exact D' | exact HP' | exact ST' | exact OUT0' | exact ERRC | exact PAD'].
Qed.

Definition leaf_openfail_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (msg_cannot_open (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPENFAIL_A) fc None m (seg_rom asegs)).

Lemma leaf_openfail_ok : leaf_openfail_stmt.
Proof.
unfold leaf_openfail_stmt. intros until fc. intros DS HP ST ARGC2 A1 FDL2 FRM.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
d5_enter.
unfold OPENFAIL_A. do 2 step. step. do 2 step. step.
evt_done5.
change (msg_cannot_open (nth 1 argv [])) with (fmt_s_msg FMT_CANNOT (nth 1 argv [])).
eapply leaf_pathmsg_ok; [left; reflexivity | exact DS | exact HP | exact ST | exact ARGC2 | exact A1 | exact FDL2 | exact FRM].
Qed.

Definition leaf_readerr_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (msg_read_error (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READERR_A) fc None m (seg_rom asegs)).

Lemma leaf_readerr_ok : leaf_readerr_stmt.
Proof.
unfold leaf_readerr_stmt. intros until fc. intros DS HP ST ARGC2 A1 FDL2 FRM.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
d5_enter.
unfold READERR_A. do 2 step. step. do 2 step.
evt_done5.
change (msg_read_error (nth 1 argv [])) with (fmt_s_msg FMT_READERR (nth 1 argv [])).
eapply leaf_pathmsg_ok; [right; reflexivity | exact DS | exact HP | exact ST | exact ARGC2 | exact A1 | exact FDL2 | exact FRM].
Qed.

Definition leaf_usage_stmt : Prop :=
forall (A : ASA A4L HIx) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A [] LM0 [] B m md -> stk asegs m LO SP ->
(exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die (msg_usage (nth 0 argv [])) fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 USAGE_A) fc None m (seg_rom asegs)).

Lemma leaf_usage_ok : leaf_usage_stmt.
Proof.
unfold leaf_usage_stmt. intros until fc. intros [D S0] HP ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) FDL2 Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xecd40, 0xece28) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xece30, 0xecf18) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x645ca0, 0x6460b0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
destruct (dm_arg0 _ _ _ D) as (p0 & A0 & STR).
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & (slack & SB5 & SB6)).
pose proof (arg_unpoisoned _ _ _ _ _ m md p0 _ HP STR) as UP.
assert (BAS : bytes_at asegs m p0 (nth 0 argv [] ++ Z_to_bv 8 0 :: slack)).
{ replace (nth 0 argv [] ++ Z_to_bv 8 0 :: slack) with ((nth 0 argv [] ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app. split; [exact SB1|]. rewrite length_app. cbn [length]. replace (p0 + Z.of_nat (length (nth 0 argv []) + 1)) with (p0 + Z.of_nat (length (nth 0 argv [])) + 1) by lia. exact SB5. }
d5_enter.
unfold USAGE_A. do 2 step. step. step. do 2 step. step.
apply evt_done. unfold t_die. change (msg_usage (nth 0 argv [])) with (fmt_s_msg FMT_USAGE (nth 0 argv [])).
eapply FPS with (lo := LO) (p := p0) (slack := slack);
[ exact HCK | exact FDL2 | left; reflexivity
| reflexivity | reflexivity | reflexivity
| exact BAS | exact SB2 | exact SB6 | exact SB4b | exact UP | lia | rewrite unsigned_lit by lia; lia | lia
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A [] LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact MFR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 0x91b84)) with (Z_to_bv 64 0x91b84 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
eapply (aj5_conseq HIx); [| apply t_emit_W_nil; apply t_exit_has_nil].
destruct (stdout_clean_of_pristine m' OUT0') as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1.
apply (epi_ok HIx SYS argv USP LO fs LM0 USPF LOF TOPF 2 [] m' cf' A B []).
constructor; [exact D' | exact HP' | exact ST' | exists j8, y7, y6, y5, y4, y3, y2, y1, y0; exact MFR'
| left; split; [reflexivity | exists wp1, rp1; exact FC1] | exact ERRC | rewrite SIO2; exact Hfs | lia
| intros E; exfalso; unfold ax_phase in E; replace (m' (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD' ADFLAG_A ltac:(unfold ADFLAG_A; lia))); discriminate E].
Qed.
End Leaf.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS67.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTmr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTmr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtWm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtWm.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaDa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaDa.
Import ListNotations. Unset Keyed Unification. Local Ltac QoSL.cell_of_bytes bs ::= QoSL.mkr__cell_of_bytes_10 bs. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac ivs_lia := repeat (lazymatch goal with |- _ \/ _ => fail | |- _ => constructor end); cbn [fst snd]; lia.

Definition USAGE_A : Z := 0x91790.
Definition OPENFAIL_A : Z := 0x91888.
Definition READERR_A : Z := 0x91824.
Definition DIE2_A : Z := 0x91880.

Lemma neq23 : Z_to_bv 64 2 <> Z_to_bv 64 3.
Proof. intros E. assert (X : bv_unsigned (Z_to_bv 64 2) = bv_unsigned (Z_to_bv 64 3)) by (rewrite E; reflexivity). rewrite !unsigned_lit in X by lia. lia. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma msg_shadow_zero : forall (HIx : heap_iface_A A4L) A LB LM FR B m md msg g,
HEAPA A4L HIx A LB LM FR B m md -> (msg = MSG_SHORT \/ msg = MSG_OVERRUN) -> msg / 8 <= g <= (msg + 31) / 8 ->
bytes_at asegs m (g + A_SB) [Z_to_bv 8 0].
Proof.
intros HIx A LB LM FR B m md msg g HP Hm Hg.
assert (R : 0x2000 <= g /\ g + 1 <= 0xc8a00) by (unfold MSG_SHORT, MSG_OVERRUN in Hm; destruct Hm as [-> | ->]; cbn in Hg; lia).
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP ltac:(cbn; lia) ltac:(cbn; lia)) as SH. cbn [hl_sb hl_reg_globals A4L] in SH.
destruct Hm as [-> | ->]; unfold MSG_SHORT, MSG_OVERRUN in Hg; cbn in Hg.
- rewrite (img_shadow_val_outside tokA_reg_globals 17035 17041 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
- rewrite (img_shadow_val_outside tokA_reg_globals 11299 11305 g ltac:(vm_compute; reflexivity) ltac:(lia)) in SH. exact SH.
Qed.

Lemma stdout_clean_of_pristine : forall m, STDOUT0_A m -> exists wp rp, file_clean m F_STDOUT wp rp.
Proof.
intros m [P _]. unfold F_STDOUT in *. exists (Z_to_bv 64 0), (Z_to_bv 64 0).
split; [| split; [| split; [| split]]].
- apply (rdn_pristine m (0xea750 + 140) (word_to_le_bytes 4 (Z_to_bv 64 4294967295))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea750 + 40) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea750 + 56) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea750 + 8) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- apply (rdn_pristine m (0xea750 + 16) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact P | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
Qed.

Lemma stderr_ptr_cells : forall (HIx : heap_iface_A A4L) A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md ->
ro_cells asegs m GOT_STDERR [C8 (Z_to_bv 64 STDERR_P)] /\ ro_cells asegs m STDERR_P [C8 (Z_to_bv 64 F_STDERR)].
Proof.
intros HIx A LB LM FR B m md HP. pose proof (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) as P.
unfold GOT_STDERR, STDERR_P, F_STDERR. split.
- rtcR_cell P 0xe6a20 (le8 (Z_to_bv 64 0xe5cb0)).
- rtcR_cell P 0xe5cb0 (le8 (Z_to_bv 64 0xea660)).
Qed.

Lemma bytes_at_func : forall (m : word -> option byte) a bs1 bs2,
bytes_at asegs m a bs1 -> bytes_at asegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs1)) as [LT|GE].
- rewrite <- (H1 i LT), <- (H2 i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
Lemma ro_C8_inj : forall (m : word -> option byte) a (v1 v2 : word), ro_cells asegs m a [C8 v1] -> ro_cells asegs m a [C8 v2] -> v1 = v2.
Proof.
intros m a v1 v2 [_ B1] [_ B2]. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
pose proof (bytes_at_func m a _ _ B1 B2 ltac:(rewrite !length_le8; reflexivity)) as E.
rewrite <- (le_bytes_to_word_le8 v1), <- (le_bytes_to_word_le8 v2), E. reflexivity.
Qed.

Section Leaf.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.
Ltac d5_reenter A := lazymatch goal with |- AJ ?J ?T ?c ?ms => refine (aj_evt J T c ms _); change (evt asegs (AJe A4L J A T c) ms) end.
Variable reqA : ASA A4L HIx -> Z.
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
Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= hiA_bot A4L HIx.
Hypothesis FPU : fprintf_u_stmt Jx PFRT PFLO.
Hypothesis FWR : fwrite_stmt Jx PFRT PFLO.
Hypothesis FPS : fprintf_s_stmt Jx PFRT PFLO.

Lemma CFDS_2 : forall fds, CFDS fds0 fds -> fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros fds [_ H]. rewrite (H _ neq23). exact FD2. Qed.

Lemma die2_ok : forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_mem argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
STDOUT0_A m -> STDERRC_A m ->
pristine m ADFLAG_A (ADFLAG_A + 48) ->
RZAx A md (t_exit (exit_code 2) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 DIE2_A) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros D HP ST OUT0 (wp2 & rp2 & FC2) PAD.
assert (AEF0 : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]).
{ intros E. exfalso. unfold ax_phase in E. replace (m (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD ADFLAG_A ltac:(unfold ADFLAG_A; lia))). discriminate E. }
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
d5_enter.
unfold DIE2_A. step. step. apply evt_done.
destruct (exit_facts HIx argv USP A LB LM0 [] _ m md D HP AEF0) as ((tid & g0 & g1 & g5 & g6 & g7 & dso & ob & junkM & mid & XC) & SG & SHW & FC0).
destruct (stdout_clean_of_pristine m OUT0) as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1. unfold F_STDERR in FC2.
rewrite <- (exit_code_and_255 2) by lia.
eapply (exit_clean_A Jx SYS) with (lo := LO);
[ exact HCK | exact MI
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact XC | exact SG | exact FC0 | exact FC1 | exact FC2 ].
Qed.

Theorem leaf_refused_ok : leaf_refused_stmt H6 argv USP LO fs LM0 fds0.
Proof.
unfold leaf_refused_stmt. intros until fc. intros [D S0] HP ST Hfds Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xea660, 0xea748) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xea750, 0xea838) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x6435e0, 0x6439f0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
d5_enter.
unfold REFUSED_A. do 2 step. step. do 3 step.
step.
apply evt_done. unfold t_die.
assert (FDL2 : fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (Hfds _ neq23); exact FD2).
eapply FPU with (lo := LO);
[ exact HCK | exact FDL2 | reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A LB LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 596060)) with (Z_to_bv 64 596060 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
rewrite <- Hfs, <- SIO2. eapply die2_ok; [exact D' | exact HP' | exact ST' | exact OUT0' | exact ERRC | exact PAD'].
Qed.

Lemma arg_unpoisoned : forall A LB LM FR B m md p str,
HEAPAx A LB LM FR B m md -> argstr m USP p str -> unpoisoned asegs m A_SB p (Z.of_nat (length str) + 1).
Proof.

intros A LB LM FR B m md p str HP (B1 & B2 & B3 & [B4a [B4b B4c]] & _).
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
set (n := Z.of_nat (length str)) in *.
set (a := p / 64 * 64). set (e := (p + n) / 64 * 64 + 64).
assert (AE : p - 63 <= a <= p /\ p + n < e <= p + n + 64 /\ e <= 2^47 /\ a mod 8 = 0 /\ e mod 8 = 0) by (unfold a, e; Z.div_mod_to_equations; lia).
destruct AE as (A1 & A2 & A3 & A4 & A5).
pose proof (heapA_shadow_stack A4L HIx _ _ _ _ _ _ _ a (e - a) HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SH.
unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
assert (G : forall g, a / 8 <= g < e / 8 -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]).
{ intros g Hg. destruct SH as (S1 & S2 & S3). rewrite repeat_length in S2, S3.
specialize (S3 (Z.to_nat (g - a / 8)) ltac:(Z.div_mod_to_equations; lia)).
rewrite Z2Nat.id in S3 by (Z.div_mod_to_equations; lia).
split; [unfold A_SB; Z.div_mod_to_equations; lia|]. split; [cbn; unfold A_SB in *; Z.div_mod_to_equations; lia|].
intros i Hi. cbn in Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
replace (g + A_SB) with (a / 8 + A_SB + (g - a / 8)) by lia. rewrite S3.
rewrite nth_error_repeat; [reflexivity | Z.div_mod_to_equations; lia]. }
eapply (unpoisoned_of_zero_shadow2 asegs m A_SB p (n + 1) (a / 8) (e / 8) G);
[unfold A_SB, a; Z.div_mod_to_equations; lia | unfold A_SB, e; Z.div_mod_to_equations; lia | lia | lia | unfold A_SB; Z.div_mod_to_equations; lia].
Qed.

Theorem leaf_hdr_ok : leaf_hdr_stmt H6 argv USP LO fs LM0 fds0.
Proof.
unfold leaf_hdr_stmt. intros until fc. intros Hpc [D S0] HP HB (errv & ERR) ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) Hfds Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xea660, 0xea748) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xea750, 0xea838) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x6435e0, 0x6439f0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
pose proof (CFDS_2 _ Hfds) as FDL2.
unfold A_TP in ERR.

assert (K : forall (q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (cf' : config),
munch (PFW_ERR LO (bv_unsigned (Z_to_bv 64 SP))) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' LO (bv_unsigned (Z_to_bv 64 SP)) -> STDERRC_A m' -> CNEXT Jx md cf' -> same_io md cf' ->
RZAx A cf' (t_exit (exit_code 2) fs)
(MS (mkR (Z_to_bv 64 TAIL_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) q0 q1 q2 (Z_to_bv 64 2) (Z_to_bv 64 buf) r0 r1 r2 r3 r4 r5 r6 r7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
F' (ret_pc (Z_to_bv 64 TAIL_A)) fc' None m' (seg_rom asegs))).
{ intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A [(buf, cap)] LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
assert (ERR' : rw_cells asegs m' (A_TP - 164) [C4 errv]).
{ unfold A_TP. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact MFR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
replace (ret_pc (Z_to_bv 64 TAIL_A)) with (Z_to_bv 64 TAIL_A : word) by (symmetry; apply ret_pc_even; [unfold TAIL_A; lia| reflexivity]).
eapply (aj5_conseq HIx); [| apply t_emit_W_nil; apply t_exit_has_nil].
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 2 buf cap [] m' cf' A B []).
destruct (stdout_clean_of_pristine m' OUT0') as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1.
constructor; [exact D' | exact HP' | exact HB | exists errv; exact ERR' | exact ST' | exists j8, y7, y6, y5, y4, y3, y2, y1, y0; exact MFR'
| left; split; [reflexivity | exists wp1, rp1; exact FC1] | exact ERRC | rewrite SIO2; exact Hfs | lia
| intros E; exfalso; unfold ax_phase in E; replace (m' (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD' ADFLAG_A ltac:(unfold ADFLAG_A; lia))); discriminate E]. }
destruct Hpc as [[-> ->] | [-> ->]].
-
d5_enter.
unfold HDR_SHORT_A. do 2 step. step. do 3 step. step. step. step.
apply evt_done. unfold t_die.
eapply FWR with (lo := LO) (msg := MSG_SHORT);
[ exact HCK | exact FDL2 | left; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| intros g Hg; eapply (msg_shadow_zero HIx); [exact HP | left; reflexivity | exact Hg]
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
refine (K q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' (conj SIO1 SIO2) _). gp5_solve.
-
d5_enter.
unfold HDR_OVERRUN_A. do 2 step. step. do 3 step. step. step.
apply evt_done. unfold t_die.
eapply FWR with (lo := LO) (msg := MSG_OVERRUN);
[ exact HCK | exact FDL2 | right; left; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | reflexivity
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| intros g Hg; eapply (msg_shadow_zero HIx); [exact HP | right; reflexivity | exact Hg]
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
refine (K q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC HN' (conj SIO1 SIO2) _). gp5_solve.
Qed.

Definition PATHMSG_A : Z := 0x91838.
Definition leaf_pathmsg_stmt : Prop :=
forall (fmt : Z) (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(fmt = FMT_CANNOT \/ fmt = FMT_READERR) ->
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (fmt_s_msg fmt (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 F_STDERR) (Z_to_bv 64 fmt) a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PATHMSG_A) fc None m (seg_rom asegs)).

Lemma leaf_pathmsg_ok : leaf_pathmsg_stmt.
Proof.
unfold leaf_pathmsg_stmt. intros until fc. intros Hfmt [D S0] HP ST ARGC2 A1 FDL2 FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xea660, 0xea748) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xea750, 0xea838) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x6435e0, 0x6439f0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.

destruct (dm_arg1 _ _ _ D ARGC2) as (p1 & A1' & STR).
pose proof (ro_C8_inj m (USP + 16) _ _ A1 A1') as E1. subst p1w. clear A1.
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & (slack & SB5 & SB6)).
pose proof (arg_unpoisoned _ _ _ _ _ m md p1 _ HP STR) as UP.
assert (BAS : bytes_at asegs m p1 (nth 1 argv [] ++ Z_to_bv 8 0 :: slack)).
{ replace (nth 1 argv [] ++ Z_to_bv 8 0 :: slack) with ((nth 1 argv [] ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app. split; [exact SB1|]. rewrite length_app. cbn [length]. replace (p1 + Z.of_nat (length (nth 1 argv []) + 1)) with (p1 + Z.of_nat (length (nth 1 argv [])) + 1) by lia. exact SB5. }
d5_enter.
unfold PATHMSG_A. step. step. step.
apply evt_done. unfold t_die.
eapply FPS with (lo := LO) (p := p1) (slack := slack);
[ exact HCK | exact FDL2 | destruct Hfmt as [-> | ->]; [right; left | right; right]; reflexivity
| reflexivity | reflexivity | reflexivity
| exact BAS | exact SB2 | exact SB6 | exact SB4b | exact UP | lia | rewrite unsigned_lit by lia; lia | lia
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A LB LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 596060)) with (Z_to_bv 64 596060 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
rewrite <- SIO2. eapply die2_ok; [exact D' | exact HP' | exact ST' | exact OUT0' | exact ERRC | exact PAD'].
Qed.

Definition leaf_openfail_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (msg_cannot_open (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 OPENFAIL_A) fc None m (seg_rom asegs)).

Lemma leaf_openfail_ok : leaf_openfail_stmt.
Proof.
unfold leaf_openfail_stmt. intros until fc. intros DS HP ST ARGC2 A1 FDL2 FRM.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
d5_enter.
unfold OPENFAIL_A. do 2 step. step. do 2 step. step.
evt_done5.
change (msg_cannot_open (nth 1 argv [])) with (fmt_s_msg FMT_CANNOT (nth 1 argv [])).
eapply leaf_pathmsg_ok; [left; reflexivity | exact DS | exact HP | exact ST | exact ARGC2 | exact A1 | exact FDL2 | exact FRM].
Qed.

Definition leaf_readerr_stmt : Prop :=
forall (A : ASA A4L HIx) (LB : list blk) (B : bud) (m : word -> option byte) (md : config) (p1w : word)
(ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A LB LM0 [] B m md -> stk asegs m LO SP ->
(2 <= length argv)%nat -> ro_cells asegs m (USP + 16) [C8 p1w] ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> frm0 fc ->
RZAx A md (t_die (msg_read_error (nth 1 argv [])) (m_fs (cfg_model md)))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
p1w s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 READERR_A) fc None m (seg_rom asegs)).

Lemma leaf_readerr_ok : leaf_readerr_stmt.
Proof.
unfold leaf_readerr_stmt. intros until fc. intros DS HP ST ARGC2 A1 FDL2 FRM.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
d5_enter.
unfold READERR_A. do 2 step. step. do 2 step.
evt_done5.
change (msg_read_error (nth 1 argv [])) with (fmt_s_msg FMT_READERR (nth 1 argv [])).
eapply leaf_pathmsg_ok; [right; reflexivity | exact DS | exact HP | exact ST | exact ARGC2 | exact A1 | exact FDL2 | exact FRM].
Qed.

Definition leaf_usage_stmt : Prop :=
forall (A : ASA A4L HIx) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
drvA_memS argv USP m -> HEAPAx A [] LM0 [] B m md -> stk asegs m LO SP ->
(exists j8 (y7 y6 y5 y4 y3 y2 y1 y0 : word), rw_cells asegs m SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))) ->
fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die (msg_usage (nth 0 argv [])) fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) s1 a0 (Z_to_bv 64 (USP + 8)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 USAGE_A) fc None m (seg_rom asegs)).

Lemma leaf_usage_ok : leaf_usage_stmt.
Proof.
unfold leaf_usage_stmt. intros until fc. intros [D S0] HP ST (j8 & y7 & y6 & y5 & y4 & y3 & y2 & y1 & y0 & MFR) FDL2 Hfs FRM.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (stderr_ptr_cells HIx _ _ _ _ _ _ _ HP) as [GOTC PTRC]. unfold GOT_STDERR, STDERR_P, F_STDERR in GOTC, PTRC.
unfold stdio0, STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (0xea660, 0xea748) ltac:(cbn; tauto)) as PE.
pose proof (proj1 (Forall_forall _ _) S0 (0xea750, 0xea838) ltac:(cbn; tauto)) as PO1.
pose proof (proj1 (Forall_forall _ _) S0 (0x6435e0, 0x6439f0) ltac:(cbn; tauto)) as PO2. cbn [fst snd] in PE, PO1, PO2.
destruct (dm_arg0 _ _ _ D) as (p0 & A0 & STR).
pose proof STR as (SB1 & SB2 & SB3 & [SB4a [SB4b SB4c]] & (slack & SB5 & SB6)).
pose proof (arg_unpoisoned _ _ _ _ _ m md p0 _ HP STR) as UP.
assert (BAS : bytes_at asegs m p0 (nth 0 argv [] ++ Z_to_bv 8 0 :: slack)).
{ replace (nth 0 argv [] ++ Z_to_bv 8 0 :: slack) with ((nth 0 argv [] ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app. split; [exact SB1|]. rewrite length_app. cbn [length]. replace (p0 + Z.of_nat (length (nth 0 argv []) + 1)) with (p0 + Z.of_nat (length (nth 0 argv [])) + 1) by lia. exact SB5. }
d5_enter.
unfold USAGE_A. do 2 step. step. step. do 2 step. step.
apply evt_done. unfold t_die. change (msg_usage (nth 0 argv [])) with (fmt_s_msg FMT_USAGE (nth 0 argv [])).
eapply FPS with (lo := LO) (p := p0) (slack := slack);
[ exact HCK | exact FDL2 | left; reflexivity
| reflexivity | reflexivity | reflexivity
| exact BAS | exact SB2 | exact SB6 | exact SB4b | exact UP | lia | rewrite unsigned_lit by lia; lia | lia
| exact PE | exact (PFIMG_of H6 argv USP _ _ _ _ _ _ _ D HP) | exact (OBL_PFRT _ _ _ _ _ _ _ HP)
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | pose proof OBL_PFLO; pose proof TOPF; lia | unfold PF_STACK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact MI | exact FRM | rewrite unsigned_lit by lia; reflexivity
| apply t_exit_has_nil | ].
intros q0 q1 q2 r0 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F' fc' m' cf' MU WM MI' ST' ERRC FS' FRM' HN' [SIO1 SIO2].
rewrite unsigned_lit in MU, ST' by lia. unfold PFW_ERR, F_STDERR in MU.
assert (D' : drvA_mem argv USP m').
{ eapply (drvA_mem_munchT argv USP LO data USPF LOF); [exact D | exact MU | exact WM | exact MI' |]. unfold twin. ivs_lia. }
assert (HP' : HEAPAx A [] LM0 [] B m' cf').
{ eapply (heapA_cfg_next A4L HIx); [| exact HN']. eapply (heapA_munchT H6 OBL_CLIENT_FRAME OBL_CS_WIDE USP); [exact HP | exact MU | exact WM | exact MI' |].
constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold alloc_ceiling;
[split; [lia | left; lia] | split; [lia | right; intros; unfold cs_wide; lia]]. }
assert (OUT0' : STDOUT0_A m').
{ unfold STDOUT0_A, F_STDOUT. split; (eapply pristine_munch; [eassumption | exact MU | ivs_lia | lia | lia]). }
assert (PAD' : pristine m' ADFLAG_A (ADFLAG_A + 48)).
{ pose proof (proj1 (Forall_forall _ _) S0 (ADFLAG_A, ADFLAG_A + 48) ltac:(unfold ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
unfold ADFLAG_A in *. eapply pristine_munch; [exact PAD | exact MU | ivs_lia | lia | lia]. }
assert (MFR' : rw_cells asegs m' SP (main_frame j8 y7 y6 y5 y4 y3 y2 y1 y0 (Z_to_bv 64 RA_MAIN))).
{ eapply rw_cells_transport; [exact MFR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add main_frame]. repeat split; lia. }
d5_reenter A.
replace (ret_pc (Z_to_bv 64 0x917ac)) with (Z_to_bv 64 0x917ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. evt_done5.
eapply (aj5_conseq HIx); [| apply t_emit_W_nil; apply t_exit_has_nil].
destruct (stdout_clean_of_pristine m' OUT0') as (wp1 & rp1 & FC1). unfold F_STDOUT in FC1.
apply (epi_ok HIx SYS argv USP LO fs LM0 USPF LOF TOPF 2 [] m' cf' A B []).
constructor; [exact D' | exact HP' | exact ST' | exists j8, y7, y6, y5, y4, y3, y2, y1, y0; exact MFR'
| left; split; [reflexivity | exists wp1, rp1; exact FC1] | exact ERRC | rewrite SIO2; exact Hfs | lia
| intros E; exfalso; unfold ax_phase in E; replace (m' (Z_to_bv 64 ADFLAG_A)) with (@None (bv 8)) in E by (symmetry; exact (PAD' ADFLAG_A ltac:(unfold ADFLAG_A; lia))); discriminate E].
Qed.
End Leaf.
End RC__1.
