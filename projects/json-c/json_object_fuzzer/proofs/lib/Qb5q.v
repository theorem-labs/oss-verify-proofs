(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5 QJFf QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QCoy QLPb QY73 Q72M QDRB Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D QvSK Qxua.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QCoy QLPb QY73 Q72M QDRB.
Import Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D QvSK.Mq0 Qxua.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Definition MV (w : bool) : nat := if w then MV_A else MV_B.
Definition GV (w : bool) : nat := if w then GV_A else GV_B.
Definition CTXc (w : bool) := if w then CTX_A else CTX_B.
Definition NLc (w : bool) := if w then NL_A else NL_B.
Definition PGSZc (w : bool) := if w then PGSZ_A else PGSZ_B.
Definition GOTSSPc (w : bool) := if w then GOTSSP_A else GOTSSP_B.
Definition SSPGc (w : bool) := if w then SSPG_A else SSPG_B.
Definition VMLc (w : bool) := if w then VML_A else VML_B.
Definition METAc (w : bool) := if w then META_A else META_B.
Definition GRPc (w : bool) := if w then GRP_A else GRP_B.
Definition PGE (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).

Lemma CHECKS : forall w ch, HSCLASS_S w ch ->
cells_check JO6SEGS (kn_view ch) (ELit 0) 0x6431e0 (CTXc w) = true /\ cells_check JO6SEGS (kn_view ch) (ELit 0) 0x6430f3 (NLc w) = true
/\ cells_check JO6SEGS (kn_view ch) (ELit 0) 0x643120 (PGSZc w) = true /\ cells_check JO6SEGS (kn_view ch) (ELit 0) 0xe6b80 (GOTSSPc w) = true
/\ cells_check JO6SEGS (kn_view ch) (ELit 0) 0x642ea0 (SSPGc w) = true /\ cells_check JO6SEGS (kn_view ch) (ELit 0) 0x6446f8 (VMLc w) = true
/\ cells_check JO6SEGS (kn_view ch) (PGE (MV w)) 4096 (METAc w) = true /\ cells_check JO6SEGS (kn_view ch) (PGE (GV w)) 0 (GRPc w) = true
/\ wr_check (kn_view ch) (PGE (MV w)) 4096 4096 = true /\ wr_check (kn_view ch) (PGE (GV w)) 0 4096 = true.
Proof.
intros [|] ch [-> | ->]; cbn [CTXc NLc PGSZc GOTSSPc SSPGc VMLc METAc GRPc MV GV].
- exact (conj CTX_HS2sA_1_ok (conj NL_HS2sA_1_ok (conj PGSZ_HS2sA_1_ok (conj GOTSSP_HS2sA_1_ok (conj SSPG_HS2sA_1_ok (conj VML_HS2sA_1_ok (conj META_HS2sA_1_ok (conj GRP_HS2sA_1_ok (conj METAW_HS2sA_1_ok GRPW_HS2sA_1_ok))))))))).
- exact (conj CTX_HS2sA_2_ok (conj NL_HS2sA_2_ok (conj PGSZ_HS2sA_2_ok (conj GOTSSP_HS2sA_2_ok (conj SSPG_HS2sA_2_ok (conj VML_HS2sA_2_ok (conj META_HS2sA_2_ok (conj GRP_HS2sA_2_ok (conj METAW_HS2sA_2_ok GRPW_HS2sA_2_ok))))))))).
- exact (conj CTX_HS2sB_3_ok (conj NL_HS2sB_3_ok (conj PGSZ_HS2sB_3_ok (conj GOTSSP_HS2sB_3_ok (conj SSPG_HS2sB_3_ok (conj VML_HS2sB_3_ok (conj META_HS2sB_3_ok (conj GRP_HS2sB_3_ok (conj METAW_HS2sB_3_ok GRPW_HS2sB_3_ok))))))))).
- exact (conj CTX_HS2sB_4_ok (conj NL_HS2sB_4_ok (conj PGSZ_HS2sB_4_ok (conj GOTSSP_HS2sB_4_ok (conj SSPG_HS2sB_4_ok (conj VML_HS2sB_4_ok (conj META_HS2sB_4_ok (conj GRP_HS2sB_4_ok (conj METAW_HS2sB_4_ok GRPW_HS2sB_4_ok))))))))).
Qed.

Lemma SMALL_w : img_w_b JO6SEGS 0x6430f3 1 = true /\ img_w_b JO6SEGS 0x643120 8 = true /\ img_w_b JO6SEGS 0xe6b80 8 = true
/\ img_w_b JO6SEGS 0x642ea0 8 = true /\ img_w_b JO6SEGS 0x6446f8 4 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section HeapCells.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).

Definition mview : word -> option byte := view LV mo FULL.

Definition METAB : Z := 4096 * bv_unsigned (ev E (MV w)).
Definition GRPBx : Z := 4096 * bv_unsigned (ev E (GV w)).

Lemma META_O_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.
Lemma pge_meta : bv_unsigned (edenot E (PGE (MV w))) = METAB /\ 4096 <= METAB /\ METAB + 8192 <= 2^47.
Proof.
pose proof (MA pv_bound _ META_O_in) as B. pose proof (MA u_obj_base _ META_O_in) as U.
pose proof (MA entry_top _ ((MA in_maps_obj) _ META_O_in)) as T. unfold METAB.
destruct w; cbn [META_O MV fst snd obj_e] in *; unfold MV_A, MV_B, PGE; (split; [exact U|]); rewrite ?U in T; cbn [fst snd] in T; lia.
Qed.
Lemma pge_grp : bv_unsigned (edenot E (PGE (GV w))) = GRPBx /\ 4096 <= GRPBx /\ GRPBx + 4096 <= 2^47.
Proof.
pose proof (MA pv_bound _ (GRP_O_in w)) as B. pose proof (MA u_obj_base _ (GRP_O_in w)) as U.
pose proof (MA entry_top _ ((MA in_maps_obj) _ (GRP_O_in w))) as T. unfold GRPBx.
destruct w; cbn [GRP_O GV fst snd obj_e] in *; unfold GV_A, GV_B, PGE; (split; [exact U|]); rewrite ?U in T; cbn [fst snd] in T; lia.
Qed.

Lemma lit_chunk : forall A cs n, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JO6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
QZDE.bytes_at JO6SEGS mview A (sc_bytes JO6SEGS E A cs) /\ QZDE.wr_at JO6SEGS mview A (Z.of_nat n).
Proof.
intros A cs n C W L H0 H1. split.
- pose proof (cells_check_sound JO6SEGS E mview (kn_view ch) (MV4 main_know_view) cs (ELit 0) A C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X. apply X; assumption.
- exact (img_w_b_sound JO6SEGS n A mview W H0 H1).
Qed.

Theorem small_bytes :
(QZDE.bytes_at JO6SEGS mview 0x6430f3 (sc_bytes JO6SEGS E 0x6430f3 (NLc w)) /\ QZDE.wr_at JO6SEGS mview 0x6430f3 1)
/\ (QZDE.bytes_at JO6SEGS mview 0x643120 (sc_bytes JO6SEGS E 0x643120 (PGSZc w)) /\ QZDE.wr_at JO6SEGS mview 0x643120 8)
/\ (QZDE.bytes_at JO6SEGS mview 0xe6b80 (sc_bytes JO6SEGS E 0xe6b80 (GOTSSPc w)) /\ QZDE.wr_at JO6SEGS mview 0xe6b80 8)
/\ (QZDE.bytes_at JO6SEGS mview 0x642ea0 (sc_bytes JO6SEGS E 0x642ea0 (SSPGc w)) /\ QZDE.wr_at JO6SEGS mview 0x642ea0 8)
/\ (QZDE.bytes_at JO6SEGS mview 0x6446f8 (sc_bytes JO6SEGS E 0x6446f8 (VMLc w)) /\ QZDE.wr_at JO6SEGS mview 0x6446f8 4).
Proof.
destruct (CHECKS w ch HCL) as (_ & C1 & C2 & C3 & C4 & C5 & _). destruct SMALL_w as (W1 & W2 & W3 & W4 & W5).
split; [exact (lit_chunk _ _ 1 C1 W1 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C2 W2 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C3 W3 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C4 W4 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
exact (lit_chunk _ _ 4 C5 W5 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
Qed.
Lemma scs_len_META : scs_len (METAc w) = 4096%nat.  Proof. destruct w; vm_compute; reflexivity. Qed.
Lemma scs_len_GRP : scs_len (GRPc w) = 4096%nat.  Proof. destruct w; vm_compute; reflexivity. Qed.
Theorem meta_bytes : QZDE.bytes_at JO6SEGS mview (METAB + 4096) (sc_bytes JO6SEGS E (METAB + 4096) (METAc w)) /\ QZDE.wr_at JO6SEGS mview (METAB + 4096) 4096.
Proof.
destruct (CHECKS w ch HCL) as (_ & _ & _ & _ & _ & _ & C & _ & CW & _). destruct pge_meta as (U & B1 & B2). pose proof (MV4 main_know_view) as KV.
pose proof (cells_check_sound JO6SEGS E mview (kn_view ch) KV (METAc w) (PGE (MV w)) 4096 C) as X. cbv zeta in X. rewrite U, scs_len_META in X.
pose proof (wr_check_sound JO6SEGS E mview (kn_view ch) KV (PGE (MV w)) 4096 4096 CW ltac:(lia)) as Y. rewrite U in Y.
split; [apply X; lia | exact Y].
Qed.
Theorem grp_bytes : QZDE.bytes_at JO6SEGS mview GRPBx (sc_bytes JO6SEGS E GRPBx (GRPc w)) /\ QZDE.wr_at JO6SEGS mview GRPBx 4096.
Proof.
destruct (CHECKS w ch HCL) as (_ & _ & _ & _ & _ & _ & _ & C & _ & CW). destruct pge_grp as (U & B1 & B2). pose proof (MV4 main_know_view) as KV.
pose proof (cells_check_sound JO6SEGS E mview (kn_view ch) KV (GRPc w) (PGE (GV w)) 0 C) as X. cbv zeta in X. rewrite U, Z.add_0_r, scs_len_GRP in X.
pose proof (wr_check_sound JO6SEGS E mview (kn_view ch) KV (PGE (GV w)) 0 4096 CW ltac:(lia)) as Y. rewrite U, Z.add_0_r in Y.
split; [apply X; lia | exact Y].
Qed.
End HeapCells.
End Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QlHe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QvSK.Mq0 QlHe.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Definition MV (w : bool) : nat := if w then MV_A else MV_B.
Definition GV (w : bool) : nat := if w then GV_A else GV_B.
Definition CTXc (w : bool) := if w then CTX_A else CTX_B.
Definition NLc (w : bool) := if w then NL_A else NL_B.
Definition PGSZc (w : bool) := if w then PGSZ_A else PGSZ_B.
Definition GOTSSPc (w : bool) := if w then GOTSSP_A else GOTSSP_B.
Definition SSPGc (w : bool) := if w then SSPG_A else SSPG_B.
Definition VMLc (w : bool) := if w then VML_A else VML_B.
Definition METAc (w : bool) := if w then META_A else META_B.
Definition GRPc (w : bool) := if w then GRP_A else GRP_B.
Definition PGE (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).

Lemma CHECKS : forall w ch, HSCLASS_S w ch ->
cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x6458a0 (CTXc w) = true /\ cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x6457b3 (NLc w) = true
/\ cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x6457e0 (PGSZc w) = true /\ cells_check JOB6SEGS (kn_view ch) (ELit 0) 0xe8f90 (GOTSSPc w) = true
/\ cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x645560 (SSPGc w) = true /\ cells_check JOB6SEGS (kn_view ch) (ELit 0) 0x646db8 (VMLc w) = true
/\ cells_check JOB6SEGS (kn_view ch) (PGE (MV w)) 4096 (METAc w) = true /\ cells_check JOB6SEGS (kn_view ch) (PGE (GV w)) 0 (GRPc w) = true
/\ wr_check (kn_view ch) (PGE (MV w)) 4096 4096 = true /\ wr_check (kn_view ch) (PGE (GV w)) 0 4096 = true.
Proof.
intros [|] ch [-> | ->]; cbn [CTXc NLc PGSZc GOTSSPc SSPGc VMLc METAc GRPc MV GV].
- exact (conj CTX_HS2sA_1_ok (conj NL_HS2sA_1_ok (conj PGSZ_HS2sA_1_ok (conj GOTSSP_HS2sA_1_ok (conj SSPG_HS2sA_1_ok (conj VML_HS2sA_1_ok (conj META_HS2sA_1_ok (conj GRP_HS2sA_1_ok (conj METAW_HS2sA_1_ok GRPW_HS2sA_1_ok))))))))).
- exact (conj CTX_HS2sA_2_ok (conj NL_HS2sA_2_ok (conj PGSZ_HS2sA_2_ok (conj GOTSSP_HS2sA_2_ok (conj SSPG_HS2sA_2_ok (conj VML_HS2sA_2_ok (conj META_HS2sA_2_ok (conj GRP_HS2sA_2_ok (conj METAW_HS2sA_2_ok GRPW_HS2sA_2_ok))))))))).
- exact (conj CTX_HS2sB_3_ok (conj NL_HS2sB_3_ok (conj PGSZ_HS2sB_3_ok (conj GOTSSP_HS2sB_3_ok (conj SSPG_HS2sB_3_ok (conj VML_HS2sB_3_ok (conj META_HS2sB_3_ok (conj GRP_HS2sB_3_ok (conj METAW_HS2sB_3_ok GRPW_HS2sB_3_ok))))))))).
- exact (conj CTX_HS2sB_4_ok (conj NL_HS2sB_4_ok (conj PGSZ_HS2sB_4_ok (conj GOTSSP_HS2sB_4_ok (conj SSPG_HS2sB_4_ok (conj VML_HS2sB_4_ok (conj META_HS2sB_4_ok (conj GRP_HS2sB_4_ok (conj METAW_HS2sB_4_ok GRPW_HS2sB_4_ok))))))))).
Qed.

Lemma SMALL_w : img_w_b JOB6SEGS 0x6457b3 1 = true /\ img_w_b JOB6SEGS 0x6457e0 8 = true /\ img_w_b JOB6SEGS 0xe8f90 8 = true
/\ img_w_b JOB6SEGS 0x645560 8 = true /\ img_w_b JOB6SEGS 0x646db8 4 = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section HeapCells.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).

Definition mview : word -> option byte := view LV mo FULL.

Definition METAB : Z := 4096 * bv_unsigned (ev E (MV w)).
Definition GRPBx : Z := 4096 * bv_unsigned (ev E (GV w)).

Lemma META_O_in : In (META_O w) (OBJS_W w).  Proof. destruct w; cbn; tauto. Qed.
Lemma pge_meta : bv_unsigned (edenot E (PGE (MV w))) = METAB /\ 4096 <= METAB /\ METAB + 8192 <= 2^47.
Proof.
pose proof (MA pv_bound _ META_O_in) as B. pose proof (MA u_obj_base _ META_O_in) as U.
pose proof (MA entry_top _ ((MA in_maps_obj) _ META_O_in)) as T. unfold METAB.
destruct w; cbn [META_O MV fst snd obj_e] in *; unfold MV_A, MV_B, PGE; (split; [exact U|]); rewrite ?U in T; cbn [fst snd] in T; lia.
Qed.
Lemma pge_grp : bv_unsigned (edenot E (PGE (GV w))) = GRPBx /\ 4096 <= GRPBx /\ GRPBx + 4096 <= 2^47.
Proof.
pose proof (MA pv_bound _ (GRP_O_in w)) as B. pose proof (MA u_obj_base _ (GRP_O_in w)) as U.
pose proof (MA entry_top _ ((MA in_maps_obj) _ (GRP_O_in w))) as T. unfold GRPBx.
destruct w; cbn [GRP_O GV fst snd obj_e] in *; unfold GV_A, GV_B, PGE; (split; [exact U|]); rewrite ?U in T; cbn [fst snd] in T; lia.
Qed.

Lemma lit_chunk : forall A cs n, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JOB6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
QZDE.bytes_at JOB6SEGS mview A (sc_bytes JOB6SEGS E A cs) /\ QZDE.wr_at JOB6SEGS mview A (Z.of_nat n).
Proof.
intros A cs n C W L H0 H1. split.
- pose proof (cells_check_sound JOB6SEGS E mview (kn_view ch) (MV4 main_know_view) cs (ELit 0) A C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X. apply X; assumption.
- exact (img_w_b_sound JOB6SEGS n A mview W H0 H1).
Qed.

Theorem small_bytes :
(QZDE.bytes_at JOB6SEGS mview 0x6457b3 (sc_bytes JOB6SEGS E 0x6457b3 (NLc w)) /\ QZDE.wr_at JOB6SEGS mview 0x6457b3 1)
/\ (QZDE.bytes_at JOB6SEGS mview 0x6457e0 (sc_bytes JOB6SEGS E 0x6457e0 (PGSZc w)) /\ QZDE.wr_at JOB6SEGS mview 0x6457e0 8)
/\ (QZDE.bytes_at JOB6SEGS mview 0xe8f90 (sc_bytes JOB6SEGS E 0xe8f90 (GOTSSPc w)) /\ QZDE.wr_at JOB6SEGS mview 0xe8f90 8)
/\ (QZDE.bytes_at JOB6SEGS mview 0x645560 (sc_bytes JOB6SEGS E 0x645560 (SSPGc w)) /\ QZDE.wr_at JOB6SEGS mview 0x645560 8)
/\ (QZDE.bytes_at JOB6SEGS mview 0x646db8 (sc_bytes JOB6SEGS E 0x646db8 (VMLc w)) /\ QZDE.wr_at JOB6SEGS mview 0x646db8 4).
Proof.
destruct (CHECKS w ch HCL) as (_ & C1 & C2 & C3 & C4 & C5 & _). destruct SMALL_w as (W1 & W2 & W3 & W4 & W5).
split; [exact (lit_chunk _ _ 1 C1 W1 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C2 W2 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C3 W3 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
split; [exact (lit_chunk _ _ 8 C4 W4 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia))|].
exact (lit_chunk _ _ 4 C5 W5 ltac:(destruct w; vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
Qed.
Lemma scs_len_META : scs_len (METAc w) = 4096%nat.  Proof. destruct w; vm_compute; reflexivity. Qed.
Lemma scs_len_GRP : scs_len (GRPc w) = 4096%nat.  Proof. destruct w; vm_compute; reflexivity. Qed.
Theorem meta_bytes : QZDE.bytes_at JOB6SEGS mview (METAB + 4096) (sc_bytes JOB6SEGS E (METAB + 4096) (METAc w)) /\ QZDE.wr_at JOB6SEGS mview (METAB + 4096) 4096.
Proof.
destruct (CHECKS w ch HCL) as (_ & _ & _ & _ & _ & _ & C & _ & CW & _). destruct pge_meta as (U & B1 & B2). pose proof (MV4 main_know_view) as KV.
pose proof (cells_check_sound JOB6SEGS E mview (kn_view ch) KV (METAc w) (PGE (MV w)) 4096 C) as X. cbv zeta in X. rewrite U, scs_len_META in X.
pose proof (wr_check_sound JOB6SEGS E mview (kn_view ch) KV (PGE (MV w)) 4096 4096 CW ltac:(lia)) as Y. rewrite U in Y.
split; [apply X; lia | exact Y].
Qed.
Theorem grp_bytes : QZDE.bytes_at JOB6SEGS mview GRPBx (sc_bytes JOB6SEGS E GRPBx (GRPc w)) /\ QZDE.wr_at JOB6SEGS mview GRPBx 4096.
Proof.
destruct (CHECKS w ch HCL) as (_ & _ & _ & _ & _ & _ & _ & C & _ & CW). destruct pge_grp as (U & B1 & B2). pose proof (MV4 main_know_view) as KV.
pose proof (cells_check_sound JOB6SEGS E mview (kn_view ch) KV (GRPc w) (PGE (GV w)) 0 C) as X. cbv zeta in X. rewrite U, Z.add_0_r, scs_len_GRP in X.
pose proof (wr_check_sound JOB6SEGS E mview (kn_view ch) KV (PGE (GV w)) 0 4096 CW ltac:(lia)) as Y. rewrite U, Z.add_0_r in Y.
split; [apply X; lia | exact Y].
Qed.
End HeapCells.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc QBrp Q1KO QOb0 QPa2 Q6sh QzgH Q7z8 QvDJ QKTr Qqcs QNLn Qi08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q1KO.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi.

Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Definition KZ_GRP (w : bool) : kentry :=
KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar (fst (GRP_O w)))) 2147450880) (ELit 512).
Lemma KZ_GRP_in : forall w ch, HSCLASS_S w ch -> In (KZ_GRP w) (kn_rest ch).
Proof. intros w ch HCL. apply kn_mem_In. destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.

Section Kla.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation h := (m_vmmaps mo).
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation GB := (GRPB E w) (only parsing).
#[local] Notation PERM0 := (PERM0_J E w) (only parsing).

Lemma grp_facts : 0 < GB /\ GB mod 4096 = 0 /\ GB + 4096 <= alloc_top h
/\ (GB + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= GB) /\ (GB + 4096 <= 0x10000 \/ 0x647000 <= GB)
/\ obj_e E (GRP_O w) = QzgH.cent (GB, 4096).
Proof.
pose proof ((MA pv_bound) _ (GRP_O_in w)) as PB. pose proof ((MA obj_lowhigh) _ (GRP_O_in w)) as LH.
pose proof ((MA entry_top) _ ((MA in_maps_obj) _ (GRP_O_in w))) as T.
pose proof (P co_bounds) as B. rewrite Forall_forall in B. pose proof (B _ ((MA in_maps_obj) _ (GRP_O_in w))) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi BJO6] in B4.
rewrite ((MA u_obj_base) _ (GRP_O_in w)), ((MA u_obj_len) _ (GRP_O_in w)) in LH, T, B4.
unfold QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg in LH.
assert (HL : snd (GRP_O w) = 4096) by (destruct w; reflexivity). rewrite HL in LH, T, B4.
unfold GRPB. split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [exact T|]. split; [exact LH|]. split; [exact B4|].
unfold QzgH.cent, QzgH.w64, obj_e. cbn [fst snd edenot]. rewrite HL.
f_equal; try (apply bv_eq; rewrite u_mul64, !u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
Qed.

Lemma gstatic_grp : QNLn.Mq0.gstatic LV PERM0 GB 4096.
Proof.
destruct grp_facts as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
unfold QNLn.Mq0.gstatic. split; [reflexivity|]. split; [unfold QvDJ.kMaxChunk; lia|]. split; [exact G1|]. split; [exact G2|].
split; [unfold QzgH.kLowEnd, QzgH.KHI, Qqcs.Mq0.kHighMemBeg; lia|].
split; [rewrite QzgH.kCeil_val; lia|].
split; [|split].
- rewrite <- G6. destruct ((MA obj_ne) _ (GRP_O_in w)) as (N1 & N2 & N3).
exact ((MA not_excl) _ ((MA in_maps_obj) _ (GRP_O_in w)) N1 N2 N3).
- intros iv y Hiv Hy. unfold LV_J, L_main_job6 in Hiv |- *. cbn [lv_base In] in Hiv. unfold shz. cbn [lv_shoff].
rewrite <- (MA main_atop) in G3, AB.
assert (Hq : 0 <= y / 8 < 0x100000000000) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; split; lia.
-
intros Hin. assert (Hc : In (QvDJ.civ (GB, 4096)) (PERMc_J E w)) by (right; exact Hin).
unfold PERM0_J, Q7z8.PERM_main in Hin. rewrite (MA grp_obj) in Hin.
assert (NE : forall e, In e (vm_maps h) -> e <> obj_e E (GRP_O w) -> wiv2z e <> wiv2z (obj_e E (GRP_O w))).
{ intros e He Hne Heq. pose proof ((MA maps_disj) _ _ He ((MA in_maps_obj) _ (GRP_O_in w)) Hne) as D.
pose proof ((MA maps_pos) _ He) as P1. unfold iv_disjoint in D.
pose proof (f_equal fst Heq) as E1. pose proof (f_equal snd Heq) as E2. unfold wiv2z in E1, E2. cbn [fst snd] in E1, E2. lia. }
assert (NO : forall o, In o (OBJS_W w) -> o <> GRP_O w -> wiv2z (obj_e E o) <> wiv2z (obj_e E (GRP_O w))).
{ intros o Ho Hne. apply NE; [exact ((MA in_maps_obj) o Ho)|]. intros Heq. apply Hne. exact ((MA obj_e_inj) _ _ Ho (GRP_O_in w) Heq). }
destruct ((MA obj_ne) _ (GRP_O_in w)) as (N1 & N2 & N3).
apply in_app_iff in Hin as [Hin|Hin].
+ cbn [In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
* rewrite (MA pres_obj) in Hin. revert Hin. apply NO; [exact (PRES_O_in w) | destruct w; discriminate].
* rewrite (MA parr_obj) in Hin. revert Hin. apply NO; [exact (PARR_O_in w) | destruct w; discriminate].
* replace Q7z8.band_hi with (wiv2z (e_high E)) in Hin by (rewrite (MA e_high_z); reflexivity). revert Hin.
apply NE; [exact (MA e_high_in) | intros X; apply N3; symmetry; exact X].
* replace Q7z8.band_lo with (wiv2z (e_low E)) in Hin by (rewrite (MA e_low_z); reflexivity). revert Hin.
apply NE; [exact (MA e_low_in) | intros X; apply N1; symmetry; exact X].
* replace Q7z8.band_gap with (wiv2z (e_gap E)) in Hin by (rewrite (MA e_gap_z); reflexivity). revert Hin.
apply NE; [exact (MA e_gap_in) | intros X; apply N2; symmetry; exact X].
+ unfold objs_of in Hin. apply in_map_iff in Hin as (o & Heq & Ho).
assert (Hne : o <> GRP_O w) by (intros ->; destruct w; cbn in Ho; repeat (destruct Ho as [Ho|Ho]; [discriminate Ho|]); exact Ho).
exact (NO o (OBJS_K_sub w o Ho) Hne Heq).
Qed.

Lemma grp_shadow_mem : forall y : word, QNLn.Mq0.in_sh GB 4096 y = true -> view LV mo FULL y = Some (Z_to_bv 8 0).
Proof.
intros y Hy. destruct grp_facts as (G1 & G2 & G3 & _).
pose proof ((MA pv_bound) _ (GRP_O_in w)) as PB.
pose proof (MV4 main_know_view) as KV. unfold know_ok in KV. rewrite Forall_forall in KV.
assert (IK : In (KZ_GRP w) (kn_view ch)) by (right; right; exact (KZ_GRP_in w ch HCL)).
pose proof (KV _ IK) as [_ KZ]. unfold estart, elenZ in KZ. cbn [a_base a_off edenot] in KZ.
rewrite u_mul64, !u64_lit in KZ by lia. rewrite (Z.mod_small (512 * _)) in KZ by lia.
unfold QNLn.Mq0.in_sh, QKTr.sh_lo, QKTr.sh_hi, Q6sh.kShadowOffset in Hy. rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl) in Hy.
apply andb_prop in Hy as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2.
assert (D1 : GB / 8 = 512 * bv_unsigned (ev E (fst (GRP_O w)))).
{ unfold GRPB. replace (4096 * bv_unsigned (ev E (fst (GRP_O w)))) with (512 * bv_unsigned (ev E (fst (GRP_O w))) * 8) by lia. apply Z.div_mul. lia. }
assert (D2 : (GB + 4096 - 1) / 8 = 512 * bv_unsigned (ev E (fst (GRP_O w))) + 511).
{ unfold GRPB. replace (4096 * bv_unsigned (ev E (fst (GRP_O w))) + 4096 - 1) with ((512 * bv_unsigned (ev E (fst (GRP_O w))) + 511) * 8 + 7) by lia.
rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
rewrite D1 in Y1. rewrite D2 in Y2.
specialize (KZ (bv_unsigned y - (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880)) ltac:(lia)).
replace (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880 + (bv_unsigned y - (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880)))
with (bv_unsigned y) in KZ by lia.
rewrite Z_to_bv_bv_unsigned in KZ. exact KZ.
Qed.

Lemma meta_perm : In (wiv2z (obj_e E (META_O w))) PERM0.
Proof. unfold PERM0_J, Q7z8.PERM_main, objs_of. apply in_app_iff. right. apply in_map_iff. exists (META_O w). split; [reflexivity | cbn; tauto]. Qed.

Theorem KLA_main_J : forall {RC__ : QNLn.Mq0.RC.RunConsts} (Lg0 : QNLn.Mq0.KV.mled) (g0 : QvDJ.ghost) (ms : machine_state),
QNLn.Mq0.RC.alloc_ceiling = atopE E ->
ms_mem ms = FULL ->
QNLn.Mq0.KV.ld_groups Lg0 = [(GB, 4096)] ->
QvDJ.g_chunks g0 = [] -> 0 <= QvDJ.g_spent g0 ->
(forall r, In r (QNLn.Mq0.oranges Lg0) -> QNLn.Mq0.ocov PERM0 h r) ->
QNLn.Mq0.KLA LV PERM0 Qi08.TMAX_J Qi08.NMAX_J (fun _ => false) Lg0 g0 (mkCfg ms mo) (QNLn.Mq0.in_sh GB 4096) (view LV mo FULL) BC_J TOT_J 22.
Proof.
intros RC__ Lg0 g0 ms HRC Hms HG Hch Hsp0 HCOV.
destruct grp_facts as (G1 & G2 & G3 & _).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
constructor; cbn [cfg_ms cfg_model].
- unfold QNLn.Mq0.PERMc. rewrite HG. cbn [map app]. exact ((MA KI_main_J) g0 Hch Hsp0).
- rewrite HG. cbn [map snd]. unfold BC_J, TOT_J, Qi08.TMAX_J, Qi08.NMAX_J, QOb0.Mq0.zlen. cbn. lia.
- exact ((MA main_cinvA) ms Hms).
- exact (P co_halt).
- rewrite HRC. symmetry. exact (MA main_atop).
- intros b l Hin. rewrite HG in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. exact gstatic_grp.
- exact HCOV.
- rewrite HG. cbn [map fst]. constructor; [intros []| constructor].
- intros y Hy. apply (QNLn.Mq0.in_sh_bounds GB 4096 y); [lia | rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl); lia | | exact Hy].
rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl), QzgH.kCeil_val. lia.
- intros y Hy. rewrite (grp_shadow_mem y Hy). discriminate.
- intros b l y Hin Hy. rewrite HG in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. exact Hy.
- intros y Hy. exists GB, 4096. split; [rewrite HG; left; reflexivity | exact Hy].
- intros y Hy. discriminate Hy.
Qed.
End Kla.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Definition KZ_GRP (w : bool) : kentry :=
KZero (SA (EMd Instr.M_MUL (ELit 512) (EVar (fst (GRP_O w)))) 2147450880) (ELit 512).
Lemma KZ_GRP_in : forall w ch, HSCLASS_S w ch -> In (KZ_GRP w) (kn_rest ch).
Proof. intros w ch HCL. apply kn_mem_In. destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.

Section Kla.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation h := (m_vmmaps mo).
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation GB := (GRPB E w) (only parsing).
#[local] Notation PERM0 := (PERM0_J E w) (only parsing).

Lemma grp_facts : 0 < GB /\ GB mod 4096 = 0 /\ GB + 4096 <= alloc_top h
/\ (GB + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= GB) /\ (GB + 4096 <= 0x10000 \/ 0x645000 <= GB)
/\ obj_e E (GRP_O w) = QzgH.cent (GB, 4096).
Proof.
pose proof ((MA pv_bound) _ (GRP_O_in w)) as PB. pose proof ((MA obj_lowhigh) _ (GRP_O_in w)) as LH.
pose proof ((MA entry_top) _ ((MA in_maps_obj) _ (GRP_O_in w))) as T.
pose proof (P co_bounds) as B. rewrite Forall_forall in B. pose proof (B _ ((MA in_maps_obj) _ (GRP_O_in w))) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi AJO6] in B4.
rewrite ((MA u_obj_base) _ (GRP_O_in w)), ((MA u_obj_len) _ (GRP_O_in w)) in LH, T, B4.
unfold QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg in LH.
assert (HL : snd (GRP_O w) = 4096) by (destruct w; reflexivity). rewrite HL in LH, T, B4.
unfold GRPB. split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [exact T|]. split; [exact LH|]. split; [exact B4|].
unfold QzgH.cent, QzgH.w64, obj_e. cbn [fst snd edenot]. rewrite HL.
f_equal; try (apply bv_eq; rewrite u_mul64, !u64_lit by lia; rewrite Z.mod_small by lia; reflexivity).
Qed.

Lemma gstatic_grp : QNLn.Mq0.gstatic LV PERM0 GB 4096.
Proof.
destruct grp_facts as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
unfold QNLn.Mq0.gstatic. split; [reflexivity|]. split; [unfold QvDJ.kMaxChunk; lia|]. split; [exact G1|]. split; [exact G2|].
split; [unfold QzgH.kLowEnd, QzgH.KHI, Qqcs.Mq0.kHighMemBeg; lia|].
split; [rewrite QzgH.kCeil_val; lia|].
split; [|split].
- rewrite <- G6. destruct ((MA obj_ne) _ (GRP_O_in w)) as (N1 & N2 & N3).
exact ((MA not_excl) _ ((MA in_maps_obj) _ (GRP_O_in w)) N1 N2 N3).
- intros iv y Hiv Hy. unfold LV_J, L_main_jo6 in Hiv |- *. cbn [lv_base In] in Hiv. unfold shz. cbn [lv_shoff].
rewrite <- (MA main_atop) in G3, AB.
assert (Hq : 0 <= y / 8 < 0x100000000000) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
destruct Hiv as [<-|[<-|[]]]; cbn [fst snd]; split; lia.
-
intros Hin. assert (Hc : In (QvDJ.civ (GB, 4096)) (PERMc_J E w)) by (right; exact Hin).
unfold PERM0_J, Q7z8.PERM_main in Hin. rewrite (MA grp_obj) in Hin.
assert (NE : forall e, In e (vm_maps h) -> e <> obj_e E (GRP_O w) -> wiv2z e <> wiv2z (obj_e E (GRP_O w))).
{ intros e He Hne Heq. pose proof ((MA maps_disj) _ _ He ((MA in_maps_obj) _ (GRP_O_in w)) Hne) as D.
pose proof ((MA maps_pos) _ He) as P1. unfold iv_disjoint in D.
pose proof (f_equal fst Heq) as E1. pose proof (f_equal snd Heq) as E2. unfold wiv2z in E1, E2. cbn [fst snd] in E1, E2. lia. }
assert (NO : forall o, In o (OBJS_W w) -> o <> GRP_O w -> wiv2z (obj_e E o) <> wiv2z (obj_e E (GRP_O w))).
{ intros o Ho Hne. apply NE; [exact ((MA in_maps_obj) o Ho)|]. intros Heq. apply Hne. exact ((MA obj_e_inj) _ _ Ho (GRP_O_in w) Heq). }
destruct ((MA obj_ne) _ (GRP_O_in w)) as (N1 & N2 & N3).
apply in_app_iff in Hin as [Hin|Hin].
+ cbn [In] in Hin. destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]].
* rewrite (MA pres_obj) in Hin. revert Hin. apply NO; [exact (PRES_O_in w) | destruct w; discriminate].
* rewrite (MA parr_obj) in Hin. revert Hin. apply NO; [exact (PARR_O_in w) | destruct w; discriminate].
* replace Q7z8.band_hi with (wiv2z (e_high E)) in Hin by (rewrite (MA e_high_z); reflexivity). revert Hin.
apply NE; [exact (MA e_high_in) | intros X; apply N3; symmetry; exact X].
* replace Q7z8.band_lo with (wiv2z (e_low E)) in Hin by (rewrite (MA e_low_z); reflexivity). revert Hin.
apply NE; [exact (MA e_low_in) | intros X; apply N1; symmetry; exact X].
* replace Q7z8.band_gap with (wiv2z (e_gap E)) in Hin by (rewrite (MA e_gap_z); reflexivity). revert Hin.
apply NE; [exact (MA e_gap_in) | intros X; apply N2; symmetry; exact X].
+ unfold objs_of in Hin. apply in_map_iff in Hin as (o & Heq & Ho).
assert (Hne : o <> GRP_O w) by (intros ->; destruct w; cbn in Ho; repeat (destruct Ho as [Ho|Ho]; [discriminate Ho|]); exact Ho).
exact (NO o (OBJS_K_sub w o Ho) Hne Heq).
Qed.

Lemma grp_shadow_mem : forall y : word, QNLn.Mq0.in_sh GB 4096 y = true -> view LV mo FULL y = Some (Z_to_bv 8 0).
Proof.
intros y Hy. destruct grp_facts as (G1 & G2 & G3 & _).
pose proof ((MA pv_bound) _ (GRP_O_in w)) as PB.
pose proof (MV4 main_know_view) as KV. unfold know_ok in KV. rewrite Forall_forall in KV.
assert (IK : In (KZ_GRP w) (kn_view ch)) by (right; right; exact (KZ_GRP_in w ch HCL)).
pose proof (KV _ IK) as [_ KZ]. unfold estart, elenZ in KZ. cbn [a_base a_off edenot] in KZ.
rewrite u_mul64, !u64_lit in KZ by lia. rewrite (Z.mod_small (512 * _)) in KZ by lia.
unfold QNLn.Mq0.in_sh, QKTr.sh_lo, QKTr.sh_hi, Q6sh.kShadowOffset in Hy. rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl) in Hy.
apply andb_prop in Hy as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.ltb_lt in Y2.
assert (D1 : GB / 8 = 512 * bv_unsigned (ev E (fst (GRP_O w)))).
{ unfold GRPB. replace (4096 * bv_unsigned (ev E (fst (GRP_O w)))) with (512 * bv_unsigned (ev E (fst (GRP_O w))) * 8) by lia. apply Z.div_mul. lia. }
assert (D2 : (GB + 4096 - 1) / 8 = 512 * bv_unsigned (ev E (fst (GRP_O w))) + 511).
{ unfold GRPB. replace (4096 * bv_unsigned (ev E (fst (GRP_O w))) + 4096 - 1) with ((512 * bv_unsigned (ev E (fst (GRP_O w))) + 511) * 8 + 7) by lia.
rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
rewrite D1 in Y1. rewrite D2 in Y2.
specialize (KZ (bv_unsigned y - (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880)) ltac:(lia)).
replace (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880 + (bv_unsigned y - (512 * bv_unsigned (ev E (fst (GRP_O w))) + 2147450880)))
with (bv_unsigned y) in KZ by lia.
rewrite Z_to_bv_bv_unsigned in KZ. exact KZ.
Qed.

Lemma meta_perm : In (wiv2z (obj_e E (META_O w))) PERM0.
Proof. unfold PERM0_J, Q7z8.PERM_main, objs_of. apply in_app_iff. right. apply in_map_iff. exists (META_O w). split; [reflexivity | cbn; tauto]. Qed.

Theorem KLA_main_J : forall {RC__ : QNLn.Mq0.RC.RunConsts} (Lg0 : QNLn.Mq0.KV.mled) (g0 : QvDJ.ghost) (ms : machine_state),
QNLn.Mq0.RC.alloc_ceiling = atopE E ->
ms_mem ms = FULL ->
QNLn.Mq0.KV.ld_groups Lg0 = [(GB, 4096)] ->
QvDJ.g_chunks g0 = [] -> 0 <= QvDJ.g_spent g0 ->
(forall r, In r (QNLn.Mq0.oranges Lg0) -> QNLn.Mq0.ocov PERM0 h r) ->
QNLn.Mq0.KLA LV PERM0 QVyC.TMAX_J QVyC.NMAX_J (fun _ => false) Lg0 g0 (mkCfg ms mo) (QNLn.Mq0.in_sh GB 4096) (view LV mo FULL) BC_J TOT_J 22.
Proof.
intros RC__ Lg0 g0 ms HRC Hms HG Hch Hsp0 HCOV.
destruct grp_facts as (G1 & G2 & G3 & _).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
constructor; cbn [cfg_ms cfg_model].
- unfold QNLn.Mq0.PERMc. rewrite HG. cbn [map app]. exact ((MA KI_main_J) g0 Hch Hsp0).
- rewrite HG. cbn [map snd]. unfold BC_J, TOT_J, QVyC.TMAX_J, QVyC.NMAX_J, QOb0.Mq0.zlen. cbn. lia.
- exact ((MA main_cinvA) ms Hms).
- exact (P co_halt).
- rewrite HRC. symmetry. exact (MA main_atop).
- intros b l Hin. rewrite HG in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. exact gstatic_grp.
- exact HCOV.
- rewrite HG. cbn [map fst]. constructor; [intros []| constructor].
- intros y Hy. apply (QNLn.Mq0.in_sh_bounds GB 4096 y); [lia | rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl); lia | | exact Hy].
rewrite (QNLn.Mq0.mmap_len_aligned 4096 eq_refl), QzgH.kCeil_val. lia.
- intros y Hy. rewrite (grp_shadow_mem y Hy). discriminate.
- intros b l y Hin Hy. rewrite HG in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. exact Hy.
- intros y Hy. exists GB, 4096. split; [rewrite HG; left; reflexivity | exact Hy].
- intros y Hy. discriminate Hy.
Qed.
End Kla.
