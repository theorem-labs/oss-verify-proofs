(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE QWxq QlEo QbVh QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz Uv2Y UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QRjH QBxa QSpR QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90 U9ch UleT UmsF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj Uc9I U4FC Uqqm UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.

Import UKNz Uv2Y UXT6.
Import QsRG.Mq0 Qnhz.Mq0 QRjH QBxa.Mq5 QSpR.Mq1 QuJV.Mq0.
Import Um90.Mq0 U9ch.Mq0 UleT.Mq0 UleT.Mq1 UmsF.Mq0.
Import QeZD QqWy.
Import UmAj Uc9I.
Import U4FC Uqqm UDH9.
Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Lemma PRIS_re_ivs : PRIS = U9ch.Mq0.re_ivs. Proof. reflexivity. Qed.

Section Leaf.
Context {AMB : Amb}.
Variables (usp0 pp tid : Z) (path : list byte).
Let sp0w : word := Z_to_bv 64 usp0.

#[using="Type"] Lemma cell_of_bytes_at : forall (m : mem) a n (v : Z),
QZDE.bytes_at rsegs m a (word_to_le_bytes n (Z_to_bv 64 v)) -> 0 <= a < 2^64 -> cell m a n v.
Proof.
intros m a n v H Ha. unfold cell. pose proof (bytes_at_rdn0 rsegs m a _ H) as R. rewrite length_N_to_le_bytes in R. exact R.
Qed.

#[using="Type"] Lemma leaf_facts : forall m A LB md,
DF usp0 pp tid path m -> HEAPc usp0 A LB m md ->
valid_sp sp0w /\ bv_unsigned sp0w = usp0
/\ stack_writable m sp0w
/\ Forall (fun iv => img_clear m (fst iv) (snd iv)) U9ch.Mq0.re_ivs
/\ cell m 0x77b58 4 tid /\ (0 < tid < 2^22)
/\ cell m 0x77b38 8 0x77b38 /\ cell m 0x97e70 8 (bv_unsigned rc_canary) /\ cell m 0x97ec0 8 4096.
Proof.
intros m A LB md D HP. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL].
assert (U : bv_unsigned sp0w = usp0) by (subst sp0w; apply unsigned_lit; lia).
split. { unfold valid_sp, sp_window_lo, sp_window_hi. rewrite U. lia. } split. { exact U. }
split. { intros d n Hd Hn. rewrite U.
pose proof (QZDE.wr_at_store_ok rsegs m (usp0 - 8388608) 8388608 d n) as W. unfold QZDE.wa in W. apply W; [| lia| lia].
destruct STK as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S3 (usp0 - 8388608 + i) ltac:(lia))). }
split. { rewrite <- PRIS_re_ivs. unfold pris in PRS. eapply Forall_impl; [| exact PRS]. intros [lo hi] H i Hi. exact (H i Hi). }
destruct TID as [T1 T2].
split. { apply cell_of_bytes_at; [exact T1| lia]. } split. { exact T2. }
split. { apply cell_of_bytes_at; [exact SELF| lia]. }
destruct (heapc_guard_cells usp0 A LB m md HP) as [_ [[_ GB] _]]. cbn [QbVh.cells_bytes QbVh.cbytes app] in GB. rewrite app_nil_r in GB.
pose proof (heapc_page_size usp0 A LB m md HP) as [[_ PB] _]. cbn [QbVh.cells_bytes QbVh.cbytes app] in PB. rewrite app_nil_r in PB.
split. { apply cell_of_bytes_at; [rewrite Z_to_bv_bv_unsigned; exact GB| unfold RSSP_GUARD; lia]. }
apply cell_of_bytes_at; [exact PB| unfold RPAGE_SIZE; lia].
Qed.

#[using="sp0w"] Lemma leaf_oom : leaf_oom_stmt usp0 pp tid path.
Proof.
unfold leaf_oom_stmt. intros until pc. intros D HP -> -> FD2 Hpc.
destruct (leaf_facts m A LB md D HP) as (VSP & U & STW & IMG & CT & HT & CS & CC & CPG).
pose proof (heapc_model_ok usp0 A LB m md HP) as [Hh Hl].
change (QEpW.MS ?R F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 pc) m (seg_rom rsegs)).
apply (ref_oom_tail (fF:=F) (fC:=fc) sp0w [] md VSP Hh Hl FD2 tid (bv_unsigned rc_canary) _ m); try assumption; cbn [getr]; rewrite ?U; reflexivity.
Qed.

#[using="sp0w"] Lemma leaf_refused : leaf_refused_stmt usp0 pp tid path.
Proof.
unfold leaf_refused_stmt. intros until LB. intros D HP -> -> FD2.
destruct (leaf_facts m A LB md D HP) as (VSP & U & STW & IMG & CT & HT & CS & CC & CPG).
pose proof (heapc_model_ok usp0 A LB m md HP) as [Hh Hl].
change (QEpW.MS ?R F (Z_to_bv 64 0x20dcc) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 0x20dcc) m (seg_rom rsegs)).
apply (ref_refused_tail (fF:=F) (fC:=fc) sp0w [] md VSP Hh Hl FD2 tid (bv_unsigned rc_canary) _ m); try assumption; cbn [getr]; rewrite ?U; reflexivity.
Qed.

#[using="sp0w"] Lemma leaf_readerr : leaf_readerr_stmt usp0 pp tid path.
Proof.
unfold leaf_readerr_stmt. intros until LB. intros D HP Hdot -> -> FD2.
destruct (leaf_facts m A LB md D HP) as (VSP & U & STW & IMG & CT & HT & CS & CC & CPG).
pose proof (heapc_model_ok usp0 A LB m md HP) as [Hh Hl].
destruct D as [SPB _ _ _ _ _ _ (P1 & P2 & P3) (t8 & Q1 & Q2) _ _]. rewrite Hdot in P1, P3, Q1. cbn [length app Z.of_nat Pos.of_succ_nat] in P1, P3, Q1.
change (QEpW.MS ?R F (Z_to_bv 64 0x20db0) fc None m (seg_rom rsegs)) with (@mkst F fc R (Z_to_bv 64 0x20db0) m (seg_rom rsegs)).
rewrite Hdot.
apply (ref_read_error_dot (fF:=F) (fC:=fc) sp0w [] md VSP Hh Hl FD2 (Z_to_bv 64 pp) tid (bv_unsigned rc_canary) _ m) with (t8 := t8); try assumption; try (cbn [getr]; rewrite ?U; reflexivity).
all: rewrite ?unsigned_lit by lia; rewrite ?U.
all: first [exact (bytes_at_rdn0 rsegs m pp _ P1) | rewrite <- Q2; exact (bytes_at_rdn0 rsegs m _ _ Q1) | lia | match goal with |- ?G => idtac "LEFT" G end].
Qed.
End Leaf.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma vm_only_fds : forall md md', QeZD.vm_only md md' -> m_fds md' = m_fds md.
Proof. intros md md' (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
Lemma vm_only_fs : forall md md', QeZD.vm_only md md' -> m_fs md' = m_fs md.
Proof. intros md md' (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.

Definition PRIS2 : list (Z * Z) :=
[(0x10000,0x658d8); (0x658e0,0x659d0); (0x659d8,0x66a30); (0x66a38,0x66a40); (0x66a48,0x66d38); (0x66e20,0x66e28); (0x66f10,0x66f20);
(0x66f31,0x66f79); (0x76f79,0x76f80); (0x76f81,0x76f84); (0x76f85,0x76fbc) ; (0x770bc,0x77b30) ;
(0x97c08,0x97c18); (0x77b64,0x77bb0); (0x77bb8,0x77bd0);
(0x77bd8,0x77bf0); (0x77c00,0x77c10); (0x77c20,0x97c08); (0x97c40,0x97c50); (0x97c54,0x97c58); (0x97c60,0x97c68); (0x97c70,0x97d68); (0x97d70,0x97e70)
; (0x97e78,0x97e80);
(0x97f00,0x97f78); (0x98320,0x98350); (0x98750,0x99000)].

Definition prisx (m : mem) : Prop :=
Forall (fun iv => forall a, fst iv <= a < snd iv -> m (wa a) = None) PRIS2.

Lemma pris_pointwise : forall m, pris m -> forall a,
((0x10000 <= a < 0x66f30) \/ (0x66f31 <= a < 0x66f79) \/ (0x76f79 <= a < 0x77b30) \/ (0x97c08 <= a < 0x97c18) \/ (0x77b64 <= a < 0x77bb0) \/ (0x77bb8 <= a < 0x77bd0) \/
(0x77bd8 <= a < 0x77bf0) \/ (0x77c00 <= a < 0x77c10) \/ (0x77c20 <= a < 0x97c08) \/ (0x97c40 <= a < 0x97e70) \/ (0x97e78 <= a < 0x97e80) \/ (0x97e91 <= a < 0x97e98) \/
(0x97ec8 <= a < 0x97ef8) \/ (0x97f00 <= a < 0x97f78) \/ (0x98320 <= a < 0x99000)) -> m (wa a) = None.
Proof.
intros m H a Ha. unfold pris, PRIS in H.
repeat match type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H as [? H] end. cbn [fst snd] in *.
repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end.
all: match goal with G : forall x : Z, _ -> ?mm (wa x) = None |- _ => exact (G a ltac:(lia)) end.
Qed.

Lemma pris_prisx : forall m, pris m -> prisx m.
Proof.
intros m H. pose proof (pris_pointwise m H) as PW. unfold prisx. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
apply PW. unfold PRIS2 in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
Qed.

Definition stdio_area (a : Z) : Prop :=
(0x66d38 <= a < 0x66e20) \/ (0x66e28 <= a < 0x66f10) \/ a = 0x76f80 \/ (0x98350 <= a < 0x98750)
\/ (0x659d0 <= a < 0x659d8) \/ (0x66a40 <= a < 0x66a44) \/ (0x66f20 <= a < 0x66f28) \/ (0x97e90 <= a < 0x97ef8)
\/ (0x658d8 <= a < 0x658e0) \/ (0x66a30 <= a < 0x66a38).

Definition atx_cell (a : Z) : Prop := (0x97c4c <= a < 0x97c70) \/ (0x97d68 <= a < 0x97d70) \/ a = 0x76f84.

Lemma atx_state_agree : forall armed (m m' : mem),
UFeQ.Mq0.atx_state armed m -> (forall x, atx_cell x -> m' (wa x) = m (wa x)) -> UFeQ.Mq0.atx_state armed m'.
Proof.
intros armed m m' A EQ.
assert (R : forall a n, (forall x, a <= x < a + Z.of_nat n -> atx_cell x) -> 0 <= a -> a + Z.of_nat n <= 0x99000 ->
rdn rsegs m' (Z_to_bv 64 a) n = rdn rsegs m (Z_to_bv 64 a) n).
{ intros a n H H0 H1. apply QsRG.Mq0.rdn_ext; rewrite unsigned_lit by lia; [lia|].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply EQ. apply H. lia. }
unfold UFeQ.Mq0.atx_state in *. destruct armed.
- destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
rewrite !R by (first [lia | unfold atx_cell; cbn; intros; lia]). repeat split; assumption.
- destruct A as (A1 & A2).
rewrite !R by (first [lia | unfold atx_cell; cbn; intros; lia]). split; assumption.
Qed.

Lemma pris_atx_idle : forall m, pris m -> UFeQ.Mq0.atx_state false m.
Proof.
intros m PR. pose proof (pris_pointwise m PR) as PW. unfold UFeQ.Mq0.atx_state.
rewrite (QBxa.Mq7.rdn_img rsegs m 0x97c4c 4 0x97c40 0x97e70); [| intros; apply PW; lia| lia| lia| lia| lia].
rewrite (QBxa.Mq7.rdn_img rsegs m 0x97c58 8 0x97c40 0x97e70); [| intros; apply PW; lia| lia| lia| lia| lia].
split; vm_compute; reflexivity.
Qed.

Section AmbX.
Context {AMB : Amb}.
Record DFX (usp0 pp tid : Z) (path : list byte) (m : mem) : Prop := MKDFX {
x_sp    : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0;
x_stk   : stk rsegs m (usp0 - 8388608) usp0;
x_frame : rw_cells rsegs m (usp0 - 120) (main_frame usp0);
x_tid   : bytes_at rsegs m 0x77b58 (le4 (Z_to_bv 64 tid)) /\ 0 < tid < 2^22;
x_self  : bytes_at rsegs m 0x77b38 (le8 (Z_to_bv 64 0x77b38));
x_pris  : prisx m;
x_stage : stk rsegs m RSTAGE (RSTAGE + RSTAGE_SZ);
x_path  : bytes_at rsegs m pp (path ++ [Z_to_bv 8 0]) /\ usp0 <= pp /\ pp + Z.of_nat (length path) + 9 <= usp0 + 4194304;
x_path8 : exists t8, bytes_at rsegs m (pp + Z.of_nat (length path)) t8 /\ length t8 = 8%nat;
x_loc   : bytes_at rsegs m 0x77bd0 (le8 (wz 0x97ec8));
x_ceil  : alloc_ceiling = usp0 - 8388608;
x_atx   : exists armed, UFeQ.Mq0.atx_state armed m    }.

#[using="Type"] Lemma DF_DFX usp0 pp tid path m : DF usp0 pp tid path m -> DFX usp0 pp tid path m.
Proof. intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11]. constructor; auto; [apply pris_prisx; exact A6 | exists false; apply pris_atx_idle; exact A6]. Qed.

#[using="Type"] Lemma DFX_munch : forall usp0 pp tid path m m' W,
DFX usp0 pp tid path m -> munch W m m' -> wmono rsegs m m' -> stk rsegs m' (usp0 - 8388608) (usp0 - 128) ->
Forall (fun iv => snd iv <= usp0 - 128 /\
(snd iv <= 0x10000 \/ 0x99000 <= fst iv
\/ (0x66d38 <= fst iv /\ snd iv <= 0x66e20) \/ (0x66e28 <= fst iv /\ snd iv <= 0x66f10)
\/ (0x76f80 <= fst iv /\ snd iv <= 0x76f81) \/ (0x98350 <= fst iv /\ snd iv <= 0x98750))
/\ fst iv <= snd iv) W ->
DFX usp0 pp tid path m'.
Proof.
intros usp0 pp tid path m m' W D MU WM ST' FW. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL ATX].
assert (OUT : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ stdio_area x)) -> outside W x).
{ intros x Hx. unfold stdio_area in Hx. clear -FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[F1 [F2 F3]] FW]. cbn [fst snd] in *.
split; [lia| apply IH; exact FW]. }
assert (EQ : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ stdio_area x)) -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT. exact Hx. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- destruct (stk_split rsegs m (usp0 - 8388608) (usp0 - 128) usp0 STK ltac:(lia)) as [_ S2].
apply (stk_merge rsegs m' (usp0 - 8388608) (usp0 - 128) usp0 ST'); [| lia].
eapply stk_transport; [exact S2| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. apply EQ; [left; lia|]. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. lia.
+ destruct WR as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. apply W3. exact Hi.
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold stdio_area; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold stdio_area; lia| lia].
- unfold prisx in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ; [right; unfold stdio_area|];
unfold PRIS2 in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- eapply stk_transport; [exact STG| exact MU| exact WM|]. intros x Hx. left. apply OUT. right. unfold RSTAGE, RSTAGE_SZ, stdio_area in *. lia.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; [left; lia| lia].
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold stdio_area; lia| lia].
- exact CEIL.
- destruct ATX as [armed AT]. exists armed. eapply atx_state_agree; [exact AT|]. intros x Hx. unfold atx_cell in Hx. apply EQ; [right; unfold stdio_area; lia| lia].
Qed.

#[using="Type"] Lemma prisx_transport : forall (m m' : mem), prisx m -> mem_inv rsegs m' ->
(forall x, 0x62000 <= x < 0x99000 -> ~ (RCTX <= x < RCTX + 928) -> ~ (RERRNO <= x < RERRNO + 4) -> m' (wa x) = m (wa x)) ->
prisx m'.
Proof.
intros m m' PRS MI' EQ. unfold prisx in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0.
destruct (Z.lt_ge_cases a 0x62000) as [LT|GE].
- apply mem_inv_text_none; [exact MI'|]. unfold PRIS2 in IN. cbn in IN.
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
- rewrite EQ; [exact E0| | |]; unfold PRIS2, RCTX, RERRNO, RATP in *; cbn in IN;
repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
Qed.

#[using="Type"] Lemma DFX_alloc usp0 pp tid path m m' LB0 SP lo :
DFX usp0 pp tid path m ->
rheap_pres LB0 SP m m' -> mem_inv rsegs m' -> stk rsegs m' lo SP ->
lo = usp0 - 8388608 -> lo <= SP <= usp0 - 120 ->
DFX usp0 pp tid path m'.
Proof.
intros [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL ATX] HP MI' ST' -> HSP.
assert (EQ : forall x, (SP <= x \/ (0x62000 <= x < 0x99000 /\ ~ (RCTX <= x < RCTX + 928) /\ ~ (RERRNO <= x < RERRNO + 4))) ->
0 <= x < 2^64 -> m' (wa x) = m (wa x)).
{ intros x Hx Hr. apply (HP x Hr). destruct Hx as [Hx|Hx]; [left; exact Hx| right; left].
unfold ralloc_static. split; [lia|]. intros [X|X]; tauto. }
constructor.
- exact SPB.
- apply (stk_merge rsegs m' _ SP); [exact ST'| | lia]. eapply rheap_pres_stk; [exact HP| | lia].
destruct (stk_split rsegs m _ SP _ STK ltac:(lia)) as [_ S2]. exact S2.
- eapply rheap_pres_rw_cells; [exact HP| exact FRM| left; lia].
- destruct TID as [T1 T2]. split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- eapply prisx_transport; [exact PRS| exact MI'|]. intros x Hx N1 N2. apply EQ; [right; tauto| lia].
- pose proof stage_bounds as (SB1 & SB2 & SB3 & SB4). eapply rheap_pres_stk_data; [exact HP| exact STG| exact SB1| exact SB2| exact SB3| exact SB4].
- destruct PTH as (P1 & P2 & P3). split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
apply EQ; [left; lia| lia].
- destruct PTH as (P1 & P2 & P3). destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2].
eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; unfold RCTX, RERRNO; lia| lia].
- exact CEIL.
- destruct ATX as [armed AT]. exists armed. eapply atx_state_agree; [exact AT|]. intros x Hx. unfold atx_cell in Hx. apply EQ; [right; unfold RCTX, RERRNO, RATP; lia| lia].
Qed.
End AmbX.

Lemma ref_ro_addr_rw : forall x : word, 0x62000 <= bv_unsigned x -> ro_addr rsegs x = false.
Proof.
intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R.
destruct (Z.lt_ge_cases (bv_unsigned x) 0x99000) as [LT|GE]; [| apply ref_ro_addr_false; lia].
unfold ro_addr. unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x20000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x42000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x62000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x66000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
set (z := bv_unsigned x) in *.
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x10000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x20000 z); destruct (Z.leb_spec0 (z + 1) (0x20000 + 0x42000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x62000 z); destruct (Z.leb_spec0 (z + 1) (0x62000 + 0x4000)); cbn [andb]; try lia.
all: try (vm_compute; reflexivity).
all: destruct (Z.leb_spec0 0x66000 z); destruct (Z.leb_spec0 (z + 1) (0x66000 + 0x33000)); cbn [andb]; try lia.
all: try (vm_compute; reflexivity).
Qed.

Lemma wmono_of_grows : forall (m m' : mem), QRjH.Mq3.mem_grows m m' -> wmono rsegs m m'.
Proof.
intros m m' G x Hx. unfold wview in *. destruct (m x) eqn:E.
- specialize (G x ltac:(rewrite E; discriminate)). destruct (m' x); [discriminate| exfalso; apply G; reflexivity].
- destruct (m' x); [discriminate| exact Hx].
Qed.

Lemma stk_grows : forall (m m' : mem) lo hi, stk rsegs m lo hi -> QRjH.Mq3.mem_grows m m' -> 0x99000 <= lo -> stk rsegs m' lo hi.
Proof.
intros m m' lo hi (S1 & S2 & S3) G Hlo. split; [exact S1|]. split; [exact S2|]. intros a Ha.
destruct (S3 a Ha) as [W (b & Hb)]. unfold mrd in Hb. rewrite ref_seg_rom_none in Hb by (unfold wa; rewrite unsigned_lit by lia; lia).
destruct (m (wa a)) eqn:E; [| discriminate].
specialize (G (wa a) ltac:(rewrite E; discriminate)). destruct (m' (wa a)) eqn:E'; [| exfalso; apply G; reflexivity].
split; [unfold wview; rewrite E'; discriminate| eexists; unfold mrd; rewrite E'; reflexivity].
Qed.

Lemma stk_img_agree : forall (m m' : mem) lo hi, stk rsegs m lo hi ->
(forall a, lo <= a < hi -> m' (wa a) = m (wa a)) -> stk rsegs m' lo hi.
Proof.
intros m m' lo hi (S1 & S2 & S3) EQ. split; [exact S1|]. split; [exact S2|]. intros a Ha.
destruct (S3 a Ha) as [W (b & Hb)]. unfold wview, mrd in *. rewrite (EQ a Ha). split; [exact W| exists b; exact Hb].
Qed.

Lemma mem_inv_of_agree : forall (m m' : mem), mem_inv rsegs m ->
(forall x : word, bv_unsigned x < 0x62000 -> m' x = m x) -> mem_inv rsegs m'.
Proof.
intros m m' MI EQ x b Hx. destruct (Z.lt_ge_cases (bv_unsigned x) 0x62000) as [LT|GE].
- rewrite EQ in Hx by exact LT. exact (MI x b Hx).
- apply ref_ro_addr_rw. exact GE.
Qed.

Lemma canonR_getr : forall R,
canonR R = QWxq.mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
(getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
(getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
(getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).
Proof. intros R. unfold canonR, getr. cbn -[reg_get]. reflexivity. Qed.

Lemma lit_add_1 : forall a : Z, (Z_to_bv 64 a + 1 : word)%bv = Z_to_bv 64 (a + 1).
Proof.
intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma store_ok_wr_at : forall segs m (a : Z) (n : nat),
(0 <= a)%Z -> (a + Z.of_nat n <= 2^64)%Z ->
store_ok segs m (Z_to_bv 64 a) n = true -> QZDE.wr_at segs m a (Z.of_nat n).
Proof.
intros segs m a n Ha Hn H. split; [exact Ha|]. split; [exact Hn|].
revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H i Hi; [lia|].
cbn [store_ok] in H. destruct (wview segs m (Z_to_bv 64 a)) eqn:W; [|discriminate].
destruct (Z.eq_dec i 0) as [->|NZ].
- unfold QZDE.wa. rewrite Z.add_0_r, W. discriminate.
- unfold QZDE.wa. replace (a + i)%Z with ((a + 1) + (i - 1))%Z by lia.
apply (IH (a + 1)%Z); [lia| lia| | lia].
rewrite <- lit_add_1. exact H.
Qed.

Lemma add_lit_Z : forall (x : word) (k : Z), (x + Z_to_bv 64 k : word)%bv = Z_to_bv 64 (bv_unsigned x + k).
Proof.
intros x k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma alu_add_lit : forall (x : word) (k : Z), alu64 ALU_ADD x (Z_to_bv 64 k) = Z_to_bv 64 (bv_unsigned x + k).
Proof. intros. unfold alu64. cbn. apply add_lit_Z. Qed.

Lemma rw_cells_img : forall (m : mem) A bs cs,
(forall i, (A <= i < A + Z.of_nat (length bs))%Z -> m (Z_to_bv 64 i) = None) ->
QBpc.rw_bytes_b rsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
QbVh.cells_wf cs -> QbVh.cells_bytes cs = bs -> QbVh.cells_size cs = length bs ->
QlEo.rw_cells rsegs m A cs.
Proof.
intros m A bs cs Hn Hb HA Hhi WF E1 E2.
apply (QBpc.rw_cells_recast rsegs m A [CB (length bs) bs] cs); [| exact WF| cbn; rewrite app_nil_r; exact E1| cbn; rewrite Nat.add_0_r; exact E2].
apply QBpc.rw_cells_image0; [| exact Hb| exact HA| exact Hhi].
intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hn. exact Ha.
Qed.

Lemma prisx_rdn : forall m lo hi a n,
prisx m -> In (lo, hi) PRIS2 -> lo <= a -> a + Z.of_nat n <= hi ->
rdn rsegs m (Z_to_bv 64 a) n = rdn rsegs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
intros m lo hi a n PR IN H1 H2.
assert (R : 0x10000 <= lo /\ hi <= 0x99000).
{ unfold PRIS2 in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN. }
apply (QBxa.Mq7.rdn_img rsegs m a n lo hi); try lia.
intros i Hi. pose proof (proj1 (Forall_forall _ _) PR _ IN i Hi) as E. cbn [fst snd] in E. unfold wa in E. exact E.
Qed.
