(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEdo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEdo.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYLF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYLF.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYLF.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0yM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0yM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFMt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFMt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QINi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QINi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QptC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QptC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QF1K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QF1K.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qz8O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qz8O.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDNp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDNp.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsl3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsl3_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Wb.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

Lemma XE0_sound : forall SEGS A nx0 LIM USP SINV argH FS0, emit_stmt SEGS A nx0 LIM USP XE0 SINV argH FS0.
Proof. intros SEGS A nx0 LIM USP SINV argH FS0 id args cs fd ps cs' E R FULL model T HC Hn. discriminate Hn. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIM USP SINV argH FS0, ext2_stmt SEGS A nx0 LIM USP XB0 SINV argH FS0.
Proof. intros SEGS A nx0 LIM USP SINV argH FS0 id args cs csa csb E R FULL model TA TB HC Hn. discriminate Hn. Qed.

Fixpoint all_holes (s : shape) : bool :=
match s with
| SHole _ => true
| SAlt2 a b => all_holes a && all_holes b
| SCase _ _ a b => all_holes a && all_holes b
| _ => false
end.

Lemma sd_all_holes : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (T : TSet) D E fs s,
all_holes s = true -> (forall h, HOLES h E fs = T) -> T [] -> t_eq (sd HOLES D E fs s) T.
Proof.
intros HOLES T D E fs s. induction s; cbn [all_holes sd]; intros Hs HH HT; try discriminate.
- apply andb_prop in Hs as [Ha Hb]. intros tr. unfold t_alt2. split.
+ intros [X|X]; [apply (IHs1 Ha HH HT) | apply (IHs2 Hb HH HT)]; exact X.
+ intros X. left. apply (IHs1 Ha HH HT). exact X.
- apply andb_prop in Hs as [Ha Hb]. destruct (_ <=? _)%Z; [exact (IHs1 Ha HH HT) | exact (IHs2 Hb HH HT)].
- rewrite HH. intros tr. tauto.
Qed.

Definition HS2s (h : nat) : option acs := match HS2sA h with Some c => Some c | None => HS2sB h end.

Section Startup.

Variable sp : word.
Variable rdraw : EntryDraw.
Variables brk0 mbase : word.
Variables argv envp : list (list byte).
Variable ifs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
#[local] Notation fs := (fs_seed_tmp ifs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk JOB6SEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.

#[local] Notation SINV := (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 JOB6PH sp rdraw argv envp uid hw).
#[local] Notation E0a := (E0 JOB6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation LIM := QVWI.Mq0.LIMIT.

#[local] Notation USP := (bv_unsigned sp).
#[local] Notation CSOK := (cs_ok JOB6SEGS BJO6 LIM USP SINV argH fs).

Lemma xsniff_disabled : forall nx0, x_stmt JOB6SEGS BJO6 nx0 LIM USP SINV argH fs XSniff.
Proof. intros nx0 args cs cs' E R FULL model T HC _ Hn Hk. discriminate Hn. Qed.

Lemma AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Proof. exact (argH0_high JOB6PH sp rdraw argv envp uid hw Hsp Hva). Qed.
Lemma ASP : forall E (a : word), argH E a = true -> USP <= bv_unsigned a.
Proof. exact (argH0_sp JOB6PH sp rdraw argv envp uid hw Hva). Qed.
Lemma USPOK : usp_ok USP.
Proof. exact (usp_ok0 sp Hsp). Qed.
Lemma NXGE : forall nx0, (NX0 <= nx0)%nat -> nx0_ge nx0.
Proof. intros nx0 Hn. unfold nx0_ge. unfold NX0 in Hn. lia. Qed.
Lemma AA : forall nx0, (NX0 <= nx0)%nat -> forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Proof. intros nx0 Hn E E' a Hag. apply argH0_agree. eapply env_agree_le; [exact Hag | exact Hn]. Qed.
Lemma SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Proof. exact (SINV0_frame JOB6PH sp rdraw brk0 argv envp uid hw). Qed.
Lemma SA : forall nx0, (NX0 <= nx0)%nat -> forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Proof. intros nx0 Hn E E' M Hag. apply SINV0_agree. eapply env_agree_le; [exact Hag | exact Hn]. Qed.

Lemma node_x_sound_all : forall nx0, (NX0 <= nx0)%nat -> forall x, x_stmt JOB6SEGS BJO6 nx0 LIM USP SINV argH fs x.
Proof.
intros nx0 Hn. pose proof AH as AH'. pose proof (AA nx0 Hn) as AA'. pose proof SF as SF'. pose proof (SA nx0 Hn) as SA'.
pose proof (NXGE nx0 Hn) as NXGE'.
intros [ | | | | | | | | | | ].
- eapply asan_node_x_sound_XIMemset; eassumption.
- eapply asan_node_x_sound_XIMemcpy; eassumption.
- eapply asan_node_x_sound_XMemset; eassumption.
- eapply asan_node_x_sound_XMemcpy; eassumption.
- eapply asan_node_x_sound_XMemIsZero; eassumption.
- eapply node_x_sound_XEnvScan_asan_gen; first [exact Hsp | exact Hva | exact Hve | exact Hfit | exact Hn | exact SF' | exact SA' | intros ? ? HH; exact HH].
- eapply node_x_sound_XPnScan_asan_gen; first [exact Hsp | exact Hva | exact Hve | exact Hfit | exact Hn | exact SF' | exact SA' | intros ? ? HH; exact HH].
- apply x_sound_layout.
- eapply asan_node_x_sound_XIStrncpy; eassumption.
- eapply asan_node_x_sound_XPopFree; eassumption.
- apply xsniff_disabled.
Qed.

Variable TM : Fs.Fs -> TSet.
Hypothesis TM_nil : forall fs', TM fs' [].
Definition HOLEST (h : nat) (E : env) (fs' : Fs.Fs) : TSet := TM fs'.

Hypothesis HMAIN : forall h ch, HS2s h = Some ch ->
forall E R FULL model, CSOK E ch R FULL model -> srealizes JOB6SEGS (cfg_of JOB6SEGS R (pc ch) FULL model) (TM (m_fs model)).

#[local] Ltac img_side :=
first [ exact asan_wx | exact asan_in_hull | exact asan_res_len | exact asan_res_hull | exact asan_hull_ok | exact asan_shadow_ok
| exact asan_hull_cov | exact USPOK | exact ASP | eassumption ].

Lemma check_sound_job6 : forall nx0, (NX0 <= nx0)%nat ->
forall IT, itab_sound JOB6SEGS IT ->
forall HS, holes_stmt JOB6SEGS BJO6 LIM USP HS SINV argH HOLEST fs ->
forall fuel bfuel p cs s,
check JOB6SEGS IT BJO6 nx0 LIM (XNjob6 JOB6SEGS nx0) XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
forall E R FULL model, CSOK E cs R FULL model ->
srealizes JOB6SEGS (cfg_of JOB6SEGS R (pc cs) FULL model) (sd HOLEST t_nil E (m_fs model) s).
Proof.
intros nx0 Hn IT IT_ok HS HSs fuel bfuel p cs s Hc E R FULL model HC.
pose proof AH as AH'. pose proof (AA nx0 Hn) as AA'. pose proof SF as SF'. pose proof (SA nx0 Hn) as SA'.
pose proof (NXGE nx0 Hn) as NXGE'. pose proof ASP as ASP'. pose proof USPOK as USPOK'.
refine (check_sound JOB6SEGS IT IT_ok BJO6 nx0 LIM USP HS (XNjob6 JOB6SEGS nx0) XE0 XB0
asan_wx asan_in_hull asan_hull_ok asan_shadow_ok NXGE' SINV argH AH' AA' SF' SA'
HOLEST _ _ _ fs KC0
_ _ _ _ _ _ _ (node_x_sound_all nx0 Hn) _ _ _ _ HSs
fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
- intros; reflexivity.
- intros; apply TM_nil.
- intros; reflexivity.
- eapply node_sys_sound; img_side.
- eapply node_brk2_sound; img_side.
- eapply node_brk2u_sound; img_side.
- eapply node_mmap2_sound; img_side.
- eapply node_mmapin_sound; img_side.
- eapply node_mprotect2_sound; img_side.
- apply node_exit_sound.
- apply node_join_sound.
- eapply xnjob6_ext_sound; img_side.
- apply XE0_sound.
- apply XB0_sound.
Qed.

Lemma NX1A_ge : (NX0 <= QINi.NX1)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
Lemma NX1B_ge : (NX0 <= QptC.NX1)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma stage2sA_holes_sound : holes_stmt JOB6SEGS BJO6 LIM USP HS2sA SINV argH HOLEST fs.
Proof.
intros h ch Hh E R FULL model HC. unfold HOLEST. refine (HMAIN h ch _ E R FULL model HC).
unfold HS2s. rewrite Hh. reflexivity.
Qed.
Lemma stage2sB_holes_sound : holes_stmt JOB6SEGS BJO6 LIM USP HS2sB SINV argH HOLEST fs.
Proof.
intros h ch Hh E R FULL model HC. unfold HOLEST. refine (HMAIN h ch _ E R FULL model HC).
unfold HS2s. rewrite Hh. destruct (HS2sA h) eqn:Ha; [|reflexivity].
exfalso. revert Hh Ha. unfold HS2sA, HS2sB. destruct h as [|[|[|[|[|h]]]]]; cbn; intros; congruence.
Qed.

Lemma stage1_holes_sound : holes_stmt JOB6SEGS BJO6 LIM USP HS1s SINV argH HOLEST fs.
Proof.
intros h ch Hh E R FULL model HC.
destruct h as [|[|[|[|[|[|[|h]]]]]]]; try discriminate Hh; cbn [HS1s] in Hh; injection Hh as <-.
- pose proof (check_sound_job6 QINi.NX1 NX1A_ge QINi.IT2 (asan_IT_ranges_ok job6_stage2_ranges) HS2sA stage2sA_holes_sound
FUEL BFUEL job6_stage2 QINi.CS1 job6_stage2sA_shape job6_stage2sA_cert E R FULL model HC) as R2.
eapply srz_conseq; [exact R2|].
unfold HOLEST. cbn [sd job6_stage2sA_shape]. destruct (_ <=? _)%Z; intros tr; tauto.
- pose proof (check_sound_job6 QptC.NX1 NX1B_ge QptC.IT2 (asan_IT_ranges_ok job6_stage2b_ranges) HS2sB stage2sB_holes_sound
FUEL BFUEL job6_stage2b QptC.CS1 job6_stage2sB_shape job6_stage2sB_cert E R FULL model HC) as R2.
eapply srz_conseq; [exact R2|].
unfold HOLEST. cbn [sd job6_stage2sB_shape]. destruct (_ <=? _)%Z; intros tr; tauto.
Qed.

Lemma job6_startup1s_all_holes : all_holes job6_startup1s_shape = true.
Proof. reflexivity. Qed.

Theorem asan_startup_job6S :
srealizes JOB6SEGS (init_config JOB6SEGS AsanUbsan.M.init_pc JOB6PH sp brk0 mbase rdraw QpvH.LIMIT
(QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp))
(TM fs).
Proof.
pose proof asan_img_facts as IMG.
rewrite (init_cfg_eq JOB6SEGS BJO6 JOB6PH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp AsanUbsan.M.init_pc eq_refl).
pose proof (init_cs_ok JOB6SEGS BJO6 JOB6PH sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net IMG Hsp Hbrk Hva Hve Hfit Huid nofile sigmask abort_terminal urnd tmp) as HC0.
pose proof (check_sound_job6 NX0 (le_n NX0) Q9O7.IT1 (asan_IT_ranges_ok job6_startup1s_ranges) HS1s stage1_holes_sound
FUEL BFUEL job6_startup1s bjo_init job6_startup1s_shape job6_startup1s_cert E0a _ _ _ HC0) as R1.
eapply srz_conseq; [exact R1|].
apply sd_all_holes; [exact job6_startup1s_all_holes | intros; reflexivity | apply TM_nil].
Qed.
End Startup.
