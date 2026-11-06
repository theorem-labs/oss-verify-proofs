(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5 QJFf Qwm6 QupI Qirj QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QvSK QvQl Qxua.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import Qsn5 QJFf.Mq1.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QvSK.Mq0 QvQl.Mq0 QvQl Qxua.Mq1.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma DRV_CHECKS : forall w ch, HSCLASS_S w ch ->
drv_pieces_check (kn_view ch) = true
/\ img_ranges (kn_view ch) (QupI.PRIS_A ++ QupI.STDIO0_A) = true
/\ img_range (kn_view ch) 0x10000 0xe4000 = true
/\ kn_mem (KRange (EVar 44) 1 4194303) (kn_view ch) = true
/\ a_fd ch = FdStd.
Proof.

intros [|] ch [-> | ->].
- split; [exact DRVPIECES_HS2sA_1_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sA_2_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sB_3_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sB_4_ok|]. repeat split; vm_compute; reflexivity.
Qed.

Lemma seg_w : seg_writable AsanUbsan.AsanUbsan_segment_002 = true
/\ seg_writable AsanUbsan.AsanUbsan_segment_003 = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma ro_addr_range : forall a : word, QZDE.ro_addr JOB6SEGS a = true -> 0x10000 <= bv_unsigned a < 0xe4000.
Proof.

intros a H. unfold QZDE.ro_addr in H. destruct seg_w as [W2 W3].
unfold JOB6SEGS, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments in H. cbn [find_segment] in H.
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x2e000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x3e000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0xa6000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xe4000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x6000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xea000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000 in H by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0x10000 + 0x2e000)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 0x3e000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0x3e000 + 0xa6000)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 0xe4000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0xe4000 + 0x6000)); cbn [andb] in H;
try (exfalso; rewrite W2 in H; discriminate H).
all: destruct (Z.leb_spec0 0xea000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0xea000 + 0x55d000)); cbn [andb] in H;
try (exfalso; rewrite W3 in H; discriminate H); try discriminate H.
Qed.

Lemma DRV_w : img_w_b JOB6SEGS (Qwm6.Mq4.A_TP - 48) 8 = true /\ img_w_b JOB6SEGS Qirj.ATEXIT_A 304 = true.
Proof. split; vm_compute; reflexivity. Qed.

Section DrvPre.
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
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).

Theorem drv_pristine : QupI.pris_A m /\ QupI.stdio0 m.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & IR & _).
pose proof (img_ranges_sound JOB6SEGS E m (kn_view ch) KV _ IR) as F. apply Forall_app in F as [F1 F2].
split; [unfold QupI.pris_A | unfold QupI.stdio0]; (eapply Forall_impl; [| eassumption]); intros iv H a Ha; exact (H a Ha).
Qed.

Theorem drv_mem_inv : QZDE.mem_inv JOB6SEGS m.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & _ & IR & _).
exact (mem_inv_of_img JOB6SEGS E m (kn_view ch) KV 0x10000 0xe4000 IR ro_addr_range).
Qed.

Theorem drv_tid : exists tid, QlEo_c1.ro_cells JOB6SEGS m (Qwm6.Mq4.A_TP - 168) [QbVh.C4 (Z_to_bv 64 tid)] /\ 0 < tid < 2^31.
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _ & _ & KR & _). unfold drv_pieces_check in C.
apply andb_prop in C as [C _]. apply andb_prop in C as [C _].
pose proof (proj1 (Forall_forall _ _) KV _ (kn_mem_In _ _ KR)) as RG. cbn [kentry_ok edenot] in RG.
exists (bv_unsigned (ev E 44)). split; [| lia].
refine (proj1 (check_cells_at JOB6SEGS E m (kn_view ch) KV DTID (ELit 0) _ [QbVh.C4 (Z_to_bv 64 (bv_unsigned (ev E 44)))] C _ _ _ _)).
- change (bv_unsigned (edenot E (ELit 0))) with 0. unfold Qwm6.Mq4.A_TP. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- cbn [sc_match DTID]. split; [| exact I]. cbn [edenot QbVh.cbytes]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. tauto.
Qed.

Theorem drv_loc : QlEo_c1.rw_cells JOB6SEGS m QupI.T_LOCCELL_A [QbVh.C8 (Z_to_bv 64 QupI.T_GLOBLOC_A)].
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _). unfold drv_pieces_check in C.
apply andb_prop in C as [C _]. apply andb_prop in C as [_ C]. destruct DRV_w as [W _].
refine (check_rw_cells JOB6SEGS E m (kn_view ch) KV DLOC (ELit 0) _ _ C _ _ _ _ _).
- change (bv_unsigned (edenot E (ELit 0))) with 0. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- cbn [sc_match DLOC]. split; [reflexivity | exact I].
- cbn. tauto.
- change (bv_unsigned (edenot E (ELit 0))) with 0. exact (img_w_b_sound JOB6SEGS 8 _ m W ltac:(unfold Qwm6.Mq4.A_TP; lia) ltac:(unfold Qwm6.Mq4.A_TP; cbn; lia)).
Qed.

Theorem drv_atexit : exists mid, QlEo_c1.rw_cells JOB6SEGS m Qirj.ATEXIT_A (Qirj.atexit_cells m mid) /\ length mid = 240%nat.
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _). unfold drv_pieces_check in C. apply andb_prop in C as [_ C]. destruct DRV_w as [_ W].
assert (PH : Qirj.ax_phase m = 1).
{ unfold Qirj.ax_phase. destruct drv_pristine as [_ S0]. unfold QupI.stdio0, QupI.STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (Qirj.ADFLAG_A, Qirj.ADFLAG_A + 48) ltac:(unfold Qirj.ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
replace (m (Z_to_bv 64 Qirj.ADFLAG_A)) with (@None (bv 8)) by (symmetry; exact (PAD Qirj.ADFLAG_A ltac:(unfold Qirj.ADFLAG_A; lia))). reflexivity. }
exists (rom_bytes JOB6SEGS (Qirj.ATEXIT_A + 48) 240). split; [| apply rom_bytes_length].
unfold Qirj.atexit_cells. rewrite PH.
refine (check_rw_cells JOB6SEGS E m (kn_view ch) KV DATEXIT (ELit 0) _ _ C _ _ _ _ _).
- change (bv_unsigned (edenot E (ELit 0))) with 0. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn [sc_match DATEXIT Qirj.atexit_cellsK].
repeat split; vm_compute; reflexivity.
- unfold Qirj.atexit_cellsK. cbn [QbVh.cells_wf QbVh.cell_wf]. rewrite rom_bytes_length. repeat split; reflexivity.
- change (bv_unsigned (edenot E (ELit 0))) with 0. exact (img_w_b_sound JOB6SEGS 304 _ m W ltac:(unfold Qirj.ATEXIT_A; lia) ltac:(unfold Qirj.ATEXIT_A; cbn; lia)).
Qed.

Theorem drv_fds : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))
/\ alloc_fd (m_fds mo) = Z_to_bv 64 3 /\ fd_lookup (m_fds mo) (Z_to_bv 64 3) = None.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & _ & _ & _ & FD). pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ _ CS) as F.
unfold fds_ok in F. rewrite FD in F. rewrite F. repeat split; vm_compute; reflexivity.
Qed.
End DrvPre.
End Mq0.
From stdpp Require gmap.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QUZl QnDM_c1 QGeV Q8zf QEoy Q9O6 QnPO QW7x QCwx QkLq QCoy QLPb QY73 Q72M QDRB Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D Qn7S Qb5q Q8BV QbBz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QCoy QLPb QY73 Q72M QDRB.
Import Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D QvSK.Mq0 QvQl Qn7S Qxua.Mq0 Qb5q.Mq0 Q8BV.Mq0.
Import QbBz.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma conc_A0 : forall sec resv b g off, QUZl.conc (Q8zf.ST0_A sec resv b g) (0%N, off) = b + off.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma conc_A1 : forall sec resv b g off, QUZl.conc (Q8zf.ST0_A sec resv b g) (1%N, off) = g + off.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma actives_A : forall sec resv b g, QnDM_c1.Mq0.actives (Q8zf.ST0_A sec resv b g) = map (QnDM_c1.Mq0.pw (Q8zf.ST0_A sec resv b g)) ACT_O.
Proof.
intros. unfold QnDM_c1.Mq0.actives. rewrite <- (map_map (fun i => QUZl.active (Q8zf.ST0_A sec resv b g) (Z.of_nat i)) (QnDM_c1.Mq0.pw (Q8zf.ST0_A sec resv b g))).
f_equal; try (vm_compute; reflexivity).
Qed.
Lemma usages_A : forall sec resv b g, QnDM_c1.Mq0.usages (Q8zf.ST0_A sec resv b g) = USE_Aw.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma brk_word_A : forall sec resv b g, QnDM_c1.Mq0.brk_word (Q8zf.ST0_A sec resv b g) = b + 8192.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma areas_A_inv : forall sec resv b g a ar, QUZl.s_areas (Q8zf.ST0_A sec resv b g) !! a = Some ar -> a = (0%N, 4096) /\ ar = QUZl.mkArea sec None 101.
Proof. intros sec resv b g a ar H. apply l2m_some in H. destruct H as [[= <- <-]|[]]. split; reflexivity. Qed.
Lemma groups_A_inv : forall sec resv b g p gh, QUZl.s_groups (Q8zf.ST0_A sec resv b g) !! p = Some gh ->
(p = (1%N, 0) /\ gh = QUZl.mkGhdr (Some (0%N, 4240)) 1) \/ (p = (1%N, 48) /\ gh = QUZl.mkGhdr (Some (0%N, 4120)) 9)
\/ (p = (1%N, 32) /\ gh = QUZl.mkGhdr (Some (0%N, 4160)) 1) \/ (p = (1%N, 16) /\ gh = QUZl.mkGhdr (Some (0%N, 4200)) 1).
Proof. intros sec resv b g p gh H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; tauto. Qed.
Lemma regions_A_inv : forall sec resv b g rid r, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! rid = Some r ->
(rid = 1%N /\ r = QUZl.mkRegion QUZl.RKGroup g 4096) \/ (rid = 0%N /\ r = QUZl.mkRegion QUZl.RKBrk b 8192).
Proof. intros sec resv b g rid r H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[]]]; tauto. Qed.
Lemma region_A0 : forall sec resv b g, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! 0%N = Some (QUZl.mkRegion QUZl.RKBrk b 8192).
Proof. intros. vm_compute. reflexivity. Qed.
Lemma region_A1 : forall sec resv b g, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! 1%N = Some (QUZl.mkRegion QUZl.RKGroup g 4096).
Proof. intros. vm_compute. reflexivity. Qed.

Lemma meta_A_0 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4120) = QUZl.mkMeta (Some (0%N, 4120)) (Some (0%N, 4120)) (Some (1%N, 48)) 1022 0 9 1 2 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_1 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4160) = QUZl.mkMeta (Some (0%N, 4160)) (Some (0%N, 4160)) (Some (1%N, 32)) 2 0 1 1 15 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_2 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4200) = QUZl.mkMeta (Some (0%N, 4200)) (Some (0%N, 4200)) (Some (1%N, 16)) 2 0 1 1 19 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_3 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4240) = QUZl.mkMeta (Some (0%N, 4240)) (Some (0%N, 4240)) (Some (1%N, 0)) 2 0 1 1 23 1.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_none : forall sec resv b g k, 4 <= k -> QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4120 + 40 * k) = QUZl.meta0.
Proof.
intros sec resv b g k Hk. unfold QUZl.get_meta_rec. replace (QUZl.s_metas (Q8zf.ST0_A sec resv b g) !! (0%N, 4120 + 40 * k)) with (@None QUZl.meta); [reflexivity|].
symmetry. apply l2m_none. cbn [map fst]. intros [X|[X|[X|[X|[]]]]]; injection X; lia.
Qed.

Definition SH_A : QUZl.shadow := QUZl.get_shadow (Q8zf.ST0_A 0 [] 0 0) 1%N.
Lemma shadow_A1 : forall sec resv b g, QUZl.get_shadow (Q8zf.ST0_A sec resv b g) 1%N = SH_A.
Proof. intros. reflexivity. Qed.

Lemma SHADOW_A_ok : mng_shadow_ok SH_A GRP_A 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shadow_A_lit : forall o v, 0 <= o < 4096 -> QUZl.cell_read SH_A o = QUZl.Known v -> sc_lit_byte GRP_A (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof. intros o v Ho Hc. exact (mng_shadow_ok_sound SH_A GRP_A 4096 o v SHADOW_A_ok Ho Hc). Qed.

Lemma groups_of_A : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr)))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKGroup => true | _ => false end) (map_to_list (QUZl.s_regions (Q8zf.ST0_A sec resv b g))))
= [(g, 4096)].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma metas_of_A : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr), Qatc.frontier (Q8zf.ST0_A sec resv b g) (fst kr) (snd kr) / QUZl.PGSZ - 1))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKMeta => true | _ => false end) (map_to_list (QUZl.s_regions (Q8zf.ST0_A sec resv b g))))
= [].
Proof. intros. vm_compute. reflexivity. Qed.

Section RmrepA.
Context {RC__ : Q6q3.RunConsts}.
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
Variable ch : acs.
Hypothesis HCL : HSCLASS_S true ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.

Hypothesis HSEC : Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8).
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
#[local] Notation LV := (LV_J E).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo true ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation MTA := (4096 * bv_unsigned (ev E 5)).
#[local] Notation GRP := (4096 * bv_unsigned (ev E 423)).
#[local] Notation ST0 := (Q8zf.ST0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP).

Lemma mta_bounds : 4096 <= MTA /\ MTA + 8192 <= 2^47.
Proof. pose proof (MV4 pge_meta) as (_ & B1 & B2). unfold METAB, MV, MV_A in B1, B2. lia. Qed.
Lemma grp_bounds : 4096 <= GRP /\ GRP + 4096 <= 2^47.
Proof. pose proof (MV4 pge_grp) as (_ & B1 & B2). unfold GRPBx, GV, GV_A in B1, B2. lia. Qed.

Lemma ed_mta : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit k)) = Z_to_bv 64 (MTA + k).
Proof.
intros k Hk. destruct mta_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit k)) = Z_to_bv 64 (GRP + k).
Proof.
intros k Hk. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp0 : edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423)) = Z_to_bv 64 (GRP + 0).
Proof. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_mul64, !u64_lit by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma lit_rw : forall A cs tcs n, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JO6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 -> sc_match JO6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m A tcs.
Proof.
intros A cs tcs n C W L H0 H1 M WF.
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X.
apply X; [exact H0 | exact H1 | exact M | exact WF | exact (img_w_b_sound JO6SEGS n A m W H0 H1)].
Qed.

Ltac piece P := lazymatch goal with H : cells_check _ _ _ _ P = true |- _ => exact H end.
Theorem rmrep_globals_A : QCwx.Mq1.rmrep_globals m.
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct STATICS_w as (W1 & W2 & W3 & W4 & W5 & W6 & _).
unfold QCwx.Mq1.rmrep_globals. split; [|split; [|split; [|split; [|split]]]].
- refine (lit_rw QW7x.Mq0.RMLOCK PLOCK_A _ 4%nat PC W1 eq_refl ltac:(unfold QW7x.Mq0.RMLOCK; lia) ltac:(unfold QW7x.Mq0.RMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PLOCK_A]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RNEED_LOCKS PNL_A _ 1%nat ltac:(piece PNL_A) W2 eq_refl ltac:(unfold QW7x.Mq0.RNEED_LOCKS; lia) ltac:(unfold QW7x.Mq0.RNEED_LOCKS; lia) _ _); [|cbn; tauto].
cbn [sc_match PNL_A]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RPAGE_SIZE PPGSZ_A _ 8%nat ltac:(piece PPGSZ_A) W3 eq_refl ltac:(unfold QW7x.Mq0.RPAGE_SIZE; lia) ltac:(unfold QW7x.Mq0.RPAGE_SIZE; lia) _ _); [|cbn; tauto].
cbn [sc_match PPGSZ_A]. split; [reflexivity | exact I].
- refine (lit_rw QW7x.Mq0.RGOT_SSP PGOTSSP_A _ 8%nat ltac:(piece PGOTSSP_A) W4 eq_refl ltac:(unfold QW7x.Mq0.RGOT_SSP; lia) ltac:(unfold QW7x.Mq0.RGOT_SSP; lia) _ _); [|cbn; tauto].
cbn [sc_match PGOTSSP_A]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RSSP_GUARD PSSPG_A _ 8%nat ltac:(piece PSSPG_A) W5 eq_refl ltac:(unfold QW7x.Mq0.RSSP_GUARD; lia) ltac:(unfold QW7x.Mq0.RSSP_GUARD; lia) _ _); [|cbn; tauto].
cbn [sc_match PSSPG_A]. split; [rewrite HCAN; reflexivity | exact I].
- refine (lit_rw QW7x.Mq0.RVMLOCK PVML_A _ 4%nat ltac:(piece PVML_A) W6 eq_refl ltac:(unfold QW7x.Mq0.RVMLOCK; lia) ltac:(unfold QW7x.Mq0.RVMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PVML_A]. split; [bytes_vm | exact I].
Qed.

Lemma lit_rw' : forall A cs tcs, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> QlEo_c1.rw_cells JO6SEGS m A tcs.
Proof.
intros A cs tcs C H0 H1 M WF W.
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u64 : forall A cs ws, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs (map QbVh.C8 ws) ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u64arr JO6SEGS m A ws.
Proof.
intros A cs ws C H0 H1 M W.
pose proof (check_u64arr JO6SEGS E m (kn_view ch) KV cs (ELit 0) A ws C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u8 : forall A cs bs, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs [QbVh.CB (length bs) bs] ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u8arr JO6SEGS m A bs.
Proof.
intros A cs bs C H0 H1 M W.
pose proof (check_u8arr JO6SEGS E m (kn_view ch) KV cs (ELit 0) A bs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.

Lemma ctx_wr : forall k l, 0 <= k -> 0 <= l -> k + l <= 928 -> QZDE.wr_at JO6SEGS m (QW7x.Mq0.RCTX + k) l.
Proof.
intros k l Hk Hl Hkl. destruct STATICS_w as (_ & _ & _ & _ & _ & _ & W).
exact (wr_at_sub JO6SEGS m QW7x.Mq0.RCTX 928 k l (img_w_b_sound JO6SEGS 928 QW7x.Mq0.RCTX m W ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; lia)) Hk Hl Hkl).
Qed.

Lemma ctx_A : QUZl.ctx ST0 = Q8zf.ST0_A_ctx Q6q3.rc_secret.  Proof. reflexivity. Qed.
Ltac cellA :=
rewrite ?ctx_A, ?brk_word_A; cbn [Q8zf.ST0_A_ctx QUZl.c_secret QUZl.c_free_meta_head QUZl.c_avail_meta QUZl.c_meta_area_head QUZl.c_meta_area_tail QUZl.c_avail_meta_areas];
lazymatch goal with
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 5)) _)) = _ =>
rewrite ed_mta by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A0; reflexivity
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 423)) _)) = _ =>
rewrite ed_grp by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EMd _ _ (EVar 423))) = _ =>
rewrite ed_grp0; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EBlob _ _ _ _)) = _ => rewrite <- HSEC; reflexivity
| |- True => exact I
| |- _ = QbVh.cbytes (QbVh.C8 (QnDM_c1.Mq0.pw _ None)) => unfold QnDM_c1.Mq0.pw, QUZl.oconc; bytes_vm
| _ => bytes_vm
end.

Theorem rmrep_ctx_A : QCwx.Mq1.rmrep_ctx ST0 m.
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq1.rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- refine (lit_rw' QW7x.Mq0.RCTX PHEAD_A _ ltac:(piece PHEAD_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_head_cells. cbv zeta. cbn [sc_match PHEAD_A]. repeat split; cellA.
+ cbn. tauto.
+ replace QW7x.Mq0.RCTX with (QW7x.Mq0.RCTX + 0) by lia. apply ctx_wr; cbn; lia.
- refine (lit_u64 (QW7x.Mq0.RCTX + 80) PACT_A _ ltac:(piece PACT_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ rewrite actives_A. unfold ACT_O. cbn [sc_match PACT_A map]. repeat split; cellA.
+ apply ctx_wr; cbn; lia.
- refine (lit_u64 (QW7x.Mq0.RCTX + 464) PUSE_A _ ltac:(piece PUSE_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ rewrite usages_A. unfold USE_Aw. cbn [sc_match PUSE_A map]. repeat split; cellA.
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QW7x.Mq0.RCTX + 848) PUNM_A _ ltac:(piece PUNM_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ cbn [sc_match PUNM_A]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QW7x.Mq0.RCTX + 880) PBNC_A _ ltac:(piece PBNC_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ cbn [sc_match PBNC_A]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_rw' (QW7x.Mq0.RCTX + 912) PTAIL_A _ ltac:(piece PTAIL_A) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_tail_cells. cbn [sc_match PTAIL_A]. repeat split; cellA.
+ cbn. tauto.
+ apply ctx_wr; cbn; lia.
- reflexivity.
Qed.

Lemma u_pgM : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 5))) = MTA.
Proof. exact (proj1 (MV4 pge_meta)). Qed.
Lemma u_pgG : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423))) = GRP.
Proof. exact (proj1 (MV4 pge_grp)). Qed.
Lemma meta_wr : QZDE.wr_at JO6SEGS m (MTA + 4096) 4096.
Proof. exact (proj2 (MV4 meta_bytes)). Qed.
Lemma grp_wr : QZDE.wr_at JO6SEGS m GRP 4096.
Proof. exact (proj2 (MV4 grp_bytes)). Qed.

Lemma mta_piece_rw : forall off cs tcs, cells_check JO6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) off cs = true ->
4096 <= off -> off + Z.of_nat (scs_len cs) <= 8192 -> sc_match JO6SEGS E (MTA + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m (MTA + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct mta_bounds as [B1 B2].
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgM in X.
apply X; [lia | lia | exact M | exact WF |].
replace (MTA + off) with ((MTA + 4096) + (off - 4096)) by lia. apply (wr_at_sub JO6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.
Lemma grp_piece_rw : forall off cs tcs, cells_check JO6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) off cs = true ->
0 <= off -> off + Z.of_nat (scs_len cs) <= 4096 -> sc_match JO6SEGS E (GRP + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m (GRP + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct grp_bounds as [B1 B2].
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgG in X.
apply X; [lia | lia | exact M | exact WF |].
apply (wr_at_sub JO6SEGS m GRP 4096); [exact grp_wr | lia | lia | lia].
Qed.

Lemma meta_zero_run : QZDE.bytes_at JO6SEGS m (MTA + 4280) (repeat (Z_to_bv 8 0) 3912) /\ QZDE.wr_at JO6SEGS m (MTA + 4280) (Z.of_nat 3912).
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct mta_bounds as [B1 B2]. split.
- pose proof (cells_check_sound JO6SEGS E m (kn_view ch) KV PMZERO_A _ 4280 ltac:(piece PMZERO_A)) as X. cbv zeta in X. rewrite u_pgM in X.
specialize (X ltac:(lia) ltac:(cbn; lia)). cbn [sc_bytes PMZERO_A] in X. rewrite app_nil_r in X. exact X.
- replace (MTA + 4280) with ((MTA + 4096) + 184) by lia. apply (wr_at_sub JO6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.

Theorem rmrep_areas_A : QCwx.Mq1.rmrep_areas ST0 m.
Proof.
intros a ar Ha. apply areas_A_inv in Ha as [-> ->].
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct meta_zero_run as [ZB ZW].
unfold QCwx.Mq1.rarea_rep. rewrite conc_A0. cbn [QUZl.a_check QUZl.a_next QUZl.a_nslots]. split; [|split].
- refine (mta_piece_rw 4096 PMHDR_A _ ltac:(piece PMHDR_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PMHDR_A]. repeat split; cellA.
- intros k Hk. unfold QUZl.NSLOTS in Hk. unfold QUZl.aadd, QUZl.AREA_HDR, QUZl.META_SIZE. cbn [fst snd].
assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ 4 <= k) by lia. destruct K as [->|[->|[->|[->|K]]]].
+ change (4096 + (24 + 40 * 0)) with 4120. rewrite meta_A_0. replace (MTA + 4096 + 24 + 40 * 0) with (MTA + 4120) by lia.
refine (mta_piece_rw 4120 PM0_A _ ltac:(piece PM0_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM0_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 1)) with 4160. rewrite meta_A_1. replace (MTA + 4096 + 24 + 40 * 1) with (MTA + 4160) by lia.
refine (mta_piece_rw 4160 PM1_A _ ltac:(piece PM1_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM1_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 2)) with 4200. rewrite meta_A_2. replace (MTA + 4096 + 24 + 40 * 2) with (MTA + 4200) by lia.
refine (mta_piece_rw 4200 PM2_A _ ltac:(piece PM2_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM2_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 3)) with 4240. rewrite meta_A_3. replace (MTA + 4096 + 24 + 40 * 3) with (MTA + 4240) by lia.
refine (mta_piece_rw 4240 PM3_A _ ltac:(piece PM3_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM3_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ replace (4096 + (24 + 40 * k)) with (4120 + 40 * k) by lia. rewrite (meta_A_none _ _ _ _ k K).
replace (MTA + 4096 + 24 + 40 * k) with (MTA + 4280 + Z.of_nat (Z.to_nat (40 * (k - 4)))) by lia.
apply (zero_cells JO6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; tauto | rewrite meta0_bytes; reflexivity | cbn [QbVh.cells_size QnDM_c1.Mq0.meta_cells QbVh.csize]; lia].
- replace (MTA + 4096 + 4064) with (MTA + 4280 + Z.of_nat 3880) by lia.
apply (zero_cells JO6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; split; [reflexivity | exact I] | bytes_vm | cbn; lia].
Qed.

Theorem rmrep_groups_A : QCwx.Mq1.rmrep_groups ST0 m.
Proof.
intros p gh Hp. apply groups_A_inv in Hp.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq1.rgroup_rep. destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite conc_A1; cbn [QUZl.g_meta QUZl.g_active_idx].
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 0 PG0_A _ ltac:(piece PG0_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG0_A]. repeat split; cellA.
- exists (Z_to_bv 8 9). split; [|reflexivity].
refine (grp_piece_rw 48 PG3_A _ ltac:(piece PG3_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG3_A]. repeat split; cellA.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 32 PG2_A _ ltac:(piece PG2_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG2_A]. repeat split; cellA.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 16 PG1_A _ ltac:(piece PG1_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG1_A]. repeat split; cellA.
Qed.

Theorem rmrep_shadow_A : QCwx.Mq1.rmrep_shadow ST0 m.
Proof.
intros rid r Hr Hk. apply regions_A_inv in Hr as [[-> ->]|[-> ->]]; [|discriminate Hk].
unfold QCwx.Mq1.rshadow_rep. cbn [QUZl.r_base QUZl.r_len]. change (QUZl.round_up_pg 4096) with 4096. split; [exact grp_wr|].
intros o v Ho Hc. rewrite shadow_A1 in Hc.
destruct (shadow_A_lit o v Ho Hc) as [SL V]. split; [|exact V].
pose proof (sc_lit_byte_sound JO6SEGS E GRP_A GRP (Z.to_nat o) v SL) as NTH.
pose proof (bytes_at_nth JO6SEGS m GRP _ (Z.to_nat o) _ (proj1 (MV4 grp_bytes)) NTH) as B.
rewrite Z2Nat.id in B by lia. exact B.
Qed.

#[local] Notation M1 L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo true ch HCL CS) (only parsing).
Lemma obj_facts : forall o, In o (OBJS_W true) ->
(4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x10000 \/ 0x645000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ 4096 * bv_unsigned (ev E (fst o)) + snd o <= atopE E.
Proof.
intros o Ho. pose proof (M1 in_maps_obj o Ho) as Hin. pose proof (M1 u_obj_base o Ho) as UB. pose proof (M1 u_obj_len o Ho) as UL.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ CS) as B. rewrite Forall_forall in B. destruct (B _ Hin) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi AJO6] in B4. rewrite UB, UL in B4.
pose proof (M1 maps_below_atop _ Hin) as T. rewrite UB, UL, <- (M1 main_atop) in T. split; [exact B4 | exact T].
Qed.
Lemma mta_facts : (MTA + 8192 <= 0x10000 \/ 0x645000 <= MTA) /\ MTA + 8192 <= atopE E.
Proof. exact (obj_facts (5%nat, 8192) ltac:(cbn; tauto)). Qed.
Lemma grp_facts : (GRP + 4096 <= 0x10000 \/ 0x645000 <= GRP) /\ GRP + 4096 <= atopE E.
Proof. exact (obj_facts (423%nat, 4096) ltac:(cbn; tauto)). Qed.
Lemma mta_grp_disj : GRP + 4096 <= MTA \/ MTA + 8192 <= GRP.
Proof.
assert (IM : In (5%nat, 8192) (OBJS_W true)) by (cbn; tauto). assert (IG : In (423%nat, 4096) (OBJS_W true)) by (cbn; tauto).
assert (NE : obj_e E (423%nat, 4096) <> obj_e E (5%nat, 8192)).
{ intros X. apply (M1 obj_e_inj _ _ IG IM) in X. discriminate X. }
pose proof (M1 maps_disj _ _ (M1 in_maps_obj _ IG) (M1 in_maps_obj _ IM) NE) as D. unfold iv_disjoint in D.
rewrite !(M1 u_obj_base _ IM), !(M1 u_obj_base _ IG), !(M1 u_obj_len _ IM), !(M1 u_obj_len _ IG) in D. cbn [fst snd] in D. exact D.
Qed.

Theorem rregions_wf_A : QCwx.Mq1.rregions_wf ST0.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold QCwx.Mq1.rregions_wf. split; [reflexivity|]. split; [|split; [|split]].
- intros rid r Hr. apply regions_A_inv in Hr as [[-> ->]|[-> ->]]; cbn [QUZl.r_base QUZl.r_len];
[change (QUZl.round_up_pg 4096) with 4096 | change (QUZl.round_up_pg 8192) with 8192]; unfold Q6q3.alloc_ceiling; rewrite HCEIL;
(split; [lia|]; split; [assumption|]; split; [lia|]; split; [lia|]; apply hull_apart_free; assumption).
- intros rid1 r1 rid2 r2 H1 H2 NE. apply regions_A_inv in H1 as [[-> ->]|[-> ->]]; apply regions_A_inv in H2 as [[-> ->]|[-> ->]]; try congruence;
unfold QnDM_c1.Mq0.lr_lo; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]; change (QUZl.round_up_pg 4096) with 4096; change (QUZl.round_up_pg 8192) with 8192; lia.
- intros a ar Ha. apply areas_A_inv in Ha as [-> ->]. exists (QUZl.mkRegion QUZl.RKBrk MTA 8192). cbn [fst snd]. rewrite region_A0.
unfold QnDM_c1.Mq0.lr_lo. cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]. change (QUZl.round_up_pg 8192) with 8192.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [discriminate | lia].
- intros p gh Hp. apply groups_A_inv in Hp. exists (QUZl.mkRegion QUZl.RKGroup GRP 4096).
destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [fst snd]; rewrite region_A1; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind];
change (QUZl.round_up_pg 4096) with 4096; (split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [lia | reflexivity]).
Qed.

Theorem rmrep_main_A : QCwx.Mq1.rmrep ST0 m.
Proof. exact (conj rregions_wf_A (conj rmrep_ctx_A (conj rmrep_globals_A (conj rmrep_areas_A (conj rmrep_groups_A rmrep_shadow_A))))). Qed.

Lemma answers_A : QUZl.brk0_answer_ok MTA = true /\ QUZl.brk_pages_ok (QUZl.minit Q6q3.rc_secret QW7x.Mq0.ref_reserved) MTA (2 * QUZl.PGSZ) = true
/\ QUZl.mmap_fixed_answer_ok MTA MTA = true /\ QUZl.mmap_answer_ok (QW7x.Mq0.ref_reserved ++ [(MTA + 4096, 4096)]) 4096 GRP = true /\ QUZl.is_err GRP = false.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
split; [|split; [|split; [|split]]].
- unfold QUZl.brk0_answer_ok, QUZl.PGSZ, QUZl.TWO64. rewrite AM. apply andb_true_intro. split; [apply andb_true_intro; split|]; [apply Z.ltb_lt; lia | reflexivity | apply Z.ltb_lt; lia].
- unfold QUZl.brk_pages_ok, QUZl.live_ranges, QUZl.PGSZ. cbn [QUZl.s_reserved QUZl.s_regions QUZl.minit]. rewrite map_to_list_empty. cbn [map]. rewrite app_nil_r.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. apply andb_true_intro. split; [apply andb_true_intro; split|]; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply hull_apart_free; exact BH].
- unfold QUZl.mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg 4096) with 4096. rewrite AG. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. unfold QUZl.ranges_free. rewrite forallb_app. fold (QUZl.ranges_free QW7x.Mq0.ref_reserved GRP 4096). rewrite (hull_apart_free _ _ GH).
cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply orb_true_iff; destruct D; [left | right]; apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem RHEAP_main_A : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 -> QGeV.ps_brk s = MTA + 8192 ->
QkLq.Mq2.RHEAP s [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP] m.
Proof.
intros s Hm Hb. destruct answers_A as (A1 & A2 & A3 & A4 & A5).
exists ST0, [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact rmrep_main_A|]. split.
- rewrite Hb. apply Q9O6.Mq3.brk_link_main_A.
- exact (Q9O6.Mq3.areach_main_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5).
Qed.

Theorem mng_main_A : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 -> QGeV.ps_brk s = MTA + 8192 ->
exists Lg0 : Qfya.mled,
QkLq.Mq2.RHEAP s [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP] m
/\ Q9kF.HSIM s Lg0 [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP]
/\ Qfya.ld_live Lg0 = [(1%N, 64)] /\ Qfya.ld_resv Lg0 = QW7x.Mq0.ref_reserved /\ Qfya.ld_groups Lg0 = [(GRP, 4096)]
/\ Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTA, 8192).
Proof.
intros s Hm Hb. destruct answers_A as (A1 & A2 & A3 & A4 & A5).
pose proof (Q9O6.Mq3.areach_main_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5) as AR.
destruct (Q3o5.Mq1.areach_inv QW7x.Mq0.ref_reserved ST0 _ AR) as (L & LS & BL & INV & LIVE & RESV & _ & CR).
pose proof INV as IR. unfold Qatc.INVL in IR. cbv zeta in IR. destruct IR as [IR _].
exists L. split; [exact (RHEAP_main_A s Hm Hb)|]. split.
- exists ST0, BL, LS, [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact INV | exact CR].
- split; [rewrite LIVE, <- (Q9kF.CORR_slots _ _ _ CR); reflexivity|]. split; [exact RESV|]. split; [|split].
+ pose proof (Qatc.ir_groups _ _ _ IR) as PG. rewrite groups_of_A in PG. apply Permutation.Permutation_sym in PG.
exact (Permutation.Permutation_length_1_inv PG).
+ pose proof (Qatc.ir_metas _ _ _ IR) as PM. rewrite metas_of_A in PM. apply Permutation.Permutation_sym in PM.
exact (Permutation.Permutation_nil PM).
+ apply (Qatc.ir_brkreg _ _ _ IR). exists 0%N, (QUZl.mkRegion QUZl.RKBrk MTA 8192). rewrite region_A0. repeat split.
Qed.
End RmrepA.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.

Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QCoy QLPb QY73 Q72M QDRB.
Import Qo4M QrQA QLJz QFop Q5o6 Q0Cb Q92D QvSK.Mq0 QvQl Qn7S Qxua.Mq0 Qb5q.Mq0 Q8BV.Mq0.
Import QbBz.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma conc_B0 : forall sec resv b g off, QUZl.conc (QEoy.ST0_B sec resv b g) (0%N, off) = b + off.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma conc_B1 : forall sec resv b g off, QUZl.conc (QEoy.ST0_B sec resv b g) (1%N, off) = g + off.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma actives_B : forall sec resv b g, QnDM_c1.Mq0.actives (QEoy.ST0_B sec resv b g) = map (QnDM_c1.Mq0.pw (QEoy.ST0_B sec resv b g)) ACT_O.
Proof.
intros. unfold QnDM_c1.Mq0.actives. rewrite <- (map_map (fun i => QUZl.active (QEoy.ST0_B sec resv b g) (Z.of_nat i)) (QnDM_c1.Mq0.pw (QEoy.ST0_B sec resv b g))).
f_equal; try (vm_compute; reflexivity).
Qed.
Lemma usages_B : forall sec resv b g, QnDM_c1.Mq0.usages (QEoy.ST0_B sec resv b g) = USE_Aw.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma brk_word_B : forall sec resv b g, QnDM_c1.Mq0.brk_word (QEoy.ST0_B sec resv b g) = 2^64 - 1.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma areas_B_inv : forall sec resv b g a ar, QUZl.s_areas (QEoy.ST0_B sec resv b g) !! a = Some ar -> a = (0%N, 4096) /\ ar = QUZl.mkArea sec None 101.
Proof. intros sec resv b g a ar H. apply l2m_some in H. destruct H as [[= <- <-]|[]]. split; reflexivity. Qed.
Lemma groups_B_inv : forall sec resv b g p gh, QUZl.s_groups (QEoy.ST0_B sec resv b g) !! p = Some gh ->
(p = (1%N, 0) /\ gh = QUZl.mkGhdr (Some (0%N, 4240)) 1) \/ (p = (1%N, 48) /\ gh = QUZl.mkGhdr (Some (0%N, 4120)) 9)
\/ (p = (1%N, 32) /\ gh = QUZl.mkGhdr (Some (0%N, 4160)) 1) \/ (p = (1%N, 16) /\ gh = QUZl.mkGhdr (Some (0%N, 4200)) 1).
Proof. intros sec resv b g p gh H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; tauto. Qed.
Lemma regions_B_inv : forall sec resv b g rid r, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! rid = Some r ->
(rid = 1%N /\ r = QUZl.mkRegion QUZl.RKGroup g 4096) \/ (rid = 0%N /\ r = QUZl.mkRegion QUZl.RKMeta b 8192).
Proof. intros sec resv b g rid r H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[]]]; tauto. Qed.
Lemma region_B0 : forall sec resv b g, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! 0%N = Some (QUZl.mkRegion QUZl.RKMeta b 8192).
Proof. intros. vm_compute. reflexivity. Qed.
Lemma region_B1 : forall sec resv b g, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! 1%N = Some (QUZl.mkRegion QUZl.RKGroup g 4096).
Proof. intros. vm_compute. reflexivity. Qed.

Lemma meta_B_0 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4120) = QUZl.mkMeta (Some (0%N, 4120)) (Some (0%N, 4120)) (Some (1%N, 48)) 1022 0 9 1 2 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_1 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4160) = QUZl.mkMeta (Some (0%N, 4160)) (Some (0%N, 4160)) (Some (1%N, 32)) 2 0 1 1 15 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_2 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4200) = QUZl.mkMeta (Some (0%N, 4200)) (Some (0%N, 4200)) (Some (1%N, 16)) 2 0 1 1 19 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_3 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4240) = QUZl.mkMeta (Some (0%N, 4240)) (Some (0%N, 4240)) (Some (1%N, 0)) 2 0 1 1 23 1.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_none : forall sec resv b g k, 4 <= k -> QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4120 + 40 * k) = QUZl.meta0.
Proof.
intros sec resv b g k Hk. unfold QUZl.get_meta_rec. replace (QUZl.s_metas (QEoy.ST0_B sec resv b g) !! (0%N, 4120 + 40 * k)) with (@None QUZl.meta); [reflexivity|].
symmetry. apply l2m_none. cbn [map fst]. intros [X|[X|[X|[X|[]]]]]; injection X; lia.
Qed.

Definition SH_B : QUZl.shadow := QUZl.get_shadow (QEoy.ST0_B 0 [] 0 0) 1%N.
Lemma shadow_B1 : forall sec resv b g, QUZl.get_shadow (QEoy.ST0_B sec resv b g) 1%N = SH_B.
Proof. intros. reflexivity. Qed.

Lemma SHADOW_B_ok : mng_shadow_ok SH_B GRP_B 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shadow_B_lit : forall o v, 0 <= o < 4096 -> QUZl.cell_read SH_B o = QUZl.Known v -> sc_lit_byte GRP_B (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof. intros o v Ho Hc. exact (mng_shadow_ok_sound SH_B GRP_B 4096 o v SHADOW_B_ok Ho Hc). Qed.

Lemma groups_of_B : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr)))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKGroup => true | _ => false end) (map_to_list (QUZl.s_regions (QEoy.ST0_B sec resv b g))))
= [(g, 4096)].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma metas_of_B : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr), Qatc.frontier (QEoy.ST0_B sec resv b g) (fst kr) (snd kr) / QUZl.PGSZ - 1))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKMeta => true | _ => false end) (map_to_list (QUZl.s_regions (QEoy.ST0_B sec resv b g))))
= [(b, 8192, 1)].
Proof. intros. vm_compute. reflexivity. Qed.

Section RmrepB.
Context {RC__ : Q6q3.RunConsts}.
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
Variable ch : acs.
Hypothesis HCL : HSCLASS_S false ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.

Hypothesis HSEC : Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8).
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
#[local] Notation LV := (LV_J E).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo false ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation MTA := (4096 * bv_unsigned (ev E 423)).
#[local] Notation GRP := (4096 * bv_unsigned (ev E 424)).
#[local] Notation ST0 := (QEoy.ST0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP).

Lemma mta_bounds : 4096 <= MTA /\ MTA + 8192 <= 2^47.
Proof. pose proof (MV4 pge_meta) as (_ & B1 & B2). unfold METAB, MV, MV_B in B1, B2. lia. Qed.
Lemma grp_bounds : 4096 <= GRP /\ GRP + 4096 <= 2^47.
Proof. pose proof (MV4 pge_grp) as (_ & B1 & B2). unfold GRPBx, GV, GV_B in B1, B2. lia. Qed.

Lemma ed_mta : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit k)) = Z_to_bv 64 (MTA + k).
Proof.
intros k Hk. destruct mta_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit k)) = Z_to_bv 64 (GRP + k).
Proof.
intros k Hk. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp0 : edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 424)) = Z_to_bv 64 (GRP + 0).
Proof. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_mul64, !u64_lit by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma lit_rw : forall A cs tcs n, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JO6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 -> sc_match JO6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m A tcs.
Proof.
intros A cs tcs n C W L H0 H1 M WF.
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X.
apply X; [exact H0 | exact H1 | exact M | exact WF | exact (img_w_b_sound JO6SEGS n A m W H0 H1)].
Qed.

Ltac piece P := lazymatch goal with H : cells_check _ _ _ _ P = true |- _ => exact H end.
Theorem rmrep_globals_B : QCwx.Mq1.rmrep_globals m.
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct STATICS_w as (W1 & W2 & W3 & W4 & W5 & W6 & _).
unfold QCwx.Mq1.rmrep_globals. split; [|split; [|split; [|split; [|split]]]].
- refine (lit_rw QW7x.Mq0.RMLOCK PLOCK_B _ 4%nat PC W1 eq_refl ltac:(unfold QW7x.Mq0.RMLOCK; lia) ltac:(unfold QW7x.Mq0.RMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PLOCK_B]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RNEED_LOCKS PNL_B _ 1%nat ltac:(piece PNL_B) W2 eq_refl ltac:(unfold QW7x.Mq0.RNEED_LOCKS; lia) ltac:(unfold QW7x.Mq0.RNEED_LOCKS; lia) _ _); [|cbn; tauto].
cbn [sc_match PNL_B]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RPAGE_SIZE PPGSZ_B _ 8%nat ltac:(piece PPGSZ_B) W3 eq_refl ltac:(unfold QW7x.Mq0.RPAGE_SIZE; lia) ltac:(unfold QW7x.Mq0.RPAGE_SIZE; lia) _ _); [|cbn; tauto].
cbn [sc_match PPGSZ_B]. split; [reflexivity | exact I].
- refine (lit_rw QW7x.Mq0.RGOT_SSP PGOTSSP_B _ 8%nat ltac:(piece PGOTSSP_B) W4 eq_refl ltac:(unfold QW7x.Mq0.RGOT_SSP; lia) ltac:(unfold QW7x.Mq0.RGOT_SSP; lia) _ _); [|cbn; tauto].
cbn [sc_match PGOTSSP_B]. split; [bytes_vm | exact I].
- refine (lit_rw QW7x.Mq0.RSSP_GUARD PSSPG_B _ 8%nat ltac:(piece PSSPG_B) W5 eq_refl ltac:(unfold QW7x.Mq0.RSSP_GUARD; lia) ltac:(unfold QW7x.Mq0.RSSP_GUARD; lia) _ _); [|cbn; tauto].
cbn [sc_match PSSPG_B]. split; [rewrite HCAN; reflexivity | exact I].
- refine (lit_rw QW7x.Mq0.RVMLOCK PVML_B _ 4%nat ltac:(piece PVML_B) W6 eq_refl ltac:(unfold QW7x.Mq0.RVMLOCK; lia) ltac:(unfold QW7x.Mq0.RVMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PVML_B]. split; [bytes_vm | exact I].
Qed.

Lemma lit_rw' : forall A cs tcs, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> QlEo_c1.rw_cells JO6SEGS m A tcs.
Proof.
intros A cs tcs C H0 H1 M WF W.
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u64 : forall A cs ws, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs (map QbVh.C8 ws) ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u64arr JO6SEGS m A ws.
Proof.
intros A cs ws C H0 H1 M W.
pose proof (check_u64arr JO6SEGS E m (kn_view ch) KV cs (ELit 0) A ws C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u8 : forall A cs bs, cells_check JO6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JO6SEGS E A cs [QbVh.CB (length bs) bs] ->
QZDE.wr_at JO6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u8arr JO6SEGS m A bs.
Proof.
intros A cs bs C H0 H1 M W.
pose proof (check_u8arr JO6SEGS E m (kn_view ch) KV cs (ELit 0) A bs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.

Lemma ctx_wr : forall k l, 0 <= k -> 0 <= l -> k + l <= 928 -> QZDE.wr_at JO6SEGS m (QW7x.Mq0.RCTX + k) l.
Proof.
intros k l Hk Hl Hkl. destruct STATICS_w as (_ & _ & _ & _ & _ & _ & W).
exact (wr_at_sub JO6SEGS m QW7x.Mq0.RCTX 928 k l (img_w_b_sound JO6SEGS 928 QW7x.Mq0.RCTX m W ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; lia)) Hk Hl Hkl).
Qed.

Lemma ctx_B : QUZl.ctx ST0 = QEoy.ST0_B_ctx Q6q3.rc_secret.  Proof. reflexivity. Qed.
Ltac cellB :=
rewrite ?ctx_B, ?brk_word_B; cbn [QEoy.ST0_B_ctx QUZl.c_secret QUZl.c_free_meta_head QUZl.c_avail_meta QUZl.c_meta_area_head QUZl.c_meta_area_tail QUZl.c_avail_meta_areas];
lazymatch goal with
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 423)) _)) = _ =>
rewrite ed_mta by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B0; reflexivity
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 424)) _)) = _ =>
rewrite ed_grp by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EMd _ _ (EVar 424))) = _ =>
rewrite ed_grp0; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EBlob _ _ _ _)) = _ => rewrite <- HSEC; reflexivity
| |- True => exact I
| |- _ = QbVh.cbytes (QbVh.C8 (QnDM_c1.Mq0.pw _ None)) => unfold QnDM_c1.Mq0.pw, QUZl.oconc; bytes_vm
| _ => bytes_vm
end.

Theorem rmrep_ctx_B : QCwx.Mq1.rmrep_ctx ST0 m.
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq1.rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- refine (lit_rw' QW7x.Mq0.RCTX PHEAD_B _ ltac:(piece PHEAD_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_head_cells. cbv zeta. cbn [sc_match PHEAD_B]. repeat split; cellB.
+ cbn. tauto.
+ replace QW7x.Mq0.RCTX with (QW7x.Mq0.RCTX + 0) by lia. apply ctx_wr; cbn; lia.
- refine (lit_u64 (QW7x.Mq0.RCTX + 80) PACT_B _ ltac:(piece PACT_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ rewrite actives_B. unfold ACT_O. cbn [sc_match PACT_B map]. repeat split; cellB.
+ apply ctx_wr; cbn; lia.
- refine (lit_u64 (QW7x.Mq0.RCTX + 464) PUSE_B _ ltac:(piece PUSE_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ rewrite usages_B. unfold USE_Aw. cbn [sc_match PUSE_B map]. repeat split; cellB.
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QW7x.Mq0.RCTX + 848) PUNM_B _ ltac:(piece PUNM_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ cbn [sc_match PUNM_B]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QW7x.Mq0.RCTX + 880) PBNC_B _ ltac:(piece PBNC_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _).
+ cbn [sc_match PBNC_B]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_rw' (QW7x.Mq0.RCTX + 912) PTAIL_B _ ltac:(piece PTAIL_B) ltac:(unfold QW7x.Mq0.RCTX; lia) ltac:(unfold QW7x.Mq0.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_tail_cells. cbn [sc_match PTAIL_B]. repeat split; cellB.
+ cbn. tauto.
+ apply ctx_wr; cbn; lia.
- reflexivity.
Qed.

Lemma u_pgM : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423))) = MTA.
Proof. exact (proj1 (MV4 pge_meta)). Qed.
Lemma u_pgG : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 424))) = GRP.
Proof. exact (proj1 (MV4 pge_grp)). Qed.
Lemma meta_wr : QZDE.wr_at JO6SEGS m (MTA + 4096) 4096.
Proof. exact (proj2 (MV4 meta_bytes)). Qed.
Lemma grp_wr : QZDE.wr_at JO6SEGS m GRP 4096.
Proof. exact (proj2 (MV4 grp_bytes)). Qed.

Lemma mta_piece_rw : forall off cs tcs, cells_check JO6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) off cs = true ->
4096 <= off -> off + Z.of_nat (scs_len cs) <= 8192 -> sc_match JO6SEGS E (MTA + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m (MTA + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct mta_bounds as [B1 B2].
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgM in X.
apply X; [lia | lia | exact M | exact WF |].
replace (MTA + off) with ((MTA + 4096) + (off - 4096)) by lia. apply (wr_at_sub JO6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.
Lemma grp_piece_rw : forall off cs tcs, cells_check JO6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) off cs = true ->
0 <= off -> off + Z.of_nat (scs_len cs) <= 4096 -> sc_match JO6SEGS E (GRP + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JO6SEGS m (GRP + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct grp_bounds as [B1 B2].
pose proof (check_rw_cells JO6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgG in X.
apply X; [lia | lia | exact M | exact WF |].
apply (wr_at_sub JO6SEGS m GRP 4096); [exact grp_wr | lia | lia | lia].
Qed.

Lemma meta_zero_run : QZDE.bytes_at JO6SEGS m (MTA + 4280) (repeat (Z_to_bv 8 0) 3912) /\ QZDE.wr_at JO6SEGS m (MTA + 4280) (Z.of_nat 3912).
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct mta_bounds as [B1 B2]. split.
- pose proof (cells_check_sound JO6SEGS E m (kn_view ch) KV PMZERO_B _ 4280 ltac:(piece PMZERO_B)) as X. cbv zeta in X. rewrite u_pgM in X.
specialize (X ltac:(lia) ltac:(cbn; lia)). cbn [sc_bytes PMZERO_B] in X. rewrite app_nil_r in X. exact X.
- replace (MTA + 4280) with ((MTA + 4096) + 184) by lia. apply (wr_at_sub JO6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.

Theorem rmrep_areas_B : QCwx.Mq1.rmrep_areas ST0 m.
Proof.
intros a ar Ha. apply areas_B_inv in Ha as [-> ->].
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct meta_zero_run as [ZB ZW].
unfold QCwx.Mq1.rarea_rep. rewrite conc_B0. cbn [QUZl.a_check QUZl.a_next QUZl.a_nslots]. split; [|split].
- refine (mta_piece_rw 4096 PMHDR_B _ ltac:(piece PMHDR_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PMHDR_B]. repeat split; cellB.
- intros k Hk. unfold QUZl.NSLOTS in Hk. unfold QUZl.aadd, QUZl.AREA_HDR, QUZl.META_SIZE. cbn [fst snd].
assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ 4 <= k) by lia. destruct K as [->|[->|[->|[->|K]]]].
+ change (4096 + (24 + 40 * 0)) with 4120. rewrite meta_B_0. replace (MTA + 4096 + 24 + 40 * 0) with (MTA + 4120) by lia.
refine (mta_piece_rw 4120 PM0_B _ ltac:(piece PM0_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM0_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 1)) with 4160. rewrite meta_B_1. replace (MTA + 4096 + 24 + 40 * 1) with (MTA + 4160) by lia.
refine (mta_piece_rw 4160 PM1_B _ ltac:(piece PM1_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM1_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 2)) with 4200. rewrite meta_B_2. replace (MTA + 4096 + 24 + 40 * 2) with (MTA + 4200) by lia.
refine (mta_piece_rw 4200 PM2_B _ ltac:(piece PM2_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM2_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 3)) with 4240. rewrite meta_B_3. replace (MTA + 4096 + 24 + 40 * 3) with (MTA + 4240) by lia.
refine (mta_piece_rw 4240 PM3_B _ ltac:(piece PM3_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM3_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ replace (4096 + (24 + 40 * k)) with (4120 + 40 * k) by lia. rewrite (meta_B_none _ _ _ _ k K).
replace (MTA + 4096 + 24 + 40 * k) with (MTA + 4280 + Z.of_nat (Z.to_nat (40 * (k - 4)))) by lia.
apply (zero_cells JO6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; tauto | rewrite meta0_bytes; reflexivity | cbn [QbVh.cells_size QnDM_c1.Mq0.meta_cells QbVh.csize]; lia].
- replace (MTA + 4096 + 4064) with (MTA + 4280 + Z.of_nat 3880) by lia.
apply (zero_cells JO6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; split; [reflexivity | exact I] | bytes_vm | cbn; lia].
Qed.

Theorem rmrep_groups_B : QCwx.Mq1.rmrep_groups ST0 m.
Proof.
intros p gh Hp. apply groups_B_inv in Hp.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq1.rgroup_rep. destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite conc_B1; cbn [QUZl.g_meta QUZl.g_active_idx].
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 0 PG0_B _ ltac:(piece PG0_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG0_B]. repeat split; cellB.
- exists (Z_to_bv 8 9). split; [|reflexivity].
refine (grp_piece_rw 48 PG3_B _ ltac:(piece PG3_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG3_B]. repeat split; cellB.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 32 PG2_B _ ltac:(piece PG2_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG2_B]. repeat split; cellB.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 16 PG1_B _ ltac:(piece PG1_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG1_B]. repeat split; cellB.
Qed.

Theorem rmrep_shadow_B : QCwx.Mq1.rmrep_shadow ST0 m.
Proof.
intros rid r Hr Hk. apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; [|discriminate Hk].
unfold QCwx.Mq1.rshadow_rep. cbn [QUZl.r_base QUZl.r_len]. change (QUZl.round_up_pg 4096) with 4096. split; [exact grp_wr|].
intros o v Ho Hc. rewrite shadow_B1 in Hc.
destruct (shadow_B_lit o v Ho Hc) as [SL V]. split; [|exact V].
pose proof (sc_lit_byte_sound JO6SEGS E GRP_B GRP (Z.to_nat o) v SL) as NTH.
pose proof (bytes_at_nth JO6SEGS m GRP _ (Z.to_nat o) _ (proj1 (MV4 grp_bytes)) NTH) as B.
rewrite Z2Nat.id in B by lia. exact B.
Qed.

#[local] Notation M1 L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo false ch HCL CS) (only parsing).
Lemma obj_facts : forall o, In o (OBJS_W false) ->
(4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x10000 \/ 0x645000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ 4096 * bv_unsigned (ev E (fst o)) + snd o <= atopE E.
Proof.
intros o Ho. pose proof (M1 in_maps_obj o Ho) as Hin. pose proof (M1 u_obj_base o Ho) as UB. pose proof (M1 u_obj_len o Ho) as UL.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ CS) as B. rewrite Forall_forall in B. destruct (B _ Hin) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi AJO6] in B4. rewrite UB, UL in B4.
pose proof (M1 maps_below_atop _ Hin) as T. rewrite UB, UL, <- (M1 main_atop) in T. split; [exact B4 | exact T].
Qed.
Lemma mta_facts : (MTA + 8192 <= 0x10000 \/ 0x645000 <= MTA) /\ MTA + 8192 <= atopE E.
Proof. exact (obj_facts (423%nat, 8192) ltac:(cbn; tauto)). Qed.
Lemma grp_facts : (GRP + 4096 <= 0x10000 \/ 0x645000 <= GRP) /\ GRP + 4096 <= atopE E.
Proof. exact (obj_facts (424%nat, 4096) ltac:(cbn; tauto)). Qed.
Lemma mta_grp_disj : GRP + 4096 <= MTA \/ MTA + 8192 <= GRP.
Proof.
assert (IM : In (423%nat, 8192) (OBJS_W false)) by (cbn; tauto). assert (IG : In (424%nat, 4096) (OBJS_W false)) by (cbn; tauto).
assert (NE : obj_e E (424%nat, 4096) <> obj_e E (423%nat, 8192)).
{ intros X. apply (M1 obj_e_inj _ _ IG IM) in X. discriminate X. }
pose proof (M1 maps_disj _ _ (M1 in_maps_obj _ IG) (M1 in_maps_obj _ IM) NE) as D. unfold iv_disjoint in D.
rewrite !(M1 u_obj_base _ IM), !(M1 u_obj_base _ IG), !(M1 u_obj_len _ IM), !(M1 u_obj_len _ IG) in D. cbn [fst snd] in D. exact D.
Qed.

Theorem rregions_wf_B : QCwx.Mq1.rregions_wf ST0.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold QCwx.Mq1.rregions_wf. split; [reflexivity|]. split; [|split; [|split]].
- intros rid r Hr. apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; cbn [QUZl.r_base QUZl.r_len];
[change (QUZl.round_up_pg 4096) with 4096 | change (QUZl.round_up_pg 8192) with 8192]; unfold Q6q3.alloc_ceiling; rewrite HCEIL;
(split; [lia|]; split; [assumption|]; split; [lia|]; split; [lia|]; apply hull_apart_free; assumption).
- intros rid1 r1 rid2 r2 H1 H2 NE. apply regions_B_inv in H1 as [[-> ->]|[-> ->]]; apply regions_B_inv in H2 as [[-> ->]|[-> ->]]; try congruence;
unfold QnDM_c1.Mq0.lr_lo; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]; change (QUZl.round_up_pg 4096) with 4096; change (QUZl.round_up_pg 8192) with 8192; lia.
- intros a ar Ha. apply areas_B_inv in Ha as [-> ->]. exists (QUZl.mkRegion QUZl.RKMeta MTA 8192). cbn [fst snd]. rewrite region_B0.
unfold QnDM_c1.Mq0.lr_lo. cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]. change (QUZl.round_up_pg 8192) with 8192.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [discriminate | lia].
- intros p gh Hp. apply groups_B_inv in Hp. exists (QUZl.mkRegion QUZl.RKGroup GRP 4096).
destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [fst snd]; rewrite region_B1; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind];
change (QUZl.round_up_pg 4096) with 4096; (split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [lia | reflexivity]).
Qed.

Theorem rmrep_main_B : QCwx.Mq1.rmrep ST0 m.
Proof. exact (conj rregions_wf_B (conj rmrep_ctx_B (conj rmrep_globals_B (conj rmrep_areas_B (conj rmrep_groups_B rmrep_shadow_B))))). Qed.

Lemma answers_B : QUZl.brk0_answer_ok 4096 = true /\ QUZl.mmap_answer_ok (QW7x.Mq0.ref_reserved ++ []) (2 * QUZl.PGSZ) MTA = true /\ QUZl.is_err MTA = false
/\ QUZl.mmap_answer_ok (QW7x.Mq0.ref_reserved ++ [(MTA, 8192)]) 4096 GRP = true /\ QUZl.is_err GRP = false.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
split; [reflexivity|]. split; [|split; [|split]].
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg (2 * 4096)) with 8192. rewrite AM. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. rewrite app_nil_r. rewrite (hull_apart_free _ _ BH).
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg 4096) with 4096. rewrite AG. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. unfold QUZl.ranges_free. rewrite forallb_app. fold (QUZl.ranges_free QW7x.Mq0.ref_reserved GRP 4096). rewrite (hull_apart_free _ _ GH).
cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply orb_true_iff; destruct D; [left | right]; apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem RHEAP_main_B : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 ->
QkLq.Mq2.RHEAP s [QnPO.Mq2.BLK0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP] m.
Proof.
intros s Hm. destruct answers_B as (A1 & A2 & A3 & A4 & A5).
exists ST0, [QnPO.Mq2.BLK0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact rmrep_main_B|]. split.
- apply QnPO.Mq2.brk_link_main_B.
- exact (QnPO.Mq2.areach_main_B Q6q3.rc_secret QW7x.Mq0.ref_reserved 4096 MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5).
Qed.

Theorem mng_main_B : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 ->
exists Lg0 : Qfya.mled,
QkLq.Mq2.RHEAP s [QnPO.Mq2.BLK0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP] m
/\ Q9kF.HSIM s Lg0 [QnPO.Mq2.BLK0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP]
/\ Qfya.ld_live Lg0 = [(1%N, 64)] /\ Qfya.ld_resv Lg0 = QW7x.Mq0.ref_reserved /\ Qfya.ld_groups Lg0 = [(GRP, 4096)]
/\ Qfya.ld_metas Lg0 = [(MTA, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None.
Proof.
intros s Hm. destruct answers_B as (A1 & A2 & A3 & A4 & A5).
pose proof (QnPO.Mq2.areach_main_B Q6q3.rc_secret QW7x.Mq0.ref_reserved 4096 MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5) as AR.
destruct (Q3o5.Mq1.areach_inv QW7x.Mq0.ref_reserved ST0 _ AR) as (L & LS & BL & INV & LIVE & RESV & _ & CR).
pose proof INV as IR. unfold Qatc.INVL in IR. cbv zeta in IR. destruct IR as [IR _].
exists L. split; [exact (RHEAP_main_B s Hm)|]. split.
- exists ST0, BL, LS, [QnPO.Mq2.BLK0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact INV | exact CR].
- split; [rewrite LIVE, <- (Q9kF.CORR_slots _ _ _ CR); reflexivity|]. split; [exact RESV|]. split; [|split].
+ pose proof (Qatc.ir_groups _ _ _ IR) as PG. rewrite groups_of_B in PG. apply Permutation.Permutation_sym in PG.
exact (Permutation.Permutation_length_1_inv PG).
+ pose proof (Qatc.ir_metas _ _ _ IR) as PM. rewrite metas_of_B in PM. apply Permutation.Permutation_sym in PM.
exact (Permutation.Permutation_length_1_inv PM).
+ destruct (Qfya.ld_brkreg L) as [[bb ll]|] eqn:EB; [|reflexivity]. exfalso.
apply (Qatc.ir_brkreg _ _ _ IR) in EB as (rid & r & Hr & Hk & _). apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; discriminate Hk.
Qed.
End RmrepB.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXEH QHqi QlHe QMhO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QvSK.Mq0 QvQl Qn7S QlHe.Mq0 Qb5q.Mq1 QMhO.
Import QbBz.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma conc_A0 : forall sec resv b g off, QUZl.conc (Q8zf.ST0_A sec resv b g) (0%N, off) = b + off.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma conc_A1 : forall sec resv b g off, QUZl.conc (Q8zf.ST0_A sec resv b g) (1%N, off) = g + off.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma actives_A : forall sec resv b g, QnDM_c1.Mq0.actives (Q8zf.ST0_A sec resv b g) = map (QnDM_c1.Mq0.pw (Q8zf.ST0_A sec resv b g)) ACT_O.
Proof.
intros. unfold QnDM_c1.Mq0.actives. rewrite <- (map_map (fun i => QUZl.active (Q8zf.ST0_A sec resv b g) (Z.of_nat i)) (QnDM_c1.Mq0.pw (Q8zf.ST0_A sec resv b g))).
f_equal; try (vm_compute; reflexivity).
Qed.
Lemma usages_A : forall sec resv b g, QnDM_c1.Mq0.usages (Q8zf.ST0_A sec resv b g) = USE_Aw.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma brk_word_A : forall sec resv b g, QnDM_c1.Mq0.brk_word (Q8zf.ST0_A sec resv b g) = b + 8192.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma areas_A_inv : forall sec resv b g a ar, QUZl.s_areas (Q8zf.ST0_A sec resv b g) !! a = Some ar -> a = (0%N, 4096) /\ ar = QUZl.mkArea sec None 101.
Proof. intros sec resv b g a ar H. apply l2m_some in H. destruct H as [[= <- <-]|[]]. split; reflexivity. Qed.
Lemma groups_A_inv : forall sec resv b g p gh, QUZl.s_groups (Q8zf.ST0_A sec resv b g) !! p = Some gh ->
(p = (1%N, 0) /\ gh = QUZl.mkGhdr (Some (0%N, 4240)) 1) \/ (p = (1%N, 48) /\ gh = QUZl.mkGhdr (Some (0%N, 4120)) 9)
\/ (p = (1%N, 32) /\ gh = QUZl.mkGhdr (Some (0%N, 4160)) 1) \/ (p = (1%N, 16) /\ gh = QUZl.mkGhdr (Some (0%N, 4200)) 1).
Proof. intros sec resv b g p gh H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; tauto. Qed.
Lemma regions_A_inv : forall sec resv b g rid r, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! rid = Some r ->
(rid = 1%N /\ r = QUZl.mkRegion QUZl.RKGroup g 4096) \/ (rid = 0%N /\ r = QUZl.mkRegion QUZl.RKBrk b 8192).
Proof. intros sec resv b g rid r H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[]]]; tauto. Qed.
Lemma region_A0 : forall sec resv b g, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! 0%N = Some (QUZl.mkRegion QUZl.RKBrk b 8192).
Proof. intros. vm_compute. reflexivity. Qed.
Lemma region_A1 : forall sec resv b g, QUZl.s_regions (Q8zf.ST0_A sec resv b g) !! 1%N = Some (QUZl.mkRegion QUZl.RKGroup g 4096).
Proof. intros. vm_compute. reflexivity. Qed.

Lemma meta_A_0 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4120) = QUZl.mkMeta (Some (0%N, 4120)) (Some (0%N, 4120)) (Some (1%N, 48)) 1022 0 9 1 2 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_1 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4160) = QUZl.mkMeta (Some (0%N, 4160)) (Some (0%N, 4160)) (Some (1%N, 32)) 2 0 1 1 15 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_2 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4200) = QUZl.mkMeta (Some (0%N, 4200)) (Some (0%N, 4200)) (Some (1%N, 16)) 2 0 1 1 19 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_3 : forall sec resv b g, QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4240) = QUZl.mkMeta (Some (0%N, 4240)) (Some (0%N, 4240)) (Some (1%N, 0)) 2 0 1 1 23 1.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_A_none : forall sec resv b g k, 4 <= k -> QUZl.get_meta_rec (Q8zf.ST0_A sec resv b g) (0%N, 4120 + 40 * k) = QUZl.meta0.
Proof.
intros sec resv b g k Hk. unfold QUZl.get_meta_rec. replace (QUZl.s_metas (Q8zf.ST0_A sec resv b g) !! (0%N, 4120 + 40 * k)) with (@None QUZl.meta); [reflexivity|].
symmetry. apply l2m_none. cbn [map fst]. intros [X|[X|[X|[X|[]]]]]; injection X; lia.
Qed.

Definition SH_A : QUZl.shadow := QUZl.get_shadow (Q8zf.ST0_A 0 [] 0 0) 1%N.
Lemma shadow_A1 : forall sec resv b g, QUZl.get_shadow (Q8zf.ST0_A sec resv b g) 1%N = SH_A.
Proof. intros. reflexivity. Qed.

Lemma SHADOW_A_ok : mng_shadow_ok SH_A GRP_A 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shadow_A_lit : forall o v, 0 <= o < 4096 -> QUZl.cell_read SH_A o = QUZl.Known v -> sc_lit_byte GRP_A (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof. intros o v Ho Hc. exact (mng_shadow_ok_sound SH_A GRP_A 4096 o v SHADOW_A_ok Ho Hc). Qed.

Lemma groups_of_A : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr)))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKGroup => true | _ => false end) (map_to_list (QUZl.s_regions (Q8zf.ST0_A sec resv b g))))
= [(g, 4096)].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma metas_of_A : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr), Qatc.frontier (Q8zf.ST0_A sec resv b g) (fst kr) (snd kr) / QUZl.PGSZ - 1))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKMeta => true | _ => false end) (map_to_list (QUZl.s_regions (Q8zf.ST0_A sec resv b g))))
= [].
Proof. intros. vm_compute. reflexivity. Qed.

Section RmrepA.
Context {RC__ : Q6q3.RunConsts}.
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
Variable ch : acs.
Hypothesis HCL : HSCLASS_S true ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.

Hypothesis HSEC : Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8).
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
#[local] Notation LV := (LV_J E).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo true ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation MTA := (4096 * bv_unsigned (ev E 5)).
#[local] Notation GRP := (4096 * bv_unsigned (ev E 423)).
#[local] Notation ST0 := (Q8zf.ST0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP).

Lemma mta_bounds : 4096 <= MTA /\ MTA + 8192 <= 2^47.
Proof. pose proof (MV4 pge_meta) as (_ & B1 & B2). unfold METAB, MV, MV_A in B1, B2. lia. Qed.
Lemma grp_bounds : 4096 <= GRP /\ GRP + 4096 <= 2^47.
Proof. pose proof (MV4 pge_grp) as (_ & B1 & B2). unfold GRPBx, GV, GV_A in B1, B2. lia. Qed.

Lemma ed_mta : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit k)) = Z_to_bv 64 (MTA + k).
Proof.
intros k Hk. destruct mta_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit k)) = Z_to_bv 64 (GRP + k).
Proof.
intros k Hk. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp0 : edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423)) = Z_to_bv 64 (GRP + 0).
Proof. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_mul64, !u64_lit by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma lit_rw : forall A cs tcs n, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JOB6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 -> sc_match JOB6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m A tcs.
Proof.
intros A cs tcs n C W L H0 H1 M WF.
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X.
apply X; [exact H0 | exact H1 | exact M | exact WF | exact (img_w_b_sound JOB6SEGS n A m W H0 H1)].
Qed.

Ltac piece P := lazymatch goal with H : cells_check _ _ _ _ P = true |- _ => exact H end.
Theorem rmrep_globals_A : QCwx.Mq3.rmrep_globals m.
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct STATICS_w as (W1 & W2 & W3 & W4 & W5 & W6 & _).
unfold QCwx.Mq3.rmrep_globals. split; [|split; [|split; [|split; [|split]]]].
- refine (lit_rw QXEH.RMLOCK PLOCK_A _ 4%nat PC W1 eq_refl ltac:(unfold QXEH.RMLOCK; lia) ltac:(unfold QXEH.RMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PLOCK_A]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RNEED_LOCKS PNL_A _ 1%nat ltac:(piece PNL_A) W2 eq_refl ltac:(unfold QXEH.RNEED_LOCKS; lia) ltac:(unfold QXEH.RNEED_LOCKS; lia) _ _); [|cbn; tauto].
cbn [sc_match PNL_A]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RPAGE_SIZE PPGSZ_A _ 8%nat ltac:(piece PPGSZ_A) W3 eq_refl ltac:(unfold QXEH.RPAGE_SIZE; lia) ltac:(unfold QXEH.RPAGE_SIZE; lia) _ _); [|cbn; tauto].
cbn [sc_match PPGSZ_A]. split; [reflexivity | exact I].
- refine (lit_rw QXEH.RGOT_SSP PGOTSSP_A _ 8%nat ltac:(piece PGOTSSP_A) W4 eq_refl ltac:(unfold QXEH.RGOT_SSP; lia) ltac:(unfold QXEH.RGOT_SSP; lia) _ _); [|cbn; tauto].
cbn [sc_match PGOTSSP_A]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RSSP_GUARD PSSPG_A _ 8%nat ltac:(piece PSSPG_A) W5 eq_refl ltac:(unfold QXEH.RSSP_GUARD; lia) ltac:(unfold QXEH.RSSP_GUARD; lia) _ _); [|cbn; tauto].
cbn [sc_match PSSPG_A]. split; [rewrite HCAN; reflexivity | exact I].
- refine (lit_rw QXEH.RVMLOCK PVML_A _ 4%nat ltac:(piece PVML_A) W6 eq_refl ltac:(unfold QXEH.RVMLOCK; lia) ltac:(unfold QXEH.RVMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PVML_A]. split; [bytes_vm | exact I].
Qed.

Lemma lit_rw' : forall A cs tcs, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> QlEo_c1.rw_cells JOB6SEGS m A tcs.
Proof.
intros A cs tcs C H0 H1 M WF W.
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u64 : forall A cs ws, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs (map QbVh.C8 ws) ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u64arr JOB6SEGS m A ws.
Proof.
intros A cs ws C H0 H1 M W.
pose proof (check_u64arr JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A ws C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u8 : forall A cs bs, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs [QbVh.CB (length bs) bs] ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u8arr JOB6SEGS m A bs.
Proof.
intros A cs bs C H0 H1 M W.
pose proof (check_u8arr JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A bs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.

Lemma ctx_wr : forall k l, 0 <= k -> 0 <= l -> k + l <= 928 -> QZDE.wr_at JOB6SEGS m (QXEH.RCTX + k) l.
Proof.
intros k l Hk Hl Hkl. destruct STATICS_w as (_ & _ & _ & _ & _ & _ & W).
exact (wr_at_sub JOB6SEGS m QXEH.RCTX 928 k l (img_w_b_sound JOB6SEGS 928 QXEH.RCTX m W ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; lia)) Hk Hl Hkl).
Qed.

Lemma ctx_A : QUZl.ctx ST0 = Q8zf.ST0_A_ctx Q6q3.rc_secret.  Proof. reflexivity. Qed.
Ltac cellA :=
rewrite ?ctx_A, ?brk_word_A; cbn [Q8zf.ST0_A_ctx QUZl.c_secret QUZl.c_free_meta_head QUZl.c_avail_meta QUZl.c_meta_area_head QUZl.c_meta_area_tail QUZl.c_avail_meta_areas];
lazymatch goal with
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 5)) _)) = _ =>
rewrite ed_mta by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A0; reflexivity
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 423)) _)) = _ =>
rewrite ed_grp by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EMd _ _ (EVar 423))) = _ =>
rewrite ed_grp0; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_A1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EBlob _ _ _ _)) = _ => rewrite <- HSEC; reflexivity
| |- True => exact I
| |- _ = QbVh.cbytes (QbVh.C8 (QnDM_c1.Mq0.pw _ None)) => unfold QnDM_c1.Mq0.pw, QUZl.oconc; bytes_vm
| _ => bytes_vm
end.

Theorem rmrep_ctx_A : QCwx.Mq3.rmrep_ctx ST0 m.
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq3.rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- refine (lit_rw' QXEH.RCTX PHEAD_A _ ltac:(piece PHEAD_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_head_cells. cbv zeta. cbn [sc_match PHEAD_A]. repeat split; cellA.
+ cbn. tauto.
+ replace QXEH.RCTX with (QXEH.RCTX + 0) by lia. apply ctx_wr; cbn; lia.
- refine (lit_u64 (QXEH.RCTX + 80) PACT_A _ ltac:(piece PACT_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ rewrite actives_A. unfold ACT_O. cbn [sc_match PACT_A map]. repeat split; cellA.
+ apply ctx_wr; cbn; lia.
- refine (lit_u64 (QXEH.RCTX + 464) PUSE_A _ ltac:(piece PUSE_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ rewrite usages_A. unfold USE_Aw. cbn [sc_match PUSE_A map]. repeat split; cellA.
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QXEH.RCTX + 848) PUNM_A _ ltac:(piece PUNM_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ cbn [sc_match PUNM_A]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QXEH.RCTX + 880) PBNC_A _ ltac:(piece PBNC_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ cbn [sc_match PBNC_A]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_rw' (QXEH.RCTX + 912) PTAIL_A _ ltac:(piece PTAIL_A) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_tail_cells. cbn [sc_match PTAIL_A]. repeat split; cellA.
+ cbn. tauto.
+ apply ctx_wr; cbn; lia.
- reflexivity.
Qed.

Lemma u_pgM : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 5))) = MTA.
Proof. exact (proj1 (MV4 pge_meta)). Qed.
Lemma u_pgG : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423))) = GRP.
Proof. exact (proj1 (MV4 pge_grp)). Qed.
Lemma meta_wr : QZDE.wr_at JOB6SEGS m (MTA + 4096) 4096.
Proof. exact (proj2 (MV4 meta_bytes)). Qed.
Lemma grp_wr : QZDE.wr_at JOB6SEGS m GRP 4096.
Proof. exact (proj2 (MV4 grp_bytes)). Qed.

Lemma mta_piece_rw : forall off cs tcs, cells_check JOB6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) off cs = true ->
4096 <= off -> off + Z.of_nat (scs_len cs) <= 8192 -> sc_match JOB6SEGS E (MTA + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m (MTA + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct mta_bounds as [B1 B2].
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgM in X.
apply X; [lia | lia | exact M | exact WF |].
replace (MTA + off) with ((MTA + 4096) + (off - 4096)) by lia. apply (wr_at_sub JOB6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.
Lemma grp_piece_rw : forall off cs tcs, cells_check JOB6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) off cs = true ->
0 <= off -> off + Z.of_nat (scs_len cs) <= 4096 -> sc_match JOB6SEGS E (GRP + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m (GRP + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct grp_bounds as [B1 B2].
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgG in X.
apply X; [lia | lia | exact M | exact WF |].
apply (wr_at_sub JOB6SEGS m GRP 4096); [exact grp_wr | lia | lia | lia].
Qed.

Lemma meta_zero_run : QZDE.bytes_at JOB6SEGS m (MTA + 4280) (repeat (Z_to_bv 8 0) 3912) /\ QZDE.wr_at JOB6SEGS m (MTA + 4280) (Z.of_nat 3912).
Proof.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct mta_bounds as [B1 B2]. split.
- pose proof (cells_check_sound JOB6SEGS E m (kn_view ch) KV PMZERO_A _ 4280 ltac:(piece PMZERO_A)) as X. cbv zeta in X. rewrite u_pgM in X.
specialize (X ltac:(lia) ltac:(cbn; lia)). cbn [sc_bytes PMZERO_A] in X. rewrite app_nil_r in X. exact X.
- replace (MTA + 4280) with ((MTA + 4096) + 184) by lia. apply (wr_at_sub JOB6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.

Theorem rmrep_areas_A : QCwx.Mq3.rmrep_areas ST0 m.
Proof.
intros a ar Ha. apply areas_A_inv in Ha as [-> ->].
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct meta_zero_run as [ZB ZW].
unfold QCwx.Mq3.rarea_rep. rewrite conc_A0. cbn [QUZl.a_check QUZl.a_next QUZl.a_nslots]. split; [|split].
- refine (mta_piece_rw 4096 PMHDR_A _ ltac:(piece PMHDR_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PMHDR_A]. repeat split; cellA.
- intros k Hk. unfold QUZl.NSLOTS in Hk. unfold QUZl.aadd, QUZl.AREA_HDR, QUZl.META_SIZE. cbn [fst snd].
assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ 4 <= k) by lia. destruct K as [->|[->|[->|[->|K]]]].
+ change (4096 + (24 + 40 * 0)) with 4120. rewrite meta_A_0. replace (MTA + 4096 + 24 + 40 * 0) with (MTA + 4120) by lia.
refine (mta_piece_rw 4120 PM0_A _ ltac:(piece PM0_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM0_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 1)) with 4160. rewrite meta_A_1. replace (MTA + 4096 + 24 + 40 * 1) with (MTA + 4160) by lia.
refine (mta_piece_rw 4160 PM1_A _ ltac:(piece PM1_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM1_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 2)) with 4200. rewrite meta_A_2. replace (MTA + 4096 + 24 + 40 * 2) with (MTA + 4200) by lia.
refine (mta_piece_rw 4200 PM2_A _ ltac:(piece PM2_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM2_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ change (4096 + (24 + 40 * 3)) with 4240. rewrite meta_A_3. replace (MTA + 4096 + 24 + 40 * 3) with (MTA + 4240) by lia.
refine (mta_piece_rw 4240 PM3_A _ ltac:(piece PM3_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM3_A QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellA.
+ replace (4096 + (24 + 40 * k)) with (4120 + 40 * k) by lia. rewrite (meta_A_none _ _ _ _ k K).
replace (MTA + 4096 + 24 + 40 * k) with (MTA + 4280 + Z.of_nat (Z.to_nat (40 * (k - 4)))) by lia.
apply (zero_cells JOB6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; tauto | rewrite meta0_bytes; reflexivity | cbn [QbVh.cells_size QnDM_c1.Mq0.meta_cells QbVh.csize]; lia].
- replace (MTA + 4096 + 4064) with (MTA + 4280 + Z.of_nat 3880) by lia.
apply (zero_cells JOB6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; split; [reflexivity | exact I] | bytes_vm | cbn; lia].
Qed.

Theorem rmrep_groups_A : QCwx.Mq3.rmrep_groups ST0 m.
Proof.
intros p gh Hp. apply groups_A_inv in Hp.
pose proof (PIECES_A ch HCL) as PC. unfold pieces_check_A in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq3.rgroup_rep. destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite conc_A1; cbn [QUZl.g_meta QUZl.g_active_idx].
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 0 PG0_A _ ltac:(piece PG0_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG0_A]. repeat split; cellA.
- exists (Z_to_bv 8 9). split; [|reflexivity].
refine (grp_piece_rw 48 PG3_A _ ltac:(piece PG3_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG3_A]. repeat split; cellA.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 32 PG2_A _ ltac:(piece PG2_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG2_A]. repeat split; cellA.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 16 PG1_A _ ltac:(piece PG1_A) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG1_A]. repeat split; cellA.
Qed.

Theorem rmrep_shadow_A : QCwx.Mq3.rmrep_shadow ST0 m.
Proof.
intros rid r Hr Hk. apply regions_A_inv in Hr as [[-> ->]|[-> ->]]; [|discriminate Hk].
unfold QCwx.Mq3.rshadow_rep. cbn [QUZl.r_base QUZl.r_len]. change (QUZl.round_up_pg 4096) with 4096. split; [exact grp_wr|].
intros o v Ho Hc. rewrite shadow_A1 in Hc.
destruct (shadow_A_lit o v Ho Hc) as [SL V]. split; [|exact V].
pose proof (sc_lit_byte_sound JOB6SEGS E GRP_A GRP (Z.to_nat o) v SL) as NTH.
pose proof (bytes_at_nth JOB6SEGS m GRP _ (Z.to_nat o) _ (proj1 (MV4 grp_bytes)) NTH) as B.
rewrite Z2Nat.id in B by lia. exact B.
Qed.

#[local] Notation M1 L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo true ch HCL CS) (only parsing).
Lemma obj_facts : forall o, In o (OBJS_W true) ->
(4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x10000 \/ 0x647000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ 4096 * bv_unsigned (ev E (fst o)) + snd o <= atopE E.
Proof.
intros o Ho. pose proof (M1 in_maps_obj o Ho) as Hin. pose proof (M1 u_obj_base o Ho) as UB. pose proof (M1 u_obj_len o Ho) as UL.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ CS) as B. rewrite Forall_forall in B. destruct (B _ Hin) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi BJO6] in B4. rewrite UB, UL in B4.
pose proof (M1 maps_below_atop _ Hin) as T. rewrite UB, UL, <- (M1 main_atop) in T. split; [exact B4 | exact T].
Qed.
Lemma mta_facts : (MTA + 8192 <= 0x10000 \/ 0x647000 <= MTA) /\ MTA + 8192 <= atopE E.
Proof. exact (obj_facts (5%nat, 8192) ltac:(cbn; tauto)). Qed.
Lemma grp_facts : (GRP + 4096 <= 0x10000 \/ 0x647000 <= GRP) /\ GRP + 4096 <= atopE E.
Proof. exact (obj_facts (423%nat, 4096) ltac:(cbn; tauto)). Qed.
Lemma mta_grp_disj : GRP + 4096 <= MTA \/ MTA + 8192 <= GRP.
Proof.
assert (IM : In (5%nat, 8192) (OBJS_W true)) by (cbn; tauto). assert (IG : In (423%nat, 4096) (OBJS_W true)) by (cbn; tauto).
assert (NE : obj_e E (423%nat, 4096) <> obj_e E (5%nat, 8192)).
{ intros X. apply (M1 obj_e_inj _ _ IG IM) in X. discriminate X. }
pose proof (M1 maps_disj _ _ (M1 in_maps_obj _ IG) (M1 in_maps_obj _ IM) NE) as D. unfold iv_disjoint in D.
rewrite !(M1 u_obj_base _ IM), !(M1 u_obj_base _ IG), !(M1 u_obj_len _ IM), !(M1 u_obj_len _ IG) in D. cbn [fst snd] in D. exact D.
Qed.

Theorem rregions_wf_A : QCwx.Mq3.rregions_wf ST0.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold QCwx.Mq3.rregions_wf. split; [reflexivity|]. split; [|split; [|split]].
- intros rid r Hr. apply regions_A_inv in Hr as [[-> ->]|[-> ->]]; cbn [QUZl.r_base QUZl.r_len];
[change (QUZl.round_up_pg 4096) with 4096 | change (QUZl.round_up_pg 8192) with 8192]; unfold Q6q3.alloc_ceiling; rewrite HCEIL;
(split; [lia|]; split; [assumption|]; split; [lia|]; split; [lia|]; apply hull_apart_free; assumption).
- intros rid1 r1 rid2 r2 H1 H2 NE. apply regions_A_inv in H1 as [[-> ->]|[-> ->]]; apply regions_A_inv in H2 as [[-> ->]|[-> ->]]; try congruence;
unfold QnDM_c1.Mq0.lr_lo; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]; change (QUZl.round_up_pg 4096) with 4096; change (QUZl.round_up_pg 8192) with 8192; lia.
- intros a ar Ha. apply areas_A_inv in Ha as [-> ->]. exists (QUZl.mkRegion QUZl.RKBrk MTA 8192). cbn [fst snd]. rewrite region_A0.
unfold QnDM_c1.Mq0.lr_lo. cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]. change (QUZl.round_up_pg 8192) with 8192.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [discriminate | lia].
- intros p gh Hp. apply groups_A_inv in Hp. exists (QUZl.mkRegion QUZl.RKGroup GRP 4096).
destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [fst snd]; rewrite region_A1; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind];
change (QUZl.round_up_pg 4096) with 4096; (split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [lia | reflexivity]).
Qed.

Theorem rmrep_main_A : QCwx.Mq3.rmrep ST0 m.
Proof. exact (conj rregions_wf_A (conj rmrep_ctx_A (conj rmrep_globals_A (conj rmrep_areas_A (conj rmrep_groups_A rmrep_shadow_A))))). Qed.

Lemma answers_A : QUZl.brk0_answer_ok MTA = true /\ QUZl.brk_pages_ok (QUZl.minit Q6q3.rc_secret QXEH.ref_reserved) MTA (2 * QUZl.PGSZ) = true
/\ QUZl.mmap_fixed_answer_ok MTA MTA = true /\ QUZl.mmap_answer_ok (QXEH.ref_reserved ++ [(MTA + 4096, 4096)]) 4096 GRP = true /\ QUZl.is_err GRP = false.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
split; [|split; [|split; [|split]]].
- unfold QUZl.brk0_answer_ok, QUZl.PGSZ, QUZl.TWO64. rewrite AM. apply andb_true_intro. split; [apply andb_true_intro; split|]; [apply Z.ltb_lt; lia | reflexivity | apply Z.ltb_lt; lia].
- unfold QUZl.brk_pages_ok, QUZl.live_ranges, QUZl.PGSZ. cbn [QUZl.s_reserved QUZl.s_regions QUZl.minit]. rewrite map_to_list_empty. cbn [map]. rewrite app_nil_r.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. apply andb_true_intro. split; [apply andb_true_intro; split|]; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply hull_apart_free; exact BH].
- unfold QUZl.mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg 4096) with 4096. rewrite AG. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. unfold QUZl.ranges_free. rewrite forallb_app. fold (QUZl.ranges_free QXEH.ref_reserved GRP 4096). rewrite (hull_apart_free _ _ GH).
cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply orb_true_iff; destruct D; [left | right]; apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem RHEAP_main_A : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 -> QGeV.ps_brk s = MTA + 8192 ->
QkLq.Mq4.RHEAP s [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP] m.
Proof.
intros s Hm Hb. destruct answers_A as (A1 & A2 & A3 & A4 & A5).
exists ST0, [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact rmrep_main_A|]. split.
- rewrite Hb. apply Q9O6.Mq3.brk_link_main_A.
- exact (Q9O6.Mq3.areach_main_A Q6q3.rc_secret QXEH.ref_reserved MTA MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5).
Qed.

Theorem mng_main_A : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 -> QGeV.ps_brk s = MTA + 8192 ->
exists Lg0 : Qfya.mled,
QkLq.Mq4.RHEAP s [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP] m
/\ Q9kF.HSIM s Lg0 [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP]
/\ Qfya.ld_live Lg0 = [(1%N, 64)] /\ Qfya.ld_resv Lg0 = QXEH.ref_reserved /\ Qfya.ld_groups Lg0 = [(GRP, 4096)]
/\ Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTA, 8192).
Proof.
intros s Hm Hb. destruct answers_A as (A1 & A2 & A3 & A4 & A5).
pose proof (Q9O6.Mq3.areach_main_A Q6q3.rc_secret QXEH.ref_reserved MTA MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5) as AR.
destruct (Q3o5.Mq1.areach_inv QXEH.ref_reserved ST0 _ AR) as (L & LS & BL & INV & LIVE & RESV & _ & CR).
pose proof INV as IR. unfold Qatc.INVL in IR. cbv zeta in IR. destruct IR as [IR _].
exists L. split; [exact (RHEAP_main_A s Hm Hb)|]. split.
- exists ST0, BL, LS, [Q9O6.Mq3.BLK0_A Q6q3.rc_secret QXEH.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact INV | exact CR].
- split; [rewrite LIVE, <- (Q9kF.CORR_slots _ _ _ CR); reflexivity|]. split; [exact RESV|]. split; [|split].
+ pose proof (Qatc.ir_groups _ _ _ IR) as PG. rewrite groups_of_A in PG. apply Permutation.Permutation_sym in PG.
exact (Permutation.Permutation_length_1_inv PG).
+ pose proof (Qatc.ir_metas _ _ _ IR) as PM. rewrite metas_of_A in PM. apply Permutation.Permutation_sym in PM.
exact (Permutation.Permutation_nil PM).
+ apply (Qatc.ir_brkreg _ _ _ IR). exists 0%N, (QUZl.mkRegion QUZl.RKBrk MTA 8192). rewrite region_A0. repeat split.
Qed.
End RmrepA.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1.
Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi QvSK.Mq0 QvQl Qn7S QlHe.Mq0 Qb5q.Mq1 QMhO.
Import QbBz.Mq0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma conc_B0 : forall sec resv b g off, QUZl.conc (QEoy.ST0_B sec resv b g) (0%N, off) = b + off.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma conc_B1 : forall sec resv b g off, QUZl.conc (QEoy.ST0_B sec resv b g) (1%N, off) = g + off.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma actives_B : forall sec resv b g, QnDM_c1.Mq0.actives (QEoy.ST0_B sec resv b g) = map (QnDM_c1.Mq0.pw (QEoy.ST0_B sec resv b g)) ACT_O.
Proof.
intros. unfold QnDM_c1.Mq0.actives. rewrite <- (map_map (fun i => QUZl.active (QEoy.ST0_B sec resv b g) (Z.of_nat i)) (QnDM_c1.Mq0.pw (QEoy.ST0_B sec resv b g))).
f_equal; try (vm_compute; reflexivity).
Qed.
Lemma usages_B : forall sec resv b g, QnDM_c1.Mq0.usages (QEoy.ST0_B sec resv b g) = USE_Aw.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma brk_word_B : forall sec resv b g, QnDM_c1.Mq0.brk_word (QEoy.ST0_B sec resv b g) = 2^64 - 1.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma areas_B_inv : forall sec resv b g a ar, QUZl.s_areas (QEoy.ST0_B sec resv b g) !! a = Some ar -> a = (0%N, 4096) /\ ar = QUZl.mkArea sec None 101.
Proof. intros sec resv b g a ar H. apply l2m_some in H. destruct H as [[= <- <-]|[]]. split; reflexivity. Qed.
Lemma groups_B_inv : forall sec resv b g p gh, QUZl.s_groups (QEoy.ST0_B sec resv b g) !! p = Some gh ->
(p = (1%N, 0) /\ gh = QUZl.mkGhdr (Some (0%N, 4240)) 1) \/ (p = (1%N, 48) /\ gh = QUZl.mkGhdr (Some (0%N, 4120)) 9)
\/ (p = (1%N, 32) /\ gh = QUZl.mkGhdr (Some (0%N, 4160)) 1) \/ (p = (1%N, 16) /\ gh = QUZl.mkGhdr (Some (0%N, 4200)) 1).
Proof. intros sec resv b g p gh H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[[= <- <-]|[[= <- <-]|[]]]]]; tauto. Qed.
Lemma regions_B_inv : forall sec resv b g rid r, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! rid = Some r ->
(rid = 1%N /\ r = QUZl.mkRegion QUZl.RKGroup g 4096) \/ (rid = 0%N /\ r = QUZl.mkRegion QUZl.RKMeta b 8192).
Proof. intros sec resv b g rid r H. apply l2m_some in H. destruct H as [[= <- <-]|[[= <- <-]|[]]]; tauto. Qed.
Lemma region_B0 : forall sec resv b g, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! 0%N = Some (QUZl.mkRegion QUZl.RKMeta b 8192).
Proof. intros. vm_compute. reflexivity. Qed.
Lemma region_B1 : forall sec resv b g, QUZl.s_regions (QEoy.ST0_B sec resv b g) !! 1%N = Some (QUZl.mkRegion QUZl.RKGroup g 4096).
Proof. intros. vm_compute. reflexivity. Qed.

Lemma meta_B_0 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4120) = QUZl.mkMeta (Some (0%N, 4120)) (Some (0%N, 4120)) (Some (1%N, 48)) 1022 0 9 1 2 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_1 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4160) = QUZl.mkMeta (Some (0%N, 4160)) (Some (0%N, 4160)) (Some (1%N, 32)) 2 0 1 1 15 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_2 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4200) = QUZl.mkMeta (Some (0%N, 4200)) (Some (0%N, 4200)) (Some (1%N, 16)) 2 0 1 1 19 0.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_3 : forall sec resv b g, QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4240) = QUZl.mkMeta (Some (0%N, 4240)) (Some (0%N, 4240)) (Some (1%N, 0)) 2 0 1 1 23 1.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma meta_B_none : forall sec resv b g k, 4 <= k -> QUZl.get_meta_rec (QEoy.ST0_B sec resv b g) (0%N, 4120 + 40 * k) = QUZl.meta0.
Proof.
intros sec resv b g k Hk. unfold QUZl.get_meta_rec. replace (QUZl.s_metas (QEoy.ST0_B sec resv b g) !! (0%N, 4120 + 40 * k)) with (@None QUZl.meta); [reflexivity|].
symmetry. apply l2m_none. cbn [map fst]. intros [X|[X|[X|[X|[]]]]]; injection X; lia.
Qed.

Definition SH_B : QUZl.shadow := QUZl.get_shadow (QEoy.ST0_B 0 [] 0 0) 1%N.
Lemma shadow_B1 : forall sec resv b g, QUZl.get_shadow (QEoy.ST0_B sec resv b g) 1%N = SH_B.
Proof. intros. reflexivity. Qed.

Lemma SHADOW_B_ok : mng_shadow_ok SH_B GRP_B 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma shadow_B_lit : forall o v, 0 <= o < 4096 -> QUZl.cell_read SH_B o = QUZl.Known v -> sc_lit_byte GRP_B (Z.to_nat o) = Some v /\ 0 <= v < 256.
Proof. intros o v Ho Hc. exact (mng_shadow_ok_sound SH_B GRP_B 4096 o v SHADOW_B_ok Ho Hc). Qed.

Lemma groups_of_B : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr)))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKGroup => true | _ => false end) (map_to_list (QUZl.s_regions (QEoy.ST0_B sec resv b g))))
= [(g, 4096)].
Proof. intros. vm_compute. reflexivity. Qed.
Lemma metas_of_B : forall sec resv b g,
map (fun kr : N * QUZl.region => (QUZl.r_base (snd kr), QUZl.r_len (snd kr), Qatc.frontier (QEoy.ST0_B sec resv b g) (fst kr) (snd kr) / QUZl.PGSZ - 1))
(List.filter (fun kr : N * QUZl.region => match QUZl.r_kind (snd kr) with QUZl.RKMeta => true | _ => false end) (map_to_list (QUZl.s_regions (QEoy.ST0_B sec resv b g))))
= [(b, 8192, 1)].
Proof. intros. vm_compute. reflexivity. Qed.

Section RmrepB.
Context {RC__ : Q6q3.RunConsts}.
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
Variable ch : acs.
Hypothesis HCL : HSCLASS_S false ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.

Hypothesis HSEC : Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8).
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
#[local] Notation LV := (LV_J E).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo false ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).
#[local] Notation MTA := (4096 * bv_unsigned (ev E 423)).
#[local] Notation GRP := (4096 * bv_unsigned (ev E 424)).
#[local] Notation ST0 := (QEoy.ST0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP).

Lemma mta_bounds : 4096 <= MTA /\ MTA + 8192 <= 2^47.
Proof. pose proof (MV4 pge_meta) as (_ & B1 & B2). unfold METAB, MV, MV_B in B1, B2. lia. Qed.
Lemma grp_bounds : 4096 <= GRP /\ GRP + 4096 <= 2^47.
Proof. pose proof (MV4 pge_grp) as (_ & B1 & B2). unfold GRPBx, GV, GV_B in B1, B2. lia. Qed.

Lemma ed_mta : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit k)) = Z_to_bv 64 (MTA + k).
Proof.
intros k Hk. destruct mta_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp : forall k, 0 <= k < 2^32 -> edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit k)) = Z_to_bv 64 (GRP + k).
Proof.
intros k Hk. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_add64, u_mul64, !u64_lit by lia.
rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma ed_grp0 : edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 424)) = Z_to_bv 64 (GRP + 0).
Proof. destruct grp_bounds. apply bv_eq. cbn [edenot]. rewrite u_mul64, !u64_lit by lia. rewrite Z.mod_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma lit_rw : forall A cs tcs n, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true -> img_w_b JOB6SEGS A n = true ->
scs_len cs = n -> 0 <= A -> A + Z.of_nat n <= 2^64 -> sc_match JOB6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m A tcs.
Proof.
intros A cs tcs n C W L H0 H1 M WF.
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l, L in X.
apply X; [exact H0 | exact H1 | exact M | exact WF | exact (img_w_b_sound JOB6SEGS n A m W H0 H1)].
Qed.

Ltac piece P := lazymatch goal with H : cells_check _ _ _ _ P = true |- _ => exact H end.
Theorem rmrep_globals_B : QCwx.Mq3.rmrep_globals m.
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct STATICS_w as (W1 & W2 & W3 & W4 & W5 & W6 & _).
unfold QCwx.Mq3.rmrep_globals. split; [|split; [|split; [|split; [|split]]]].
- refine (lit_rw QXEH.RMLOCK PLOCK_B _ 4%nat PC W1 eq_refl ltac:(unfold QXEH.RMLOCK; lia) ltac:(unfold QXEH.RMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PLOCK_B]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RNEED_LOCKS PNL_B _ 1%nat ltac:(piece PNL_B) W2 eq_refl ltac:(unfold QXEH.RNEED_LOCKS; lia) ltac:(unfold QXEH.RNEED_LOCKS; lia) _ _); [|cbn; tauto].
cbn [sc_match PNL_B]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RPAGE_SIZE PPGSZ_B _ 8%nat ltac:(piece PPGSZ_B) W3 eq_refl ltac:(unfold QXEH.RPAGE_SIZE; lia) ltac:(unfold QXEH.RPAGE_SIZE; lia) _ _); [|cbn; tauto].
cbn [sc_match PPGSZ_B]. split; [reflexivity | exact I].
- refine (lit_rw QXEH.RGOT_SSP PGOTSSP_B _ 8%nat ltac:(piece PGOTSSP_B) W4 eq_refl ltac:(unfold QXEH.RGOT_SSP; lia) ltac:(unfold QXEH.RGOT_SSP; lia) _ _); [|cbn; tauto].
cbn [sc_match PGOTSSP_B]. split; [bytes_vm | exact I].
- refine (lit_rw QXEH.RSSP_GUARD PSSPG_B _ 8%nat ltac:(piece PSSPG_B) W5 eq_refl ltac:(unfold QXEH.RSSP_GUARD; lia) ltac:(unfold QXEH.RSSP_GUARD; lia) _ _); [|cbn; tauto].
cbn [sc_match PSSPG_B]. split; [rewrite HCAN; reflexivity | exact I].
- refine (lit_rw QXEH.RVMLOCK PVML_B _ 4%nat ltac:(piece PVML_B) W6 eq_refl ltac:(unfold QXEH.RVMLOCK; lia) ltac:(unfold QXEH.RVMLOCK; lia) _ _); [|cbn; tauto].
cbn [sc_match PVML_B]. split; [bytes_vm | exact I].
Qed.

Lemma lit_rw' : forall A cs tcs, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs tcs -> QbVh.cells_wf tcs ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> QlEo_c1.rw_cells JOB6SEGS m A tcs.
Proof.
intros A cs tcs C H0 H1 M WF W.
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A tcs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u64 : forall A cs ws, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs (map QbVh.C8 ws) ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u64arr JOB6SEGS m A ws.
Proof.
intros A cs ws C H0 H1 M W.
pose proof (check_u64arr JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A ws C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.
Lemma lit_u8 : forall A cs bs, cells_check JOB6SEGS (kn_view ch) (ELit 0) A cs = true ->
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 -> sc_match JOB6SEGS E A cs [QbVh.CB (length bs) bs] ->
QZDE.wr_at JOB6SEGS m A (Z.of_nat (scs_len cs)) -> Q5Rg.u8arr JOB6SEGS m A bs.
Proof.
intros A cs bs C H0 H1 M W.
pose proof (check_u8arr JOB6SEGS E m (kn_view ch) KV cs (ELit 0) A bs C) as X. cbv zeta in X.
change (bv_unsigned (edenot E (ELit 0))) with 0 in X. rewrite Z.add_0_l in X. apply X; assumption.
Qed.

Lemma ctx_wr : forall k l, 0 <= k -> 0 <= l -> k + l <= 928 -> QZDE.wr_at JOB6SEGS m (QXEH.RCTX + k) l.
Proof.
intros k l Hk Hl Hkl. destruct STATICS_w as (_ & _ & _ & _ & _ & _ & W).
exact (wr_at_sub JOB6SEGS m QXEH.RCTX 928 k l (img_w_b_sound JOB6SEGS 928 QXEH.RCTX m W ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; lia)) Hk Hl Hkl).
Qed.

Lemma ctx_B : QUZl.ctx ST0 = QEoy.ST0_B_ctx Q6q3.rc_secret.  Proof. reflexivity. Qed.
Ltac cellB :=
rewrite ?ctx_B, ?brk_word_B; cbn [QEoy.ST0_B_ctx QUZl.c_secret QUZl.c_free_meta_head QUZl.c_avail_meta QUZl.c_meta_area_head QUZl.c_meta_area_tail QUZl.c_avail_meta_areas];
lazymatch goal with
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 423)) _)) = _ =>
rewrite ed_mta by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B0; reflexivity
| |- word_to_le_bytes _ (edenot _ (EAlu _ (EMd _ _ (EVar 424)) _)) = _ =>
rewrite ed_grp by lia; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EMd _ _ (EVar 424))) = _ =>
rewrite ed_grp0; unfold QnDM_c1.Mq0.pw, QUZl.oconc; rewrite ?conc_B1; reflexivity
| |- word_to_le_bytes _ (edenot _ (EBlob _ _ _ _)) = _ => rewrite <- HSEC; reflexivity
| |- True => exact I
| |- _ = QbVh.cbytes (QbVh.C8 (QnDM_c1.Mq0.pw _ None)) => unfold QnDM_c1.Mq0.pw, QUZl.oconc; bytes_vm
| _ => bytes_vm
end.

Theorem rmrep_ctx_B : QCwx.Mq3.rmrep_ctx ST0 m.
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq3.rmrep_ctx. split; [|split; [|split; [|split; [|split; [|split]]]]].
- refine (lit_rw' QXEH.RCTX PHEAD_B _ ltac:(piece PHEAD_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_head_cells. cbv zeta. cbn [sc_match PHEAD_B]. repeat split; cellB.
+ cbn. tauto.
+ replace QXEH.RCTX with (QXEH.RCTX + 0) by lia. apply ctx_wr; cbn; lia.
- refine (lit_u64 (QXEH.RCTX + 80) PACT_B _ ltac:(piece PACT_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ rewrite actives_B. unfold ACT_O. cbn [sc_match PACT_B map]. repeat split; cellB.
+ apply ctx_wr; cbn; lia.
- refine (lit_u64 (QXEH.RCTX + 464) PUSE_B _ ltac:(piece PUSE_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ rewrite usages_B. unfold USE_Aw. cbn [sc_match PUSE_B map]. repeat split; cellB.
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QXEH.RCTX + 848) PUNM_B _ ltac:(piece PUNM_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ cbn [sc_match PUNM_B]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_u8 (QXEH.RCTX + 880) PBNC_B _ ltac:(piece PBNC_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _).
+ cbn [sc_match PBNC_B]. split; [bytes_vm | exact I].
+ apply ctx_wr; cbn; lia.
- refine (lit_rw' (QXEH.RCTX + 912) PTAIL_B _ ltac:(piece PTAIL_B) ltac:(unfold QXEH.RCTX; lia) ltac:(unfold QXEH.RCTX; cbn; lia) _ _ _).
+ unfold QnDM_c1.Mq0.ctx_tail_cells. cbn [sc_match PTAIL_B]. repeat split; cellB.
+ cbn. tauto.
+ apply ctx_wr; cbn; lia.
- reflexivity.
Qed.

Lemma u_pgM : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 423))) = MTA.
Proof. exact (proj1 (MV4 pge_meta)). Qed.
Lemma u_pgG : bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 4096) (EVar 424))) = GRP.
Proof. exact (proj1 (MV4 pge_grp)). Qed.
Lemma meta_wr : QZDE.wr_at JOB6SEGS m (MTA + 4096) 4096.
Proof. exact (proj2 (MV4 meta_bytes)). Qed.
Lemma grp_wr : QZDE.wr_at JOB6SEGS m GRP 4096.
Proof. exact (proj2 (MV4 grp_bytes)). Qed.

Lemma mta_piece_rw : forall off cs tcs, cells_check JOB6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) off cs = true ->
4096 <= off -> off + Z.of_nat (scs_len cs) <= 8192 -> sc_match JOB6SEGS E (MTA + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m (MTA + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct mta_bounds as [B1 B2].
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgM in X.
apply X; [lia | lia | exact M | exact WF |].
replace (MTA + off) with ((MTA + 4096) + (off - 4096)) by lia. apply (wr_at_sub JOB6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.
Lemma grp_piece_rw : forall off cs tcs, cells_check JOB6SEGS (kn_view ch) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) off cs = true ->
0 <= off -> off + Z.of_nat (scs_len cs) <= 4096 -> sc_match JOB6SEGS E (GRP + off) cs tcs -> QbVh.cells_wf tcs ->
QlEo_c1.rw_cells JOB6SEGS m (GRP + off) tcs.
Proof.
intros off cs tcs C H0 H1 M WF. destruct grp_bounds as [B1 B2].
pose proof (check_rw_cells JOB6SEGS E m (kn_view ch) KV cs _ off tcs C) as X. cbv zeta in X. rewrite u_pgG in X.
apply X; [lia | lia | exact M | exact WF |].
apply (wr_at_sub JOB6SEGS m GRP 4096); [exact grp_wr | lia | lia | lia].
Qed.

Lemma meta_zero_run : QZDE.bytes_at JOB6SEGS m (MTA + 4280) (repeat (Z_to_bv 8 0) 3912) /\ QZDE.wr_at JOB6SEGS m (MTA + 4280) (Z.of_nat 3912).
Proof.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct mta_bounds as [B1 B2]. split.
- pose proof (cells_check_sound JOB6SEGS E m (kn_view ch) KV PMZERO_B _ 4280 ltac:(piece PMZERO_B)) as X. cbv zeta in X. rewrite u_pgM in X.
specialize (X ltac:(lia) ltac:(cbn; lia)). cbn [sc_bytes PMZERO_B] in X. rewrite app_nil_r in X. exact X.
- replace (MTA + 4280) with ((MTA + 4096) + 184) by lia. apply (wr_at_sub JOB6SEGS m (MTA + 4096) 4096); [exact meta_wr | lia | lia | lia].
Qed.

Theorem rmrep_areas_B : QCwx.Mq3.rmrep_areas ST0 m.
Proof.
intros a ar Ha. apply areas_B_inv in Ha as [-> ->].
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
destruct meta_zero_run as [ZB ZW].
unfold QCwx.Mq3.rarea_rep. rewrite conc_B0. cbn [QUZl.a_check QUZl.a_next QUZl.a_nslots]. split; [|split].
- refine (mta_piece_rw 4096 PMHDR_B _ ltac:(piece PMHDR_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PMHDR_B]. repeat split; cellB.
- intros k Hk. unfold QUZl.NSLOTS in Hk. unfold QUZl.aadd, QUZl.AREA_HDR, QUZl.META_SIZE. cbn [fst snd].
assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ 4 <= k) by lia. destruct K as [->|[->|[->|[->|K]]]].
+ change (4096 + (24 + 40 * 0)) with 4120. rewrite meta_B_0. replace (MTA + 4096 + 24 + 40 * 0) with (MTA + 4120) by lia.
refine (mta_piece_rw 4120 PM0_B _ ltac:(piece PM0_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM0_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 1)) with 4160. rewrite meta_B_1. replace (MTA + 4096 + 24 + 40 * 1) with (MTA + 4160) by lia.
refine (mta_piece_rw 4160 PM1_B _ ltac:(piece PM1_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM1_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 2)) with 4200. rewrite meta_B_2. replace (MTA + 4096 + 24 + 40 * 2) with (MTA + 4200) by lia.
refine (mta_piece_rw 4200 PM2_B _ ltac:(piece PM2_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM2_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ change (4096 + (24 + 40 * 3)) with 4240. rewrite meta_B_3. replace (MTA + 4096 + 24 + 40 * 3) with (MTA + 4240) by lia.
refine (mta_piece_rw 4240 PM3_B _ ltac:(piece PM3_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
unfold QnDM_c1.Mq0.meta_cells. cbn [sc_match PM3_B QUZl.m_prev QUZl.m_next QUZl.m_mem QUZl.m_avail QUZl.m_freed]. repeat split; cellB.
+ replace (4096 + (24 + 40 * k)) with (4120 + 40 * k) by lia. rewrite (meta_B_none _ _ _ _ k K).
replace (MTA + 4096 + 24 + 40 * k) with (MTA + 4280 + Z.of_nat (Z.to_nat (40 * (k - 4)))) by lia.
apply (zero_cells JOB6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; tauto | rewrite meta0_bytes; reflexivity | cbn [QbVh.cells_size QnDM_c1.Mq0.meta_cells QbVh.csize]; lia].
- replace (MTA + 4096 + 4064) with (MTA + 4280 + Z.of_nat 3880) by lia.
apply (zero_cells JOB6SEGS m (MTA + 4280) 3912 _ _ ZB ZW); [cbn; split; [reflexivity | exact I] | bytes_vm | cbn; lia].
Qed.

Theorem rmrep_groups_B : QCwx.Mq3.rmrep_groups ST0 m.
Proof.
intros p gh Hp. apply groups_B_inv in Hp.
pose proof (PIECES_B ch HCL) as PC. unfold pieces_check_B in PC. do 21 (apply andb_prop in PC as [PC ?]).
unfold QCwx.Mq3.rgroup_rep. destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite conc_B1; cbn [QUZl.g_meta QUZl.g_active_idx].
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 0 PG0_B _ ltac:(piece PG0_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG0_B]. repeat split; cellB.
- exists (Z_to_bv 8 9). split; [|reflexivity].
refine (grp_piece_rw 48 PG3_B _ ltac:(piece PG3_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG3_B]. repeat split; cellB.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 32 PG2_B _ ltac:(piece PG2_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG2_B]. repeat split; cellB.
- exists (Z_to_bv 8 1). split; [|reflexivity].
refine (grp_piece_rw 16 PG1_B _ ltac:(piece PG1_B) ltac:(lia) ltac:(cbn; lia) _ _); [|cbn; tauto].
cbn [sc_match PG1_B]. repeat split; cellB.
Qed.

Theorem rmrep_shadow_B : QCwx.Mq3.rmrep_shadow ST0 m.
Proof.
intros rid r Hr Hk. apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; [|discriminate Hk].
unfold QCwx.Mq3.rshadow_rep. cbn [QUZl.r_base QUZl.r_len]. change (QUZl.round_up_pg 4096) with 4096. split; [exact grp_wr|].
intros o v Ho Hc. rewrite shadow_B1 in Hc.
destruct (shadow_B_lit o v Ho Hc) as [SL V]. split; [|exact V].
pose proof (sc_lit_byte_sound JOB6SEGS E GRP_B GRP (Z.to_nat o) v SL) as NTH.
pose proof (bytes_at_nth JOB6SEGS m GRP _ (Z.to_nat o) _ (proj1 (MV4 grp_bytes)) NTH) as B.
rewrite Z2Nat.id in B by lia. exact B.
Qed.

#[local] Notation M1 L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo false ch HCL CS) (only parsing).
Lemma obj_facts : forall o, In o (OBJS_W false) ->
(4096 * bv_unsigned (ev E (fst o)) + snd o <= 0x10000 \/ 0x647000 <= 4096 * bv_unsigned (ev E (fst o)))
/\ 4096 * bv_unsigned (ev E (fst o)) + snd o <= atopE E.
Proof.
intros o Ho. pose proof (M1 in_maps_obj o Ho) as Hin. pose proof (M1 u_obj_base o Ho) as UB. pose proof (M1 u_obj_len o Ho) as UL.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ CS) as B. rewrite Forall_forall in B. destruct (B _ Hin) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi BJO6] in B4. rewrite UB, UL in B4.
pose proof (M1 maps_below_atop _ Hin) as T. rewrite UB, UL, <- (M1 main_atop) in T. split; [exact B4 | exact T].
Qed.
Lemma mta_facts : (MTA + 8192 <= 0x10000 \/ 0x647000 <= MTA) /\ MTA + 8192 <= atopE E.
Proof. exact (obj_facts (423%nat, 8192) ltac:(cbn; tauto)). Qed.
Lemma grp_facts : (GRP + 4096 <= 0x10000 \/ 0x647000 <= GRP) /\ GRP + 4096 <= atopE E.
Proof. exact (obj_facts (424%nat, 4096) ltac:(cbn; tauto)). Qed.
Lemma mta_grp_disj : GRP + 4096 <= MTA \/ MTA + 8192 <= GRP.
Proof.
assert (IM : In (423%nat, 8192) (OBJS_W false)) by (cbn; tauto). assert (IG : In (424%nat, 4096) (OBJS_W false)) by (cbn; tauto).
assert (NE : obj_e E (424%nat, 4096) <> obj_e E (423%nat, 8192)).
{ intros X. apply (M1 obj_e_inj _ _ IG IM) in X. discriminate X. }
pose proof (M1 maps_disj _ _ (M1 in_maps_obj _ IG) (M1 in_maps_obj _ IM) NE) as D. unfold iv_disjoint in D.
rewrite !(M1 u_obj_base _ IM), !(M1 u_obj_base _ IG), !(M1 u_obj_len _ IM), !(M1 u_obj_len _ IG) in D. cbn [fst snd] in D. exact D.
Qed.

Theorem rregions_wf_B : QCwx.Mq3.rregions_wf ST0.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
unfold QCwx.Mq3.rregions_wf. split; [reflexivity|]. split; [|split; [|split]].
- intros rid r Hr. apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; cbn [QUZl.r_base QUZl.r_len];
[change (QUZl.round_up_pg 4096) with 4096 | change (QUZl.round_up_pg 8192) with 8192]; unfold Q6q3.alloc_ceiling; rewrite HCEIL;
(split; [lia|]; split; [assumption|]; split; [lia|]; split; [lia|]; apply hull_apart_free; assumption).
- intros rid1 r1 rid2 r2 H1 H2 NE. apply regions_B_inv in H1 as [[-> ->]|[-> ->]]; apply regions_B_inv in H2 as [[-> ->]|[-> ->]]; try congruence;
unfold QnDM_c1.Mq0.lr_lo; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]; change (QUZl.round_up_pg 4096) with 4096; change (QUZl.round_up_pg 8192) with 8192; lia.
- intros a ar Ha. apply areas_B_inv in Ha as [-> ->]. exists (QUZl.mkRegion QUZl.RKMeta MTA 8192). cbn [fst snd]. rewrite region_B0.
unfold QnDM_c1.Mq0.lr_lo. cbn [QUZl.r_base QUZl.r_len QUZl.r_kind]. change (QUZl.round_up_pg 8192) with 8192.
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [discriminate | lia].
- intros p gh Hp. apply groups_B_inv in Hp. exists (QUZl.mkRegion QUZl.RKGroup GRP 4096).
destruct Hp as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [fst snd]; rewrite region_B1; cbn [QUZl.r_base QUZl.r_len QUZl.r_kind];
change (QUZl.round_up_pg 4096) with 4096; (split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [lia | reflexivity]).
Qed.

Theorem rmrep_main_B : QCwx.Mq3.rmrep ST0 m.
Proof. exact (conj rregions_wf_B (conj rmrep_ctx_B (conj rmrep_globals_B (conj rmrep_areas_B (conj rmrep_groups_B rmrep_shadow_B))))). Qed.

Lemma answers_B : QUZl.brk0_answer_ok 4096 = true /\ QUZl.mmap_answer_ok (QXEH.ref_reserved ++ []) (2 * QUZl.PGSZ) MTA = true /\ QUZl.is_err MTA = false
/\ QUZl.mmap_answer_ok (QXEH.ref_reserved ++ [(MTA, 8192)]) 4096 GRP = true /\ QUZl.is_err GRP = false.
Proof.
destruct mta_bounds as [B1 B2]. destruct grp_bounds as [G1 G2]. destruct mta_facts as [BH BT]. destruct grp_facts as [GH GT]. pose proof mta_grp_disj as D.
assert (AM : MTA mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (AG : GRP mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
split; [reflexivity|]. split; [|split; [|split]].
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg (2 * 4096)) with 8192. rewrite AM. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. rewrite app_nil_r. rewrite (hull_apart_free _ _ BH).
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
- unfold QUZl.mmap_answer_ok, QUZl.PGSZ. change (QUZl.round_up_pg 4096) with 4096. rewrite AG. apply orb_true_iff. right.
unfold Q6q3.alloc_ceiling. rewrite HCEIL. unfold QUZl.ranges_free. rewrite forallb_app. fold (QUZl.ranges_free QXEH.ref_reserved GRP 4096). rewrite (hull_apart_free _ _ GH).
cbn [forallb fst snd]. unfold QUZl.iv_disjoint.
repeat (apply andb_true_intro; split); try reflexivity; [apply Z.ltb_lt; lia | apply Z.leb_le; lia | apply orb_true_iff; destruct D; [left | right]; apply Z.leb_le; lia].
- unfold QUZl.is_err, QUZl.TWO64. apply Z.ltb_ge. lia.
Qed.

Theorem RHEAP_main_B : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 ->
QkLq.Mq4.RHEAP s [QnPO.Mq2.BLK0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP] m.
Proof.
intros s Hm. destruct answers_B as (A1 & A2 & A3 & A4 & A5).
exists ST0, [QnPO.Mq2.BLK0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact rmrep_main_B|]. split.
- apply QnPO.Mq2.brk_link_main_B.
- exact (QnPO.Mq2.areach_main_B Q6q3.rc_secret QXEH.ref_reserved 4096 MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5).
Qed.

Theorem mng_main_B : forall s : QGeV.PState, QGeV.ps_m s = QUZl.strip ST0 ->
exists Lg0 : Qfya.mled,
QkLq.Mq4.RHEAP s [QnPO.Mq2.BLK0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP] m
/\ Q9kF.HSIM s Lg0 [QnPO.Mq2.BLK0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP]
/\ Qfya.ld_live Lg0 = [(1%N, 64)] /\ Qfya.ld_resv Lg0 = QXEH.ref_reserved /\ Qfya.ld_groups Lg0 = [(GRP, 4096)]
/\ Qfya.ld_metas Lg0 = [(MTA, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None.
Proof.
intros s Hm. destruct answers_B as (A1 & A2 & A3 & A4 & A5).
pose proof (QnPO.Mq2.areach_main_B Q6q3.rc_secret QXEH.ref_reserved 4096 MTA GRP Q6q3.rc_secret_range A1 A2 A3 A4 A5) as AR.
destruct (Q3o5.Mq1.areach_inv QXEH.ref_reserved ST0 _ AR) as (L & LS & BL & INV & LIVE & RESV & _ & CR).
pose proof INV as IR. unfold Qatc.INVL in IR. cbv zeta in IR. destruct IR as [IR _].
exists L. split; [exact (RHEAP_main_B s Hm)|]. split.
- exists ST0, BL, LS, [QnPO.Mq2.BLK0_B Q6q3.rc_secret QXEH.ref_reserved MTA GRP].
split; [apply Permutation.Permutation_refl|]. split; [symmetry; exact Hm|]. split; [exact INV | exact CR].
- split; [rewrite LIVE, <- (Q9kF.CORR_slots _ _ _ CR); reflexivity|]. split; [exact RESV|]. split; [|split].
+ pose proof (Qatc.ir_groups _ _ _ IR) as PG. rewrite groups_of_B in PG. apply Permutation.Permutation_sym in PG.
exact (Permutation.Permutation_length_1_inv PG).
+ pose proof (Qatc.ir_metas _ _ _ IR) as PM. rewrite metas_of_B in PM. apply Permutation.Permutation_sym in PM.
exact (Permutation.Permutation_length_1_inv PM).
+ destruct (Qfya.ld_brkreg L) as [[bb ll]|] eqn:EB; [|reflexivity]. exfalso.
apply (Qatc.ir_brkreg _ _ _ IR) in EB as (rid & r & Hr & Hk & _). apply regions_B_inv in Hr as [[-> ->]|[-> ->]]; discriminate Hk.
Qed.
End RmrepB.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvQl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvQl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8BV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8BV.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Lemma DRV_CHECKS : forall w ch, HSCLASS_S w ch ->
drv_pieces_check (kn_view ch) = true
/\ img_ranges (kn_view ch) (Q2y2.PRIS_A ++ Q2y2.STDIO0_A) = true
/\ img_range (kn_view ch) 0x10000 0xe2000 = true
/\ kn_mem (KRange (EVar 44) 1 4194303) (kn_view ch) = true
/\ a_fd ch = FdStd.
Proof.

intros [|] ch [-> | ->].
- split; [exact DRVPIECES_HS2sA_1_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sA_2_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sB_3_ok|]. repeat split; vm_compute; reflexivity.
- split; [exact DRVPIECES_HS2sB_4_ok|]. repeat split; vm_compute; reflexivity.
Qed.

Lemma seg_w : seg_writable Asan.Asan_segment_002 = true
/\ seg_writable Asan.Asan_segment_003 = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma ro_addr_range : forall a : word, QZDE.ro_addr JO6SEGS a = true -> 0x10000 <= bv_unsigned a < 0xe2000.
Proof.

intros a H. unfold QZDE.ro_addr in H. destruct seg_w as [W2 W3].
unfold JO6SEGS, Asan.M.loaded_segments, Asan.Asan_loaded_segments in H. cbn [find_segment] in H.
replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x2d000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x3d000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0xa5000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0xe2000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x5000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0xe7000 in H by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55e000 in H by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0x10000 + 0x2d000)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 0x3d000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0x3d000 + 0xa5000)); cbn [andb] in H; try lia.
all: destruct (Z.leb_spec0 0xe2000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0xe2000 + 0x5000)); cbn [andb] in H;
try (exfalso; rewrite W2 in H; discriminate H).
all: destruct (Z.leb_spec0 0xe7000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) (0xe7000 + 0x55e000)); cbn [andb] in H;
try (exfalso; rewrite W3 in H; discriminate H); try discriminate H.
Qed.

Lemma DRV_w : img_w_b JO6SEGS (Qwm6.Mq0.A_TP - 48) 8 = true /\ img_w_b JO6SEGS Qirj.Mq0.ATEXIT_A 304 = true.
Proof. split; vm_compute; reflexivity. Qed.

Section DrvPre.
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
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation m := (view LV mo FULL).
#[local] Notation KV := (MV4 main_know_view).

Theorem drv_pristine : Q2y2.pris_A m /\ Q2y2.stdio0 m.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & IR & _).
pose proof (img_ranges_sound JO6SEGS E m (kn_view ch) KV _ IR) as F. apply Forall_app in F as [F1 F2].
split; [unfold Q2y2.pris_A | unfold Q2y2.stdio0]; (eapply Forall_impl; [| eassumption]); intros iv H a Ha; exact (H a Ha).
Qed.

Theorem drv_mem_inv : QZDE.mem_inv JO6SEGS m.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & _ & IR & _).
exact (mem_inv_of_img JO6SEGS E m (kn_view ch) KV 0x10000 0xe2000 IR ro_addr_range).
Qed.

Theorem drv_tid : exists tid, QlEo_c1.ro_cells JO6SEGS m (Qwm6.Mq0.A_TP - 168) [QbVh.C4 (Z_to_bv 64 tid)] /\ 0 < tid < 2^31.
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _ & _ & KR & _). unfold drv_pieces_check in C.
apply andb_prop in C as [C _]. apply andb_prop in C as [C _].
pose proof (proj1 (Forall_forall _ _) KV _ (kn_mem_In _ _ KR)) as RG. cbn [kentry_ok edenot] in RG.
exists (bv_unsigned (ev E 44)). split; [| lia].
refine (proj1 (check_cells_at JO6SEGS E m (kn_view ch) KV DTID (ELit 0) _ [QbVh.C4 (Z_to_bv 64 (bv_unsigned (ev E 44)))] C _ _ _ _)).
- change (bv_unsigned (edenot E (ELit 0))) with 0. unfold Qwm6.Mq0.A_TP. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- cbn [sc_match DTID]. split; [| exact I]. cbn [edenot QbVh.cbytes]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. tauto.
Qed.

Theorem drv_loc : QlEo_c1.rw_cells JO6SEGS m Q2y2.T_LOCCELL_A [QbVh.C8 (Z_to_bv 64 Q2y2.T_GLOBLOC_A)].
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _). unfold drv_pieces_check in C.
apply andb_prop in C as [C _]. apply andb_prop in C as [_ C]. destruct DRV_w as [W _].
refine (check_rw_cells JO6SEGS E m (kn_view ch) KV DLOC (ELit 0) _ _ C _ _ _ _ _).
- change (bv_unsigned (edenot E (ELit 0))) with 0. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- cbn [sc_match DLOC]. split; [reflexivity | exact I].
- cbn. tauto.
- change (bv_unsigned (edenot E (ELit 0))) with 0. exact (img_w_b_sound JO6SEGS 8 _ m W ltac:(unfold Qwm6.Mq0.A_TP; lia) ltac:(unfold Qwm6.Mq0.A_TP; cbn; lia)).
Qed.

Theorem drv_atexit : exists mid, QlEo_c1.rw_cells JO6SEGS m Qirj.Mq0.ATEXIT_A (Qirj.Mq0.atexit_cells m mid) /\ length mid = 240%nat.
Proof.
destruct (DRV_CHECKS w ch HCL) as (C & _). unfold drv_pieces_check in C. apply andb_prop in C as [_ C]. destruct DRV_w as [_ W].
assert (PH : Qirj.Mq0.ax_phase m = 1).
{ unfold Qirj.Mq0.ax_phase. destruct drv_pristine as [_ S0]. unfold Q2y2.stdio0, Q2y2.STDIO0_A in S0.
pose proof (proj1 (Forall_forall _ _) S0 (Qirj.Mq0.ADFLAG_A, Qirj.Mq0.ADFLAG_A + 48) ltac:(unfold Qirj.Mq0.ADFLAG_A; cbn; tauto)) as PAD. cbn [fst snd] in PAD.
replace (m (Z_to_bv 64 Qirj.Mq0.ADFLAG_A)) with (@None (bv 8)) by (symmetry; exact (PAD Qirj.Mq0.ADFLAG_A ltac:(unfold Qirj.Mq0.ADFLAG_A; lia))). reflexivity. }
exists (rom_bytes JO6SEGS (Qirj.Mq0.ATEXIT_A + 48) 240). split; [| apply rom_bytes_length].
unfold Qirj.Mq0.atexit_cells. rewrite PH.
refine (check_rw_cells JO6SEGS E m (kn_view ch) KV DATEXIT (ELit 0) _ _ C _ _ _ _ _).
- change (bv_unsigned (edenot E (ELit 0))) with 0. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn. lia.
- change (bv_unsigned (edenot E (ELit 0))) with 0. cbn [sc_match DATEXIT Qirj.Mq0.atexit_cellsK].
repeat split; vm_compute; reflexivity.
- unfold Qirj.Mq0.atexit_cellsK. cbn [QbVh.cells_wf QbVh.cell_wf]. rewrite rom_bytes_length. repeat split; reflexivity.
- change (bv_unsigned (edenot E (ELit 0))) with 0. exact (img_w_b_sound JO6SEGS 304 _ m W ltac:(unfold Qirj.Mq0.ATEXIT_A; lia) ltac:(unfold Qirj.Mq0.ATEXIT_A; cbn; lia)).
Qed.

Theorem drv_fds : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))
/\ alloc_fd (m_fds mo) = Z_to_bv 64 3 /\ fd_lookup (m_fds mo) (Z_to_bv 64 3) = None.
Proof.
destruct (DRV_CHECKS w ch HCL) as (_ & _ & _ & _ & FD). pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ _ CS) as F.
unfold fds_ok in F. rewrite FD in F. rewrite F. repeat split; vm_compute; reflexivity.
Qed.
End DrvPre.
