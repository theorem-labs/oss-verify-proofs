(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFeq AFgi AFex.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFfv AFga AFgc AFge AFfy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Lemma le_byte_lt : forall v (w k : nat), 0 <= YG0f.le_byte v w k < 256.
Proof. intros v w k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma aview_vis_byte : forall H mem a, aview tfibsegs H mem a <> None ->
exists b, aview tfibsegs H mem a = Some b /\ 0 <= b < 256 /\ mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 b).
Proof.
intros H mem a Hv. destruct (aview tfibsegs H mem a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exists b. split; [reflexivity|]. pose proof E as E'. apply aview_some in E as (b8 & Hb & <-).
pose proof (bv_unsigned_in_range 8 b8) as R. change (bv_modulus 8) with 256 in R. split; [lia|]. exact (aview_byte _ _ _ _ E').
Qed.
Lemma vis_word : forall H mem a, (forall i, 0 <= i < 8 -> aview tfibsegs H mem (a + i) <> None) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 w /\ rdword (aview tfibsegs H mem) a = Some w.
Proof.
intros H mem a Hv.
destruct (aview_vis_byte H mem (a + 0) (Hv 0 ltac:(lia))) as (b0 & E0 & R0 & M0).
destruct (aview_vis_byte H mem (a + 1) (Hv 1 ltac:(lia))) as (b1 & E1 & R1 & M1).
destruct (aview_vis_byte H mem (a + 2) (Hv 2 ltac:(lia))) as (b2 & E2 & R2 & M2).
destruct (aview_vis_byte H mem (a + 3) (Hv 3 ltac:(lia))) as (b3 & E3 & R3 & M3).
destruct (aview_vis_byte H mem (a + 4) (Hv 4 ltac:(lia))) as (b4 & E4 & R4 & M4).
destruct (aview_vis_byte H mem (a + 5) (Hv 5 ltac:(lia))) as (b5 & E5 & R5 & M5).
destruct (aview_vis_byte H mem (a + 6) (Hv 6 ltac:(lia))) as (b6 & E6 & R6 & M6).
destruct (aview_vis_byte H mem (a + 7) (Hv 7 ltac:(lia))) as (b7 & E7 & R7 & M7).
set (w := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))).
exists w. split; [subst w; lia|]. split.
- assert (LB : forall k, (k < 8)%nat -> YO0f.le_byte w 8 k = nth k [b0; b1; b2; b3; b4; b5; b6; b7] 0).
{ intros k Hk. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small w (2 ^ 64)) by (subst w; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
[ change (2 ^ (8 * 0)) with 1 | change (2 ^ (8 * 1)) with 256 | change (2 ^ (8 * 2)) with 65536 | change (2 ^ (8 * 3)) with 16777216
| change (2 ^ (8 * 4)) with 4294967296 | change (2 ^ (8 * 5)) with 1099511627776 | change (2 ^ (8 * 6)) with 281474976710656
| change (2 ^ (8 * 7)) with 72057594037927936 ]; subst w; Z.div_mod_to_equations; nia. }
intros k Hk. rewrite (LB k Hk). rewrite Z.add_0_r in M0.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; assumption.
- unfold rdword. rewrite Z.add_0_r in E0. rewrite E0, E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.
Lemma vis_writable : forall H mem a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hv. destruct (aview_vis_byte H mem a Hv) as (b & _ & _ & M). exact (mbyte_high_writable _ a _ Ha M).
Qed.
Lemma vis_writable_off : forall H mem a, off_img a -> aview tfibsegs H mem a <> None -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hv. destruct (aview_vis_byte H mem a Hv) as (b & _ & _ & M). exact (mbyte_off_writable _ a _ Ha M).
Qed.
Lemma vis_apresent : forall H mem a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. destruct (aview_vis_byte H mem a Hv) as (b & _ & _ & M). exact (mbyte_high_apresent H mem a _ Ha M).
Qed.
Lemma vis_apresent_off : forall H mem a, off_img a -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. destruct (aview_vis_byte H mem a Hv) as (b & _ & _ & M). exact (mbyte_off_apresent H mem a _ Ha M).
Qed.
Lemma val_mem_vis : forall H mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.
Section h.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x52a6c regs ch.
Let sp0 : Z := bv_unsigned (getr regs 2).
Let pa : Z := sptr_addr B ly p.
Let nn : Z := req_size n.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Variables (lastb : batch) (initr : list batch).
Hypothesis ARM : rev (qc_list (st_qthread S)) = lastb :: initr /\ Z.of_nat (length (b_items lastb)) < kBatchSlots /\
qc_bytes (st_qthread S) + nn <= kQuarantineCacheMax.
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread S).
Lemma M : ARm B ly S rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Definition kk : chunk := match find_user (st_chunks S) p with Some k => k | None => mkChunk PNull 0 CAllocated end.
Lemma kk_facts : find_user (st_chunks S) p = Some kk /\ In kk (st_chunks S) /\ ck_state kk = CAllocated /\ ck_user kk = p /\ ck_req kk = n.
Proof.
pose proof (find_user_block _ 0 0 0 S p n WF HBLK) as (k & Hf & Hk & Hst & Hu & Hr). unfold kk. rewrite Hf. auto.
Qed.
Lemma KF : cfacts B ly S kk. Proof. exact (chunk_facts B ly S rd0 kk M (proj1 (proj2 kk_facts))). Qed.
Lemma Epa : pa = ck_base B ly kk + ck_rz kk.
Proof. pose proof KF as (_ & _ & _ & G4 & _). pose proof kk_facts as (_ & _ & _ & Hu & _). unfold pa. rewrite <- Hu. exact G4. Qed.
Lemma Enn : nn = ck_n kk.
Proof. pose proof kk_facts as (_ & _ & _ & _ & Hr). unfold nn, ck_n. rewrite Hr. reflexivity. Qed.
Definition hb1 : Z := match rd0 (pa - 15) with Some b => b | None => 0 end.
Definition jw (a : Z) : Z := match rdword rd0 a with Some w => w | None => 0 end.
Definition j1 : Z := jw (T + t_stats + 24).
Definition j2 : Z := jw (T + t_stats + 32).
Definition j3 : Z := jw pa.
Local Notation E0 := (AFgi.E0 ly regs ch pa nn hb1 q lastb j1 j2 j3).
Local Notation LENv := (AFgi.LENv ly regs ch).
Local Notation IMv := (AFgi.IMv pa).
Local Notation HWv := (AFgi.HWv hb1).
Local Notation SPv := (AFgi.SPv pa).
Local Notation N8v := (AFgi.N8v nn).
Local Notation CNT8v := (AFgi.CNT8v nn).
Local Notation Bv := (AFgi.Bv ly lastb).
Local Notation BBv := (AFgi.BBv lastb).
Local Notation BCv := (AFgi.BCv lastb).
Local Notation SLOTv := (AFgi.SLOTv ly lastb).
Local Notation QSv := (AFgi.QSv q).
Local Notation QFv := (AFgi.QFv ly q).
Local Notation QBv := (AFgi.QBv q).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (tfib_const_lookup_sym B TB ly S H0 mem e w e' M E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (tfib_const_lookup B TB ly S H0 mem a w x M E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells B ly S) -> c = ACell e w (AV e') -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. apply (cell_holds_val_mem B ly H0 mem e w e'). exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) \/ In (e, len) (aclient S) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 M) _ Hin i Hi).
- exact (proj1 (Forall_forall _ _) (am_client B ly S rd0 M) _ Hin i Hi).
Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.
Lemma junk_vals : val_mem tfibsegs m0 (T + t_stats + 24) 8 j1 /\ 0 <= j1 < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_stats + 32) 8 j2 /\ 0 <= j2 < 2 ^ 64.
Proof.
assert (V : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> val_mem tfibsegs m0 a 8 (jw a) /\ 0 <= jw a < 2 ^ 64).
{ intros a H1 H2. destruct (vis_word H0 mem a) as (w & Rw & Vw & Ew).
- intros i Hi. replace (a + i) with (aeval B ly (AT t_stats) + (a + i - (T + t_stats))) by (cbn; lia).
apply (vis_range (AT t_stats) (t_unwinding - t_stats)); [left; apply in_thread_junk; unfold thread_junk; cbn; tauto | lia].
- unfold jw. rewrite Ew. auto. }
unfold j1, j2. pose proof (V (T + t_stats + 24)) as [A1 A2]; [unfold t_stats, t_unwinding; lia | unfold t_stats, t_unwinding; lia|].
pose proof (V (T + t_stats + 32)) as [A3 A4]; [unfold t_stats, t_unwinding; lia | unfold t_stats, t_unwinding; lia|]. auto.
Qed.
Lemma hdr_In : forall c, In c (chunk_cells kk) -> In c (acells B ly S).
Proof. intros c Hc. unfold acells. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists kk. split; [exact (proj1 (proj2 kk_facts)) | exact Hc]. Qed.
Lemma hb1_facts : rd0 (pa - 15) = Some hb1 /\ 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Proof.
pose proof kk_facts as (_ & Hk & Hst & _).
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M)). apply hdr_In. unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite (AFex.EA2 B ly S rd0 M lastb kk _ _ Hk) in C. unfold kChunkHeaderSize in C.
replace (ck_base B ly kk + (ck_rz kk - 16) + 1) with (pa - 15) in C by (rewrite Epa; lia).
destruct C as (b & Hb & Hm). unfold hb1. rewrite Hb. destruct (aview_vis_byte H0 mem (pa - 15) ltac:(rewrite Hb; discriminate)) as (b' & E' & R' & _).
rewrite Hb in E'. injection E' as <-. auto.
Qed.
Lemma hw_val : val_mem tfibsegs m0 (pa - 16) 4 HWv /\ val_mem tfibsegs m0 (pa - 12) 4 nn.
Proof.
pose proof kk_facts as (_ & Hk & Hst & _). pose proof hb1_facts as (HB & HR & _).
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) = pa - 16).
{ rewrite (AFex.EA B ly S rd0 M lastb kk _ Hk). rewrite Epa. unfold kChunkHeaderSize. lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) d) = pa - 16 + d).
{ intros d. rewrite (AFex.EA2 B ly S rd0 M lastb kk _ _ Hk). rewrite Epa. unfold kChunkHeaderSize. lia. }
assert (V0 : val_mem tfibsegs m0 (pa - 16) 1 2).
{ rewrite <- EH. eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; left; reflexivity|]. unfold z1, c1, hdr_state. rewrite Hst. reflexivity. }
assert (V2 : val_mem tfibsegs m0 (pa - 14) 2 0).
{ replace (pa - 14) with (pa - 16 + 2) by lia. rewrite <- (EH2 2). eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; do 2 right; left; reflexivity|]. reflexivity. }
assert (V4 : val_mem tfibsegs m0 (pa - 12) 4 (ck_n kk)).
{ replace (pa - 12) with (pa - 16 + 4) by lia. rewrite <- (EH2 4). eapply cell_stateZ; [apply hdr_In; unfold chunk_cells; apply in_app_iff; left; do 3 right; left; reflexivity|]. reflexivity. }
split; [|rewrite Enn; exact V4].
intros i Hi. unfold AFgi.HWv.
assert (LB : forall v (w j : nat), YO0f.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
destruct i as [|[|[|[|i]]]]; [| | | |lia].
- rewrite (V0 0%nat ltac:(lia)). do 2 f_equal. rewrite !LB. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- change (Z.of_nat 1) with 1. replace (pa - 16 + 1) with (pa - 15) by lia. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 2) with (pa - 14 + Z.of_nat 0) by lia. rewrite (V2 0%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 3) with (pa - 14 + Z.of_nat 1) by lia. rewrite (V2 1%nat ltac:(lia)). do 2 f_equal.
rewrite !LB. change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia.
Qed.
Lemma Hrev : rev (qc_list q) = lastb :: initr. Proof. exact (proj1 ARM). Qed.
Lemma Hroom : BCv < kBatchSlots. Proof. exact (proj1 (proj2 ARM)). Qed.
Lemma qlist0 : qc_list q = rev initr ++ [lastb]. Proof. rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity. Qed.
Lemma lastb_in : In lastb (all_batches S). Proof. unfold all_batches. rewrite qlist0, !in_app_iff. left. right. left. reflexivity. Qed.
Lemma quar_In : forall c, In c (quar_cells S) -> In c (acells B ly S).
Proof. intros c Hc. unfold acells. rewrite !in_app_iff. do 4 right. left. exact Hc. Qed.
Lemma qc_vals : val_mem tfibsegs m0 (T + t_qc) 8 QSv /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 QFv /\
val_mem tfibsegs m0 (T + t_qc + 16) 8 Bv /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 QBv.
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) q) -> In c (acells B ly S)).
{ intros c Hc. apply quar_In. unfold quar_cells. right. right. apply in_app_iff. left. exact Hc. }
unfold qc_cells in IN. splits.
- replace (T + t_qc) with (aeval B ly (AT t_qc)) by reflexivity. eapply cell_stateZ; [apply IN; left; reflexivity | reflexivity].
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
replace QFv with (aeval B ly (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end)) by (unfold AFgi.QFv; destruct (qc_list q); reflexivity).
eapply cell_state; [apply IN; right; left; reflexivity | reflexivity].
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
replace Bv with (aeval B ly (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end)) by (rewrite Hrev; reflexivity).
eapply cell_state; [apply IN; do 2 right; left; reflexivity | reflexivity].
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia). eapply cell_stateZ; [apply IN; do 3 right; left; reflexivity | reflexivity].
Qed.
Lemma batch_vals : val_mem tfibsegs m0 (Bv + 8) 8 BBv /\ val_mem tfibsegs m0 (Bv + 16) 8 BCv.
Proof.
destruct (batch_cells_snoc (rev initr) lastb lastb eq_refl) as (P & EP & _ & _).
assert (IN : forall c, In c (batch_cells [lastb]) -> In c (acells B ly S)).
{ intros c Hc. apply quar_In. unfold quar_cells. right. right. apply in_app_iff. left. unfold qc_cells. do 4 right. rewrite qlist0, EP. apply in_app_iff. right. exact Hc. }
cbn [batch_cells app] in IN. split.
- replace (Bv + 8) with (aeval B ly (aoff (batch_exp lastb) 8)) by (cbn; unfold AFgi.Bv; lia). eapply cell_stateZ; [apply IN; right; left; reflexivity | reflexivity].
- replace (Bv + 16) with (aeval B ly (aoff (batch_exp lastb) 16)) by (cbn; unfold AFgi.Bv; lia). eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
Qed.
Lemma slot_vis : forall a, SLOTv <= a < SLOTv + 8 -> rd0 a <> None.
Proof.
intros a Ha. pose proof Hroom as HR. unfold AFgi.SLOTv, AFgi.Bv, AFgi.BCv, kBatchSlots in *.
replace a with (aeval B ly (aoff (batch_exp lastb) (24 + 8 * Z.of_nat (length (b_items lastb)))) + (a - SLOTv)) by (cbn; unfold AFgi.SLOTv, AFgi.Bv, AFgi.BCv; lia).
apply (vis_range _ (kBatchBytes - 24 - 8 * Z.of_nat (length (b_items lastb)))); [| unfold AFgi.SLOTv, AFgi.Bv, AFgi.BCv, kBatchBytes; lia].
left. unfold ajunk. right. right. rewrite !in_app_iff. do 4 right. left. unfold quar_junk. apply in_flat_map. exists lastb. split; [exact lastb_in | left; reflexivity].
Qed.
Lemma user_vis : forall a, pa <= a < pa + 8 -> rd0 a <> None.
Proof.
intros a Ha. pose proof kk_facts as (_ & Hk & Hst & Hu & _). pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in *.
destruct (Z_lt_le_dec a (pa + nn)) as [L|L].
- replace a with (aeval B ly (sptr_exp (ck_user kk)) + (a - pa)) by (unfold pa; rewrite <- Hu; unfold sptr_addr; lia).
apply (vis_range _ (ck_n kk)); [|rewrite <- Enn; lia]. do 2 right. unfold aclient. apply in_app_iff. left. apply in_flat_map. exists kk. split; [exact Hk|].
unfold chunk_user. rewrite Hst. left. reflexivity.
- replace a with (aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk + ck_n kk)) + (a - pa - nn)) by (rewrite (AFex.EA B ly S rd0 M lastb kk _ Hk), Epa, Enn; lia).
apply (vis_range _ (ck_extent kk - ck_rz kk - ck_n kk)); [|rewrite <- Enn; lia].
left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists kk. split; [exact Hk|].
unfold chunk_junk. rewrite !in_app_iff. do 3 right. left. reflexivity.
Qed.
Lemma j3_val : val_mem tfibsegs m0 pa 8 j3 /\ 0 <= j3 < 2 ^ 64.
Proof.
destruct (vis_word H0 mem pa) as (w & Rw & Vw & Ew); [intros i Hi; apply user_vis; lia|]. unfold j3, jw. rewrite Ew. auto.
Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
eapply cell_stateZ; [|reflexivity]. unfold acells. rewrite !in_app_iff. do 8 right. left. reflexivity.
Qed.
Lemma meta_vis : forall a, pa - 16 <= a < pa -> rd0 a <> None.
Proof.
intros a Ha. pose proof kk_facts as (_ & Hk & _). pose proof hw_val as [V1 V2].
destruct (Z_lt_le_dec a (pa - 12)) as [L1|L1]. { replace a with (pa - 16 + (a - (pa - 16))) by lia. exact (val_mem_vis _ _ _ _ _ (a - (pa - 16)) V1 ltac:(lia)). }
destruct (Z_lt_le_dec a (pa - 8)) as [L2|L2]. { replace a with (pa - 12 + (a - (pa - 12))) by lia. exact (val_mem_vis _ _ _ _ _ (a - (pa - 12)) V2 ltac:(lia)). }
replace a with (aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - 8)) + (a - (pa - 8))) by (rewrite (AFex.EA B ly S rd0 M lastb kk _ Hk), Epa; lia).
apply (vis_range _ 8); [|lia]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. apply in_flat_map. exists kk. split; [exact Hk|].
unfold chunk_junk. rewrite !in_app_iff. right. left. left. reflexivity.
Qed.
Lemma shadow_vis : forall i, 0 <= i < CNT8v -> exists v, rd0 (SPv + i) = Some v.
Proof.
intros i Hi. pose proof kk_facts as (_ & Hk & _). pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3).
pose proof (AFex.u_al8 B ly S rd0 M kk lastb Hk) as (U8 & B8 & R8). pose proof KF as (G1 & G2 & G3 & G4 & G5 & _).
unfold AFgi.CNT8v, AFgi.N8v in Hi. rewrite Z_div_mult in Hi by lia. rewrite <- Enn in *.
set (g := pa + 8 * i).
assert (FC : find_chunk_at B ly (st_chunks S) g = Some kk).
{ apply (find_chunk_at_hit B ly S rd0 (st_chunks S) kk g M ltac:(intros x Hx; exact Hx) (wf_chunks_nodup _ _ _ _ _ WF) Hk). subst g.
pose proof Epa as EP. clear - EP Hi ER NN2 G5. rewrite EP. lia. }
assert (SH : ashadow B ly S g = Some (chunk_granule kk ((g - ck_base B ly kk) / 8))) by (unfold ashadow; rewrite FC; reflexivity).
pose proof kk_facts as (_ & _ & _ & Hu & _).
assert (PC : exists c, pa = c * 8). { apply Z.mod_divide in U8 as [c Hc]; [|lia]. exists c. unfold pa. rewrite <- Hu. exact Hc. }
destruct PC as [c Hc].
pose proof (am_shadow B ly S rd0 M g _ ltac:(subst g; rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult) SH) as R.
exists (chunk_granule kk ((g - ck_base B ly kk) / 8)). rewrite <- R. f_equal. unfold shadow_addr, AFgi.SPv. subst g.
rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia.
Qed.
Lemma ial_vals : val_mem tfibsegs m0 TFIB_IAL_FLAG 1 (if st_internal_inited S then 1 else 0) /\ val_mem tfibsegs m0 (TFIB_IAL_FLAG + 1) 1 0 /\
(if st_internal_inited S then val_mem tfibsegs m0 TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m0 TFIB_IAL_W 8 0 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 0) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells B ly S)) by (intros c Hc; unfold acells; rewrite !in_app_iff; do 7 right; left; exact Hc).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB) in IN.
splits.
- replace TFIB_IAL_FLAG with (aeval B ly (ANum TFIB_IAL_FLAG)) at 1 by reflexivity. eapply cell_stateZ; [apply IN; left; reflexivity | destruct (st_internal_inited S); reflexivity].
- replace (TFIB_IAL_FLAG + 1) with (aeval B ly (ANum (TFIB_IAL_FLAG + 1))) by reflexivity. eapply cell_stateZ; [apply IN; right; left; reflexivity | reflexivity].
- assert (E1 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO)) = TFIB_IAL_W) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E2 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 8)) = TFIB_IAL_W + 8) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E3 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) = TFIB_IAL_W + 16) by (cbn; rewrite (ts_ial_lo _ TB); lia).
destruct (st_internal_inited S); split.
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2, <- E3. eapply cell_state; [apply IN; do 3 right; left; reflexivity | reflexivity].
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2. eapply (cell_state _ _ 8 (ANum 0)); [apply IN; do 3 right; left; reflexivity | reflexivity].
- intros a Ha. pose proof (am_zero B ly S rd0 M) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : rd0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFIB_IAL_LO)) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z1. cbn [snd]. lia.
- replace a with (aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) + (a - (TFIB_IAL_W + 16))) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z2. cbn [snd]. lia. }
exact (aview_byte _ _ _ _ R).
Qed.
Lemma HB1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17. Proof. pose proof hb1_facts; tauto. Qed.
Lemma HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & Hlo & _ & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct PRE as ((_ & LED & _) & _). exact (img_cover_of_ledger ly S md LED). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
zone3 (ck_base B ly kk) (ck_extent kk) /\ ck_base B ly kk + ck_extent kk <= ASAN_CEIL /\ 16 <= ck_rz kk /\
kHighMemBeg <= Bv /\ Bv + kBatchBytes <= ASAN_CEIL /\ ly_stk_lo ly mod 4096 = 0 /\
ly_prim ly <= Bv /\ Bv + kBatchBytes <= ly_space ly + kSpaceSize.
Proof. exact (AFex.HIGH B ly S rd0 M kk lastb initr hb1 (proj1 (proj2 kk_facts)) Hrev HB1 sp0 HSP IMG). Qed.
Lemma items_n_pos : forall b x, In b (all_batches S) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros b x Hb Hx. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x ltac:(unfold q_items; apply in_flat_map; exists b; auto)) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(lia)). lia.
Qed.
Lemma b_bytes_ge : forall b, In b (all_batches S) -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. unfold b_bytes.
assert (G : forall l, incl l (b_items b) -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 l).
{ induction l as [|x t IH]; intros Hl; cbn; [lia|]. pose proof (items_n_pos b x Hb (Hl x (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). lia. }
pose proof (G (b_items b) ltac:(intros y Hy; exact Hy)). lia.
Qed.
Lemma sum_bytes_ge : forall l, incl l (all_batches S) -> 0 <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros Hl; cbn; [unfold sum_bytes; cbn; lia|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge b (Hl b (or_introl eq_refl))). pose proof (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). unfold kBatchBytes in *. lia.
Qed.
Lemma QB_facts : 0 <= QBv /\ QBv + nn <= kQuarantineCacheMax /\ kBatchBytes <= BBv /\ BBv <= QBv /\ 1 <= QSv /\ QSv <= 2 ^ 17   /\ BCv < kBatchSlots /\ 1 <= nn < 2 ^ 28.
Proof.
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE. pose proof lastb_in as LB.
assert (SUM : qc_bytes q = sum_bytes (rev initr) + b_bytes lastb).
{ rewrite QE, qlist0, sum_bytes_app. unfold sum_bytes at 2. cbn [fold_right]. lia. }
assert (LEN : Z.of_nat (length (qc_list q)) = Z.of_nat (length initr) + 1).
{ rewrite qlist0, length_app, length_rev. cbn [length]. lia. }
pose proof (sum_bytes_ge (rev initr) ltac:(intros y Hy; unfold all_batches; rewrite qlist0, !in_app_iff; tauto)) as S1.
pose proof (b_bytes_ge lastb LB) as S2. pose proof Hroom as HR.
assert (BB : Z.of_nat (length (all_batches S)) <= 2 ^ 17).
{ pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ((T1 & T2 & _) & _)).
apply (YG0l.batches_len_bound _ _ _ _ S WF); [unfold kQuarantineCacheMax, kQuarantineMax in *; clear - T1 T2; lia | unfold kBatchBytes in S2; clear - SUM S1 S2; lia]. }
unfold all_batches in BB. rewrite length_app in BB.
pose proof kk_facts as (_ & Hk & _ & _ & Hr). pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [N _].
pose proof (req_size_bounds (ck_req kk) ltac:(lia)) as (Q1 & Q2 & Q3). rewrite Hr in Q1, Q2, Q3, N. unfold MALLOC_MAX in N.
pose proof (proj2 (proj2 ARM)) as HC.
unfold AFgi.QBv, AFgi.BBv, AFgi.QSv. unfold nn in *. unfold kBatchBytes in *. splits; lia.
Qed.
Lemma QF_facts : 0 <= QFv < 2 ^ 64.
Proof.
unfold AFgi.QFv. rewrite qlist0.
assert (G : forall b0, In b0 (all_batches S) -> 0 <= SB + b_self b0 < 2 ^ 64).
{ intros b0 Hb0. destruct (AFex.batch_geom B ly S rd0 M lastb hb1 HB1 sp0 HSP b0 Hb0) as (x & Ex & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). pose proof HI as (hP1 & hP2 & _). ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes in *. lia. }
destruct (rev initr) as [|b0 t] eqn:E; cbn [app]; apply G; unfold all_batches; rewrite qlist0, E, !in_app_iff; cbn; tauto.
Qed.
Lemma p_zone : zone3 (pa - 16) (N8v + 16).
Proof.
pose proof kk_facts as (_ & Hk & _). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3). pose proof Epa as EP. rewrite <- Enn in *.
pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZK & _). clear - G1 G4 G5 ER NN1 NN2 NN3 EP ZK.
unfold AFgi.N8v. rewrite EP. ceil. unfold zone3, zone3cases, in_app in *. lia.
Qed.
Lemma p_facts : 4096 + 16 <= pa /\ pa + N8v <= ASAN_CEIL /\ pa mod 16 = 0 /\ pa mod 8 = 0 /\ 8 <= N8v /\ nn <= N8v < nn + 8 /\ N8v mod 8 = 0 /\
1 <= LENv <= 30 /\ 0 <= IMv - 0xa7200 <= 8 * 0x7fff /\ IMv mod 8 = 0 /\ SHADOW_OFF + 514 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ SPv mod 2 = 0 /\
CNT8v = (nn + 7) / 8.
Proof.
pose proof kk_facts as (_ & Hk & _). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3). pose proof (AFex.u_al8 B ly S rd0 M kk lastb Hk) as (U8 & B8 & R8).
pose proof Epa as EP. rewrite <- Enn in *.
assert (LO16 : 4096 <= ck_base B ly kk) by (clear - G1; unfold in_app in G1; lia).
assert (P16 : pa mod 16 = 0).
{ rewrite EP. apply Z.mod_divide in G3 as [c Hc]; [|lia]. apply Z.mod_divide in G6 as [c' Hc']; [|lia]. rewrite Hc, Hc'. apply Z.mod_divide; [lia|]. exists (c + c'). lia. }
unfold AFgi.N8v, AFgi.LENv, AFgi.IMv, AFgi.SPv, AFgi.CNT8v, AFgi.N8v. rewrite !Z_div_mult by lia.
pose proof (unwind_of_chain_length 0x52a6c ((spZ regs, raZ regs, s0Z regs) :: ch)) as UL.
assert (LEN : (1 <= length (AFgi.tr ly regs ch) <= 30)%nat).
{ unfold AFgi.tr, call_trace. destruct (frame0_ok ly regs); [exact UL | cbn; lia]. }
apply Z.mod_divide in P16 as [c Hc]; [|lia].
pose proof (Z.div_le_mono 4112 pa 8 ltac:(lia) ltac:(lia)) as S1. change (4112 / 8) with 514 in S1.
pose proof (AFex.hs_bounds lastb (pa + (nn + 7) / 8 * 8 - 8) ltac:(lia) ltac:(ceil; unfold kHighMemEnd, ASAN_CEIL in *; lia)) as [_ S2].
unfold shadow_addr in S2. replace (pa + (nn + 7) / 8 * 8 - 8) with (pa + ((nn + 7) / 8 - 1) * 8) in S2 by lia. rewrite Z.div_add in S2 by lia.
assert (D32 : 0 <= pa / 2 ^ 32 <= 32767).
{ change (2 ^ 32) with 4294967296. split; [apply Z.div_pos; lia|].
pose proof (Z.div_le_mono pa 140737479966720 4294967296 ltac:(lia) ltac:(ceil; unfold ASAN_CEIL in *; lia)) as X. change (140737479966720 / 4294967296) with 32767 in X. exact X. }
assert (IM8 : (684544 + 8 * (pa / 2 ^ 32)) mod 8 = 0). { apply Z.mod_divide; [lia|]. exists (85568 + pa / 2 ^ 32). lia. }
assert (SP2 : (SHADOW_OFF + pa / 8) mod 2 = 0).
{ rewrite Hc. replace (c * 16) with (c * 2 * 8) by lia. rewrite Z_div_mult by lia. unfold SHADOW_OFF. apply Z.mod_divide; [lia|]. exists (1073725440 + c). lia. }
assert (P8 : pa mod 8 = 0). { rewrite Hc. replace (c * 16) with (c * 2 * 8) by lia. apply Z_mod_mult. }
assert (P16' : pa mod 16 = 0). { rewrite Hc. apply Z_mod_mult. }
assert (N88 : (nn + 7) / 8 * 8 mod 8 = 0) by apply Z_mod_mult.
splits; first [assumption | lia].
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgi.E2 ly regs ch pa nn hb1 q lastb j1 j2 j3). Qed.
Lemma E10 : ew E0 10 = w64 pa. Proof. rewrite (AFgi.E10 ly regs ch pa nn hb1 q lastb j1 j2 j3). exact HA0. Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.
Lemma EaIM : ew E0 37 = w64 IMv. Proof. reflexivity. Qed.
Lemma EaHW : ew E0 38 = w64 HWv. Proof. reflexivity. Qed.
Lemma EaN : ew E0 39 = w64 nn. Proof. reflexivity. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
Lemma EaSP : ew E0 41 = w64 SPv. Proof. reflexivity. Qed.
Lemma EaN8 : ew E0 42 = w64 N8v. Proof. reflexivity. Qed.
Lemma EaCNT8 : ew E0 43 = w64 CNT8v. Proof. reflexivity. Qed.
Lemma EaB : ew E0 44 = w64 Bv. Proof. reflexivity. Qed.
Lemma EaBB : ew E0 45 = w64 BBv. Proof. reflexivity. Qed.
Lemma EaBC : ew E0 46 = w64 BCv. Proof. reflexivity. Qed.
Lemma EaSLOT : ew E0 47 = w64 SLOTv. Proof. reflexivity. Qed.
Lemma EaQS : ew E0 48 = w64 QSv. Proof. reflexivity. Qed.
Lemma EaQF : ew E0 49 = w64 QFv. Proof. reflexivity. Qed.
Lemma EaQB : ew E0 50 = w64 QBv. Proof. reflexivity. Qed.
Lemma EaJ1 : ew E0 51 = w64 j1. Proof. reflexivity. Qed.
Lemma EaJ2 : ew E0 52 = w64 j2. Proof. reflexivity. Qed.
Lemma EaJ3 : ew E0 53 = w64 j3. Proof. reflexivity. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Ltac offw := first [ lia | apply off_img_high; unfold TFIB_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HI)))))); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; lia
| apply (zone3_off_img _ _ _ p_zone); unfold AFgi.N8v in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgi.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & hB1 & hB2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof QF_facts as QF. pose proof HB1 as [HBR _].
assert (BC0 : 0 <= BCv) by (unfold AFgi.BCv; lia).
pose proof qc_vals as (V1 & V2 & V3 & V4). pose proof batch_vals as (V5 & V6). pose proof junk_vals as (J1 & J1R & J2 & J2R). pose proof j3_val as [J3 J3R].
pose proof hw_val as [W1 W2].
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kHighShadowBeg, kQuarantineCacheMax, EV_MAX, kBatchSlots in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, hK1, hK2, hB1, hB2, S1, S2, T2, T4, T7, P1, P2, P11, P12, Q2, Q3, Q6, Q7.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold AFgi.REG0, flit1, flit4, flit8, flits8, fatom8. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aQS, aQF, aQB, aB, aBB, aBC, aSLOT, aHW, aN.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- ASTACK)); [rewrite E2; reflexivity | unfold ASTACK in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, ASTACK in *; lia | apply HPRES; exact Ha]. }
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | | unfold SHADOW_OFF; cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 13 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (6131600 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TB); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 6267704 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [|destruct (Z_lt_le_dec o 96); [|destruct (Z_lt_le_dec o 104)]];
[ apply (val_mem_writable _ _ _ _ V1) | apply (val_mem_writable _ _ _ _ V2) | apply (val_mem_writable _ _ _ _ V3) | apply (val_mem_writable _ _ _ _ V4) ];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 48%nat 0 QSv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 49%nat 0 QFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 44%nat 0 Bv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 50%nat 0 QBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_unwinding.
pose proof unwinding_val as U. unfold t_unwinding in U.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact U | cbn; lia | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 2832); [apply (val_mem_writable _ _ _ _ J1) | apply (val_mem_writable _ _ _ _ J2)]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 51%nat 0 j1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 52%nat 0 j2); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J2 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite E10. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o (-12)); [apply (val_mem_writable _ _ _ _ W1) | apply (val_mem_writable _ _ _ _ W2)]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 4 38%nat 0 HWv); [rewrite Z.sub_0_r; reflexivity | unfold AFgi.HWv; lia | replace (pa + -16) with (pa - 16) by lia; exact W1 | unfold AFgi.HWv; r4 | cbn; lia].
- apply (chunk_atom _ _ 4 39%nat 0 nn); [rewrite Z.sub_0_r; reflexivity | lia | replace (pa + -12) with (pa - 12) by lia; exact W2 | r4 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite E10. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ J3); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 53%nat 0 j3); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact J3 | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite EaB. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 16); [apply (val_mem_writable _ _ _ _ V5) | apply (val_mem_writable _ _ _ _ V6)]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 45%nat 0 BBv); [rewrite Z.sub_0_r; reflexivity | lia | exact V5 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 46%nat 0 BCv); [rewrite Z.sub_0_r; reflexivity | lia | exact V6 | r8 | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil]. {   reg_intro. rewrite EaSLOT. unfold w64.
pose proof slot_vis as SV. unfold AFgi.SLOTv, AFgi.BCv in *. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply vis_writable; [unfold TFIB_IMG_END; lia|]. apply SV. lia. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgi.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & hB1 & hB2 & _ & hB3 & hB4). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _). pose proof QB_facts as (_ & _ & _ & _ & _ & _ & Q7 & Q8).
pose proof kk_facts as (_ & Hk & _). pose proof Epa as EP. pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
pose proof (AFex.SX B ly S rd0 M lastb 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DCT.
pose proof (AFex.SX B ly S rd0 M lastb 6 8 _ _ eq_refl eq_refl ltac:(lia)) as DCS.
pose proof (AFex.SX B ly S rd0 M lastb 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS.
pose proof (AFex.SX B ly S rd0 M lastb 0 6 _ _ eq_refl eq_refl ltac:(lia)) as DCB.
pose proof (AFex.SX B ly S rd0 M lastb 0 2 _ _ eq_refl eq_refl ltac:(lia)) as DTB.
pose proof (AFex.SX B ly S rd0 M lastb 0 8 _ _ eq_refl eq_refl ltac:(lia)) as DSB.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 6 _ eq_refl ltac:(lia)) as DCP.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 2 _ eq_refl ltac:(lia)) as DTP.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 8 _ eq_refl ltac:(lia)) as DSP.
pose proof (AFex.batch_vs_chunk B ly S rd0 M lastb hb1 HB1 sp0 HSP lastb kk lastb_in Hk) as DPB.
unfold zdisjoint in DCT, DCS, DTS, DCB, DTB, DSB, DCP, DTP, DSP, DPB. cbn [fst snd] in DCT, DCS, DTS, DCB, DTB, DSB, DCP, DTP, DSP, DPB.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold AFgi.REG0, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aQS, aQF, aQB, aB, aBB, aBC, aSLOT, aHW, aN.
rewrite E2, E10, EaT, EaC, EaB, EaSLOT. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kNodesBlockSize, kStoreBlockSize, ASTACK, AFgi.SLOTv, AFgi.BCv, AFgi.Bv in *.
fold sp0. rewrite !unsigned_lit_small by lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hK1 hK2 hK3 hB1 hB2 hB3 hB4 hP1 hP2 hNB1 hSB1 P1 P2 P5 Q7 EP ER NN1 Usp DCT DCS DTS DCB DTB DSB DCP DTP DSP DPB CR CR0.
unfold TFIB_TP, TFIB_TSD, t_qc, t_unwinding, t_stats in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1, hK1.
repeat split;
first [ clear DCT DCS DTS DCB DTB DSB DCP DTP DSP DPB hT1 hC1 hK1; lia
| clear - hT1 CR0; lia
| clear - hC1 CR0; lia
| clear - hK1 hK3 EP ER NN1 P5 CR0; lia
| clear - hC1 hC2 hT1 hT2 DCT; lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp DCS; lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp DTS; lia
| clear - hC1 hC2 hK1 hK2 hK3 EP ER NN1 P5 DCP; lia
| clear - hT1 hT2 hK1 hK2 hK3 EP ER NN1 P5 DTP; lia
| clear - S1 S2 hS1 hS2 Usp hK1 hK2 hK3 EP ER NN1 P5 DSP; lia
| clear - hC1 hC2 hB1 hB2 hB3 hB4 hSP1 hSP2 hP1 hP2 Q7 DCB; lia
| clear - hT1 hT2 hB1 hB2 hB3 hB4 hSP1 hSP2 hP1 hP2 Q7 DTB; lia
| clear - S1 S2 hS1 hS2 Usp hB1 hB2 hB3 hB4 hSP1 hSP2 hP1 hP2 Q7 DSB; lia
| clear - hK1 hK2 hK3 EP ER NN1 P5 hB1 hB2 Q7 DPB; lia ].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms FF).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & hB1 & hB2 & _ & hB3 & hB4). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct PRE as (_ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof QF_facts as QF. pose proof HB1 as [HBR _].
pose proof junk_vals as (_ & J1R & _ & J2R). pose proof j3_val as [_ J3R].
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. unfold page_aligned in TAL, T3.
destruct (AFex.batch_geom B ly S rd0 M lastb hb1 HB1 sp0 HSP lastb lastb_in) as (xb & Exb & Pxb & Axb & _).
assert (BAL : Bv mod 8192 = 0).
{ unfold AFgi.Bv. rewrite Exb. unfold region_base. rewrite region_off_eq by (unfold kBatchClass; lia). unfold kBatchClass.
apply Z.mod_divide in SAL as [c Hc]; [|lia]. apply Z.mod_divide in Axb as [c' Hc']; [|unfold kBatchBytes; lia]. rewrite Hc, Hc'. unfold kBatchBytes.
apply Z.mod_divide; [lia|]. exists (c * 8 + 24 * 524288 + c'). lia. }
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kHighShadowBeg, kQuarantineCacheMax, EV_MAX, ASTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, hK1, hK2, hB1, hB2, hB3, hB4, S1, S2, T2, T4, T7, P1, P2, P11, P12, Q2, Q3, Q6, Q7.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
unfold AFgi.Bv in *. cbn [FF f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM, aHW, aN, aSP, aN8, aCNT8, aB, aBB, aBC, aSLOT, aQS, aQF, aQB, aJ1, aJ2, aJ3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, kBatchSlots.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 10%nat pa); [exact E10| | | |].
all: clear - CR0 P1 P2 P3 P5; first [lia | change (2 ^ 4) with 16; exact P3 | apply Z.mod_divide in P3 as [c Hc]; [|lia]; lia]. }
split. { apply (AF 32%nat T); [exact EaT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |]. all: clear - CR0 hC1 hC2 CAL; first [lia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [lia | exact T3]. }
split. { apply (AF 36%nat LENv); [exact EaLEN| | | |]. all: clear - CR0 P8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat IMv); [exact EaIM| | | |]. all: clear - CR0 P9 P10; first [lia | change (2 ^ 3) with 8; exact P10]. }
split. { apply (AF 38%nat HWv); [exact EaHW| | | |]. all: clear - CR0 HBR; unfold AFgi.HWv; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat nn); [exact EaN| | | |]. all: clear - CR0 Q8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat SHADOW_OFF); [exact EaSHB| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
split. { apply (AF 41%nat SPv); [exact EaSP| | | |]. all: unfold AFgi.SPv, SHADOW_OFF in *; clear - CR0 P1 P2 P5 P11 P12 P13 P14 Q8; first [lia | change (2 ^ 1) with 2; exact P13 | rewrite P14 in P12; pose proof (Z.div_pos (nn + 7) 8); nia]. }
split. { apply (AF 42%nat N8v); [exact EaN8| | | |]. all: clear - CR0 P5 P6 P7 Q8; first [lia | change (2 ^ 3) with 8; exact P7 | apply Z.mod_divide in P7 as [c Hc]; [|lia]; lia]. }
split. { apply (AF 43%nat CNT8v); [exact EaCNT8| | | |]. all: clear - CR0 P5 P6 P14 Q8; rewrite ?P14 in *; unfold AFgi.N8v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r | nia]. }
split. { apply (AF 44%nat (SB + b_self lastb)); [exact EaB| | | |]. all: clear - CR0 hB1 hB2 BAL; first [lia | change (2 ^ 13) with 8192; exact BAL]. }
split. { apply (AF 45%nat BBv); [exact EaBB| | | |]. all: clear - CR0 Q1 Q2 Q3 Q4 Q8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 46%nat BCv); [exact EaBC| | | |]. all: clear - CR0 Q7; unfold AFgi.BCv in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 47%nat SLOTv); [exact EaSLOT| | | |].
all: clear - CR0 hB1 hB2 BAL Q7; unfold AFgi.SLOTv, AFgi.BCv, AFgi.Bv in *; first [lia | change (2 ^ 3) with 8; apply Z.mod_divide in BAL as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (c * 1024 + 3 + Z.of_nat (length (b_items lastb))); lia]. }
split. { apply (AF 48%nat QSv); [exact EaQS| | | |]. all: clear - CR0 Q5 Q6; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 49%nat QFv); [exact EaQF| | | |]. all: clear - CR0 QF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 50%nat QBv); [exact EaQB| | | |]. all: clear - CR0 Q1 Q2 Q8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 51%nat j1); [exact EaJ1| | | |]. all: clear - CR0 J1R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 52%nat j2); [exact EaJ2| | | |]. all: clear - CR0 J2R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 53%nat j3); [exact EaJ3| | | |]. all: clear - CR0 J3R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgi.SS0 (restrict (w_H W) (mkst regs (w64 0x5292c) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
rewrite restrict_mkst_fx. unfold AFgi.SS0, AFgi.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
Theorem FH_ok : free_hyps W ly regs mem ch pa nn hb1 q lastb j1 j2 j3 (st_internal_inited S).
Proof.
pose proof PRE as PRE'. destruct PRE' as ((MM & _ & _) & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). unfold spZ, raZ, s0Z in *. fold sp0 in Hal, Hlo, Hbot, Hhi, HPRES, Hch.
pose proof kk_facts as (_ & Hk & Hst & Hu & Hr). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof Epa as EP.
pose proof (AFex.ext_rounded B ly S rd0 M kk lastb Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof QF_facts as QF. pose proof HB1 as [HBR HBM].
pose proof junk_vals as (_ & J1R & _ & J2R). pose proof j3_val as [_ J3R]. pose proof HI as HH.
constructor.
- exact LO.
- exact HA0.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- destruct Hch as [R4096 _]. exact R4096.
- splits; lia.
- exact Hal.
- destruct Hch as [_ CH]. unfold frame0_ok, spZ, s0Z in CH. fold sp0 in CH. exact CH.
- exact p_zone.
- exact IMG.
- exact P3.
- exact Q8.
- exact HBR.
- exact HBM.
-   intros a Ha.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 8 _ eq_refl ltac:(lia)) as D7. pose proof (AFex.KX B ly S rd0 M kk lastb Hk 2 _ eq_refl ltac:(lia)) as D2.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 6 _ eq_refl ltac:(lia)) as D6. pose proof (AFex.KX B ly S rd0 M kk lastb Hk 4 _ eq_refl ltac:(lia)) as D4.
pose proof (AFex.KX B ly S rd0 M kk lastb Hk 5 _ eq_refl ltac:(lia)) as D5. pose proof (AFex.KX B ly S rd0 M kk lastb Hk 7 _ eq_refl ltac:(lia)) as DD.
unfold zdisjoint in D7, D2, D6, D4, D5, DD. cbn [fst snd] in D7, D2, D6, D4, D5, DD. clear - Ha D7 D2 D6 D4 D5 DD EP ER G5 P5. unfold AFgi.N8v in *. splits; lia.
-   intros a Ha. apply vis_apresent_off; [exact (zone3_off_img _ _ a p_zone ltac:(clear - Ha P5 P6; lia))|].
destruct (Z_lt_le_dec a pa); [apply meta_vis; lia | apply user_vis; lia].
-   intros a Ha. destruct (shadow_vis (a - SPv) ltac:(lia)) as [v Hv]. replace (SPv + (a - SPv)) with a in Hv by lia.
apply vis_apresent; [unfold SHADOW_OFF, kHighMemBeg, TFIB_IMG_END in *; lia | rewrite Hv; discriminate].
- pose proof QB_facts as QQ. unfold kBatchBytes, kQuarantineCacheMax, EV_MAX in QQ. split; [rewrite qlist0; destruct (rev initr); discriminate|]. clear - QQ. unfold kBatchBytes, kQuarantineCacheMax, EV_MAX, kBatchSlots in *. splits; lia.
- rewrite Hrev. reflexivity.
- destruct (AFex.batch_geom B ly S rd0 M lastb hb1 HB1 sp0 HSP lastb lastb_in) as (xb & Exb & Pxb & _).
pose proof HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hSP1 & hSP2 & _ & _ & _ & _ & _ & _ & hB3 & hB4).
unfold AFgi.Bv, region_base in *. rewrite region_off_eq in Exb by (unfold kBatchClass; lia). clear - Exb Pxb hB4 QF. unfold kBatchClass, kBatchBytes in *. splits; lia.
-   destruct (AFex.batch_geom B ly S rd0 M lastb hb1 HB1 sp0 HSP lastb lastb_in) as (xb & Exb & Pxb & Axb & _).
unfold AFgi.AL, AFgi.Bv. rewrite Exb. unfold region_base. rewrite region_off_eq by (unfold kBatchClass; lia). unfold kBatchClass.
pose proof (lo_space_al ly LO) as SAL. apply Z.mod_divide in SAL as [c Hc]; [|lia]. apply Z.mod_divide in Axb as [c' Hc']; [|unfold kBatchBytes; lia]. rewrite Hc, Hc'. unfold kBatchBytes.
apply Z.mod_divide; [lia|]. exists (c * 8 + 24 * 524288 + c'). lia.
-   pose proof (AFex.batch_vs_chunk B ly S rd0 M lastb hb1 HB1 sp0 HSP lastb kk lastb_in Hk) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - D EP ER G5 P5. unfold AFgi.PBDISJ, AFgi.N8v, AFgi.Bv, kBatchBytes in *. lia.
-   intros a Ha. pose proof batch_vals as [V5 V6]. pose proof HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hB1 & hB2 & _).
apply vis_apresent; [ceil; unfold AFgi.SLOTv, kHighMemBeg, ASAN_CEIL, TFIB_IMG_END, kBatchBytes, AFgi.BCv, kBatchSlots in *; lia|].
destruct Ha as [Ha|Ha]; [|apply slot_vis; exact Ha].
destruct (Z_lt_le_dec a (Bv + 16)).
+ replace a with (Bv + 8 + (a - (Bv + 8))) by lia. eapply val_mem_vis; [exact V5 | lia].
+ replace a with (Bv + 16 + (a - (Bv + 16))) by lia. eapply val_mem_vis; [exact V6 | lia].
- splits; lia.
- pose proof ial_vals as IV. exact IV.
- exact IA1.
- exact U1.
- exact SEED_ok.
Qed.
End h.
Theorem afree_common : forall B, TfibSyms B -> forall ly S W regs mem md p n ch lastb initr,
acall_pre tfibsegs B ly S W regs mem md ch -> In (p, n) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly 0x52a6c regs ch) (as_universe B) ->
rev (qc_list (st_qthread S)) = lastb :: initr /\ Z.of_nat (length (b_items lastb)) < kBatchSlots /\ qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
tfib_ialloc_spec -> tfib_unwind_spec -> tfib_depot_spec B -> ly_tsd ly = TFIB_TSD ->
amreal tfibsegs (free p (call_trace ly 0x52a6c regs ch) S) W (cfg_at tfibsegs 0x5292c regs mem md) (free_leaf tfibsegs B ly S W regs mem md p n).
Proof.
intros B TB ly S W regs mem md p n ch lastb initr PRE HBLK HA0 HU ARM IA1 U1 D1 HTSD.
exact (AFfy.afree_common_arm B TB ly S W regs mem md p n ch PRE HBLK HU lastb initr ARM D1 _ _ _ _
(FH_ok B TB ly S W regs mem md p n ch PRE HBLK HA0 lastb initr ARM IA1 U1 HTSD) HTSD).
Qed.
End f.
