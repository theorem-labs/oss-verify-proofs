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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFi9 AFjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0v YK13 YP0n YA05 YA09 YG0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFia AFid AFie AFif AFjh AFji AFjk AFjo AFjr AFjs AFju AFk0 AFk2 AFi3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YA00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma word_of_bytes : forall (m : word -> option byte) a,
(forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m (a + Z.of_nat k) = Some b) -> exists w, val_mem tfibsegs m a 8 w.
Proof.
intros m a BY.
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YO0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m (a + Z.of_nat kk) = Some bk -> YO0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. repeat split; reflexivity. Qed.
Lemma SRr_with_AI : forall (Wx : world tfibsegs) cx (Q : world tfibsegs -> config -> Prop),
SRr tfibsegs Wx cx Q -> SRr tfibsegs Wx cx (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. intros Wx cx Q H HI T HK. apply (H HI T). intros W' c' Hle HI' HQ. exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Section f.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x52bcc regs0 ch.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let idx : Z := Z.of_nat (length (st_sec_arr S)).
Let res : Z := st_sec_reserved S.
Let mat0 : list word := m_vm_materialized md0.
Lemma HAR0 : AR tfibsegs B ly S W mem0 md0. Proof. exact (proj1 PRE). Qed.
Lemma HARm0 : ARm B ly S (aview tfibsegs (w_H W) mem0). Proof. exact (proj1 HAR0). Qed.
Lemma HDC : AFk2.DCELLS W mem0.
Proof.
unfold AFk2.DCELLS. repeat split; apply (tfib_const_lookup B TS ly S (w_H W) mem0 _ _ _ HARm0); vm_compute; reflexivity.
Qed.
Lemma HBC : AFk1.BCELLS W mem0.
Proof.
unfold AFk1.BCELLS.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x214ac 1 0x04 HARm0 ltac:(vm_compute; reflexivity)) as L1.
pose proof (tfib_const_lookup B TS ly S (w_H W) mem0 0x214ad 1 0xff HARm0 ltac:(vm_compute; reflexivity)) as L2.
repeat split; try (apply (tfib_const_lookup B TS ly S (w_H W) mem0 _ _ _ HARm0); vm_compute; reflexivity).
intros k Hk. destruct k as [|[|k]]; [ | | cbn in Hk; lia].
- pose proof (L1 0%nat ltac:(cbn; lia)) as X. change (0x214ac + Z.of_nat 0) with 0x214ac in X |- *. rewrite X. reflexivity.
- pose proof (L2 0%nat ltac:(cbn; lia)) as X. change (0x214ad + Z.of_nat 0) with 0x214ad in X. change (0x214ac + Z.of_nat 1) with 0x214ad. rewrite X. reflexivity.
Qed.
Lemma Hev : aregime S. Proof. exact (proj1 (proj2 PRE)). Qed.
Lemma LY : layout_ok ly. Proof. exact (am_layout _ _ _ _ HARm0). Qed.
Lemma IMG : img_cover ly. Proof. exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0))). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0). exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _). rewrite (ts_tp B TS) in Htp'. exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as (_ & _ & H & _). exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as (_ & _ & _ & Hal & Hlo & Hbot & Hhi & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HQT : qmeter S. Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [H _] & _). exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ H] & _). unfold frame0_ok, spZ, s0Z in H. exact H. Qed.
Lemma WF0 : Wf (as_universe B) S. Proof. exact (am_wf _ _ _ _ HARm0). Qed.
Lemma Hidx : 0 <= idx < kMaxNumChunks.
Proof. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. unfold idx, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia. Qed.
Lemma Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Proof.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ WF0)) as [_ RA].
unfold idx, res, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. split; [lia | exact RA].
Qed.
Lemma Hidx_def : idx = Z.of_nat (length (st_sec_arr S)). Proof. reflexivity. Qed.
Lemma Hres_def : res = st_sec_reserved S. Proof. reflexivity. Qed.
Lemma FP : from_primary n = false.
Proof. pose proof (AFjy.sizes_model ly regs0 n res Nrange S) as (_ & _ & _ & _ & FP' & _). exact FP'. Qed.
Lemma junk_at : forall e len a, In (e, len) (ajunk B ly S) -> aeval B ly e <= a -> a + 8 <= aeval B ly e + len ->
exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w.
Proof.
intros e len a Hin H1 H2. apply word_of_bytes. intros k Hk.
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a + Z.of_nat k - aeval B ly e)
(proj1 (Forall_forall _ _) (am_junk B ly S _ HARm0) _ Hin) ltac:(lia)) as [b Hb].
exists b. replace (aeval B ly e + (a + Z.of_nat k - aeval B ly e)) with (a + Z.of_nat k) in Hb by lia. exact Hb.
Qed.
Lemma JUNK : exists j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3,
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa2c58 8 j6 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa2c60 8 j7 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (AFjm.BSLv n) 8 j8 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Proof.
pose proof (@AFjm.BSLv_range ly regs0 n idx res 0 Nrange Hidx) as HB. pose proof (ts_inst B TS) as EI.
assert (TJ1 : forall a, T + t_cache_stats <= a -> a + 8 <= T + t_stats -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_at (AT t_cache_stats) (t_stats - t_cache_stats) a); [| cbn [aeval]; unfold T in *; lia | cbn [aeval]; unfold T in *; lia].
unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (TJ2 : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_at (AT t_stats) (t_unwinding - t_stats) a); [| cbn [aeval]; unfold T in *; lia | cbn [aeval]; unfold T in *; lia].
unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (SJ : forall a, TFIB_INST + o_sec_stats <= a -> a + 8 <= TFIB_INST + o_sec_mutex -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_at (AInst o_sec_stats) (o_sec_mutex - o_sec_stats) a); [| cbn [aeval]; rewrite EI; lia | cbn [aeval]; rewrite EI; lia].
unfold ajunk. right; right. do 3 (apply in_or_app; right). apply in_or_app; left. unfold sec_junk. cbn. tauto. }
assert (CJ : forall a, TFIB_INST + o_comb_stats <= a -> a + 8 <= TFIB_INST + o_comb_stats + 40 -> exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. apply (junk_at (ANum (TFIB_INST + o_comb_stats)) 40 a); [| cbn [aeval]; lia | cbn [aeval]; lia].
unfold ajunk. right; right. do 7 (apply in_or_app; right). apply (ts_junk_comb B TS). }
destruct (TJ1 (T + 2784)) as [j0 Hj0]; [unfold t_cache_stats; lia | unfold t_stats; lia |].
destruct (TJ2 (T + 2800)) as [j1 Hj1]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2808)) as [j2 Hj2]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2816)) as [j3 Hj3]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2872)) as [j4 Hj4]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2880)) as [j5 Hj5]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (TJ2 (T + 2904)) as [j9 Hj9]; [unfold t_stats; lia | unfold t_unwinding; lia |].
destruct (CJ 0xa2c58) as [j6 Hj6]; [unfold TFIB_INST, o_comb_stats; lia | unfold TFIB_INST, o_comb_stats; lia |].
destruct (CJ 0xa2c60) as [j7 Hj7]; [unfold TFIB_INST, o_comb_stats; lia | unfold TFIB_INST, o_comb_stats; lia |].
destruct (SJ (AFjm.BSLv n)) as [j8 Hj8]; [unfold o_sec_stats; lia | unfold o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats)) as [i1 Hi1]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats + 16)) as [i2 Hi2]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (SJ (TFIB_INST + o_sec_stats + 24)) as [i3 Hi3]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
exists j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, i1, i2, i3. repeat (split; [assumption|]). exact Hi3.
Qed.
Theorem malloc_sec :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct JUNK as (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & i1 & i2 & i3 & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj9 & Hj6 & Hj7 & Hj8 & Hi1 & Hi2 & Hi3).
pose proof HAR0 as HAR. pose proof HARm0 as HARm. pose proof Hev as HEV. pose proof LY as HLY. pose proof Hsp as HSP. pose proof Hidx as HI. pose proof Hres as HR.
pose proof Htp as HTP. pose proof Hra as HRA. pose proof Hra4096 as HRA4. pose proof Hch as HCH. pose proof Hpres0 as HP0. pose proof HTSD as HTS. pose proof Hgp as HGP. pose proof HQT as HQ.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) WF0 HEV); [lia | exact Hlive | exact Htr]. }
change tr with (AFjm.tr ly regs0 ch). rewrite (AFk0.malloc_secondary_eq ly regs0 n ch S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; lia); reflexivity|].
lazymatch goal with |- amreal _ _ _ ?c ?Q => pose proof (AFk0.sec_ask_eq ly regs0 n ch S W c Q) as EQ end.
unfold AFk0.S1 in EQ. rewrite EQ. clear EQ.
apply (amreal_mono tfibsegs _ _ _ (@AFk0.QLEAF fx _ W ly regs0 mem0 md0 n B S)).
{ intros [p s'] W' c' H [ns MP]. apply H. cbn [fst snd]. cbn in MP. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQ))). }
cbn [amreal].
pose proof (@AFjh.seg0 fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HTP HRA4 HSP HCH Nrange HI HR HP0 mat0 U1 (fun _ _ => True) B S TS HTS HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3) as PFX.
unfold cfg_at. replace md0 with (with_vm_backing (m_vm_lazy md0) mat0 md0) at 1 by (unfold mat0; apply with_vm_backing_id).
eapply SRr_bind; [exact PFX|]. clear PFX. intros W1 c1 _ HR1. pose proof (proj1 HR1) as EW. subst W1.
eapply SRr_mono; [exact (SRr_with_AI _ _ _ (@AFji.seg1 fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HSP Nrange HI HR _ _ HR1))|].
clear HR1 c1. intros W1 c1 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. subst W1.
pose proof HN as HNc. destruct HNc as (_ & ms1 & mat1 & E1 & Ec1 & _).
assert (EcM : cfg_model c1 = with_vm_backing (m_vm_lazy md0) mat1 md0) by (rewrite Ec1; reflexivity).
apply (@AFjs.nodeS fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG HSP Nrange HI HR B S HARm HQ _ S1 (AFk0.KSEC ly regs0 n ch S) (@AFk0.QLEAF fx _ W ly regs0 mem0 md0 n B S) c1 HAR HEV HN HAI).
- intros z Hz. exact Hz.
-
intros c' HRf _ _ _. rewrite EcM in HRf.
exact (@AFk0.refuseS fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG HTP HRA HSP Nrange HI HR (fun _ _ => True) B S TS HARm Hidx_def Hres_def mat1 c' HAR HEV HRf).
-
intros a W3 ms E'. cbv zeta. rewrite EcM.
intros GOK L1 MW1 LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 AI2 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB.
set (A := bv_unsigned a) in *.
assert (EA : a = w64 A) by (unfold w64, A; symmetry; apply Z_to_bv_bv_unsigned).
rewrite EA in GOK, AI2, MW2, IO2, EG2, VM2. rewrite EA.
pose proof (AFjm.size_facts n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
assert (MSB : 0 < AFjm.MSv n <= MALLOC_MAX + 4 * 4096) by (clear - Z1 Z8; unfold MALLOC_MAX in *; lia).
pose proof (AFia.grant_parts _ (w64 A) _ GOK) as (GP1 & GP2 & GP3 & _).
pose proof (AFia.grant_zone B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GH.
pose proof (AFia.grant_apart B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GA.
assert (UA : bv_unsigned (w64 A) = A) by (rewrite <- EA; reflexivity). rewrite UA in GP1, GP2, GP3, GH, GA.
assert (HmapA : A mod 4096 = 0 /\ AFjm.mzone A (AFjm.MSv n)) by (split; [exact GP1 | exact GH]).
assert (GAx : forall e, In e (static_extents ly ++ vis0_zones ly) -> zdisjoint (A, AFjm.MSv n) e).
{ intros e He. apply (proj1 (Forall_forall _ _) GA). rewrite app_assoc. apply in_app_iff. left. exact He. }
assert (HapartA : zdisjoint (A, AFjm.MSv n) (ly_T ly, kThreadObjSize) /\ zdisjoint (A, AFjm.MSv n) (ly_C ly, kCtxMapSize) /\
zdisjoint (A, AFjm.MSv n) (ly_prim ly, kPrimResvSize) /\ zdisjoint (A, AFjm.MSv n) (ly_Q ly, kPtrArrayResv) /\
zdisjoint (A, AFjm.MSv n) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (A, AFjm.MSv n) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (A, AFjm.MSv n) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
{ repeat split; apply GAx; unfold static_extents, owned_extents, vis0_zones; rewrite !in_app_iff; cbn [In]; tauto. }
destruct (Z.eq_dec idx res) as [EQ|NE].
+ exact (@AFk0.grantS_eq fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA (@AFju.DPOSTS ly regs0 ch B S W3) B S TS HTS HARm HGP Hidx_def Hres_def HQ W3 mat1 ms E' 0 HAR HEV Htr D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB EQ).
+ exact (@AFk0.grantS_ne fx _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA (@AFju.DPOSTS ly regs0 ch B S W3) B S TS HTS HARm HGP Hidx_def Hres_def W3 mat1 ms E' 0 HAR HEV Htr D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 VM2 HE' HS MEQ PRS HB NE).
- rewrite EcM. apply same_io_wvb.
Qed.
End f.
End d.
