(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6z YF7f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0v YK13 YQ0k YA05 YA09 YG0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF48 YF71 YF72 YF73 YF7a YF7b YF7d YF7h YF7k YF7l YF7n YF7t YF7v YF40.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma word_of_bytes {imgk : img} : forall (m : word -> option byte) a,
(forall k, (k < 8)%nat -> exists b, mbyte tfxsegs m (a + Z.of_nat k) = Some b) -> exists w, val_mem tfxsegs m a 8 w.
Proof.
intros m a BY.
destruct (BY 0%nat ltac:(img_lia)) as [b0 B0]. destruct (BY 1%nat ltac:(img_lia)) as [b1 B1]. destruct (BY 2%nat ltac:(img_lia)) as [b2 B2]. destruct (BY 3%nat ltac:(img_lia)) as [b3 B3].
destruct (BY 4%nat ltac:(img_lia)) as [b4 B4]. destruct (BY 5%nat ltac:(img_lia)) as [b5 B5]. destruct (BY 6%nat ltac:(img_lia)) as [b6 B6]. destruct (BY 7%nat ltac:(img_lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YP0g.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia.
rewrite (Z.mod_small z) by (img_try (img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); img_lia)).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(img_try (left; img_exact Hr)) Hz).
symmetry. img_apply (Z.mod_unique _ 256 q b); img_lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfxsegs m (a + Z.of_nat kk) = Some bk -> YP0g.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfxsegs m (a + Z.of_nat kk) = Some (Z_to_bv 8 (YP0g.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, Hl, Z_to_bv_bv_unsigned. img_refl. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|img_lia];
[ img_try (img_apply (GOAL b0 0%nat B0)) | img_try (img_apply (GOAL b1 1%nat B1)) | img_try (img_apply (GOAL b2 2%nat B2)) | img_try (img_apply (GOAL b3 3%nat B3))
| img_try (img_apply (GOAL b4 4%nat B4)) | img_try (img_apply (GOAL b5 5%nat B5)) | img_try (img_apply (GOAL b6 6%nat B6)) | img_try (img_apply (GOAL b7 7%nat B7)) ]; (subst WW; cbv beta).
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 0)) with 1; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 1)) with 256; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 2)) with 65536; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 3)) with 16777216; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; img_lia) | img_lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; img_lia) | img_lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; img_lia) | img_lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [img_lia | img_lia | img_lia | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; img_lia) | img_try (img_change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; img_lia) | img_lia].
Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. repeat split; img_refl. Qed.
Lemma SRr_with_AI {imgk : img} : forall (Wx : world tfxsegs) cx (Q : world tfxsegs -> config -> Prop),
SRr tfxsegs Wx cx Q -> SRr tfxsegs Wx cx (fun W' c' => AI tfxsegs (w_H W') (w_A W') (cfg_model c') /\ Q W' c').
Proof. intros Wx cx Q H b HI T HK. img_apply (H b HI T). intros W' c' Hle HI' HQ. img_exact (HK W' c' Hle HI' (conj HI' HQ)). Qed.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis D1 : tfx_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x53640 + D_2c4) regs0 ch.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Variable regsU : bvmap 5 word.
Hypothesis REGSU : forall extra : list word, regs_ok (Ereg regs0 extra) REGS_A regsU.
Hypothesis STKU : forall extra : list word, nth 4 extra (w64 0) = w64 (Z.of_nat (length tr)) ->
Forall (region_ok tfxsegs (Ereg regs0 extra) (mrestrict (w_H W) mem0)) [R_bstA; R_scrA; R_topA].
Hypothesis PBUF0 : YF7a.PBUF W ly regs0 ch mem0.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let idx : Z := Z.of_nat (length (st_sec_arr S)).
Let res : Z := st_sec_reserved S.
Let mat0 : list word := m_vm_materialized md0.
Lemma HAR0 : AR tfxsegs B ly S W mem0 md0. Proof. img_exact (proj1 PRE). Qed.
Lemma HARm0 : ARm B ly S (aview tfxsegs (w_H W) mem0). Proof. img_exact (proj1 HAR0). Qed.
Lemma HDC : YF7v.DCELLS W mem0.
Proof.
unfold YF7v.DCELLS. repeat split; img_apply (tfx_const_lookup B TS ly S (w_H W) mem0 _ _ _ HARm0); (img_case; vm_compute); img_refl.
Qed.
Lemma HBC : YF7u.BCELLS W mem0.
Proof.
unfold YF7u.BCELLS.
pose proof (tfx_const_lookup B TS ly S (w_H W) mem0 0x2150c 1 0x04 HARm0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as L1.
pose proof (tfx_const_lookup B TS ly S (w_H W) mem0 0x2150d 1 0xff HARm0 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as L2.
repeat split; try (img_apply (tfx_const_lookup B TS ly S (w_H W) mem0 _ _ _ HARm0); (img_case; vm_compute); img_refl).
intros k Hk. destruct k as [|[|k]]; [ | | img_try (cbn in Hk; img_lia)].
- pose proof (L1 0%nat ltac:(img_try (cbn; img_lia))) as X. change (0x2150c + Z.of_nat 0) with 0x2150c in X |- *. rewrite X. img_refl.
- pose proof (L2 0%nat ltac:(img_try (cbn; img_lia))) as X. img_change (0x2150d + Z.of_nat 0) with 0x2150d in X. img_change (0x2150c + Z.of_nat 1) with 0x2150d. rewrite X. img_refl.
Qed.
Lemma Hev : aregime S. Proof. img_exact (proj1 (proj2 PRE)). Qed.
Lemma LY : layout_ok ly. Proof. img_exact (am_layout _ _ _ _ HARm0). Qed.
Lemma IMG : img_cover ly. Proof. img_exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0))). Qed.
Lemma HTSD : ly_tsd ly = TFX_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0). img_exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFX_TP.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _). rewrite (ts_tp B TS) in Htp'. img_exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). img_exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as (_ & _ & H & _). img_exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as (_ & _ & _ & Hal & Hlo & Hbot & Hhi & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & H & _). img_exact H. Qed.
Lemma HQT : qtight S. Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). img_exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [H _] & _). img_exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ H] & _). unfold frame0_ok, spZ, s0Z in H. img_exact H. Qed.
Lemma WF0 : Wf (as_universe B) S. Proof. img_exact (am_wf _ _ _ _ HARm0). Qed.
Lemma Hidx : 0 <= idx < kMaxNumChunks.
Proof. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. unfold idx, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. img_lia. Qed.
Lemma Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Proof.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF0)) as R. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ WF0)) as [_ RA].
unfold idx, res, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. split; [img_lia | img_try (img_exact RA)].
Qed.
Lemma Hidx_def : idx = Z.of_nat (length (st_sec_arr S)). Proof. img_refl. Qed.
Lemma Hres_def : res = st_sec_reserved S. Proof. img_refl. Qed.
Lemma FP : from_primary n = false.
Proof. pose proof (YF7r.sizes_model ly regs0 n res Nrange S) as (_ & _ & _ & _ & FP' & _). img_exact FP'. Qed.
Lemma junk_at : forall e len a, In (e, len) (ajunk B ly S) -> aeval B ly e <= a -> a + 8 <= aeval B ly e + len ->
exists w, val_mem tfxsegs (mrestrict (w_H W) mem0) a 8 w.
Proof.
intros e len a Hin H1 H2. img_apply word_of_bytes. intros k Hk.
destruct (range_vis_mbyte B ly (w_H W) mem0 e len (a + Z.of_nat k - aeval B ly e)
(proj1 (Forall_forall _ _) (am_junk B ly S _ HARm0) _ Hin) ltac:(img_lia)) as [b Hb].
exists b. replace (aeval B ly e + (a + Z.of_nat k - aeval B ly e)) with (a + Z.of_nat k) in Hb by img_lia. img_exact Hb.
Qed.
Lemma JUNK : exists j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3,
val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e18 + D_10c0) 8 j6 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e20 + D_10c0) 8 j7 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (YF7f.BSLv n) 8 j8 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats) 8 i1 /\ val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 16) 8 i2 /\
val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 24) 8 i3.
Proof.
pose proof (@YF7f.BSLv_range imgk ly regs0 n idx res 0 Nrange Hidx) as HB. pose proof (ts_inst B TS) as EI.
assert (TJ1 : forall a, T + t_cache_stats <= a -> a + 8 <= T + t_stats -> exists w, val_mem tfxsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. img_apply (junk_at (AT t_cache_stats) (t_stats - t_cache_stats) a); [| img_try (cbn [aeval]; unfold T in *; img_lia) | img_try (cbn [aeval]; unfold T in *; img_lia)].
unfold ajunk. right; right. do 5 (img_apply in_or_app; right). img_apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (TJ2 : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> exists w, val_mem tfxsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. img_apply (junk_at (AT t_stats) (t_unwinding - t_stats) a); [| img_try (cbn [aeval]; unfold T in *; img_lia) | img_try (cbn [aeval]; unfold T in *; img_lia)].
unfold ajunk. right; right. do 5 (img_apply in_or_app; right). img_apply in_or_app; left. unfold thread_junk. cbn. tauto. }
assert (SJ : forall a, TFX_INST + o_sec_stats <= a -> a + 8 <= TFX_INST + o_sec_mutex -> exists w, val_mem tfxsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. img_apply (junk_at (AInst o_sec_stats) (o_sec_mutex - o_sec_stats) a); [| img_try (cbn [aeval]; rewrite EI; img_lia) | img_try (cbn [aeval]; rewrite EI; img_lia)].
unfold ajunk. right; right. do 3 (img_apply in_or_app; right). img_apply in_or_app; left. unfold sec_junk. cbn. tauto. }
assert (CJ : forall a, TFX_INST + o_comb_stats <= a -> a + 8 <= TFX_INST + o_comb_stats + 40 -> exists w, val_mem tfxsegs (mrestrict (w_H W) mem0) a 8 w).
{ intros a Ha1 Ha2. img_apply (junk_at (ANum (TFX_INST + o_comb_stats)) 40 a); [| img_try (cbn [aeval]; img_lia) | img_try (cbn [aeval]; img_lia)].
unfold ajunk. right; right. do 7 (img_apply in_or_app; right). img_apply (ts_junk_comb B TS). }
destruct (TJ1 (T + 2784)) as [j0 Hj0]; [img_try (unfold t_cache_stats; img_lia) | img_try (unfold t_stats; img_lia) |].
destruct (TJ2 (T + 2800)) as [j1 Hj1]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (T + 2808)) as [j2 Hj2]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (T + 2816)) as [j3 Hj3]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (T + 2872)) as [j4 Hj4]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (T + 2880)) as [j5 Hj5]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (TJ2 (T + 2904)) as [j9 Hj9]; [img_try (unfold t_stats; img_lia) | img_try (unfold t_unwinding; img_lia) |].
destruct (CJ (0xa6e18 + D_10c0)) as [j6 Hj6]; [img_try (unfold TFX_INST, o_comb_stats; img_lia) | img_try (unfold TFX_INST, o_comb_stats; img_lia) |].
destruct (CJ (0xa6e20 + D_10c0)) as [j7 Hj7]; [img_try (unfold TFX_INST, o_comb_stats; img_lia) | img_try (unfold TFX_INST, o_comb_stats; img_lia) |].
destruct (SJ (YF7f.BSLv n)) as [j8 Hj8]; [img_try (unfold o_sec_stats; img_lia) | img_try (unfold o_sec_mutex; img_lia) |].
destruct (SJ (TFX_INST + o_sec_stats)) as [i1 Hi1]; [img_lia | img_try (unfold o_sec_stats, o_sec_mutex; img_lia) |].
destruct (SJ (TFX_INST + o_sec_stats + 16)) as [i2 Hi2]; [img_lia | img_try (unfold o_sec_stats, o_sec_mutex; img_lia) |].
destruct (SJ (TFX_INST + o_sec_stats + 24)) as [i3 Hi3]; [img_lia | img_try (unfold o_sec_stats, o_sec_mutex; img_lia) |].
exists j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, i1, i2, i3. repeat (split; [img_try (assumption)|]). img_exact Hi3.
Qed.
Theorem malloc_sec :
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x323b8 + D_150) regsU mem0 md0) (mid_leaf B ly S W regs0 mem0 md0 n tr).
Proof.
destruct JUNK as (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & i1 & i2 & i3 & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj9 & Hj6 & Hj7 & Hj8 & Hi1 & Hi2 & Hi3).
pose proof HAR0 as HAR. pose proof HARm0 as HARm. pose proof Hev as HEV. pose proof LY as HLY. pose proof Hsp as HSP. pose proof Hidx as HI. pose proof Hres as HR.
pose proof Htp as HTP. pose proof Hra as HRA. pose proof Hra4096 as HRA4. pose proof Hch as HCH. pose proof Hpres0 as HP0. pose proof HTSD as HTS. pose proof Hgp as HGP. pose proof HQT as HQ.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ img_apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) WF0 HEV); [img_lia | img_try (img_exact Hlive) | img_try (img_exact Htr)]. }
img_change tr with (YF7f.tr ly regs0 ch). rewrite (YF7t.malloc_secondary_eq ly regs0 n ch S FP). eapply amreal_pure; [img_refl|].
eapply amreal_pure; [img_try (unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; img_apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; img_lia); img_refl)|].
lazymatch goal with |- amreal _ _ _ ?c ?Q => pose proof (YF7t.sec_ask_eq ly regs0 n ch S W c Q) as EQ end.
unfold YF7t.S1 in EQ. rewrite EQ. clear EQ.
img_apply (amreal_mono tfxsegs _ _ _ (@YF7t.QLEAF fx _ imgk W ly regs0 mem0 md0 n ch B S)).
{ intros [p s'] W' c' H [ns MP]. img_apply H. cbn [fst snd]. cbn in MP. destruct MP as (WF' & _ & _ & _ & _ & QT). img_exact (conj WF' (QT HQ)). }
cbn [amreal].
pose proof (@YF7a.seg0 fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HSP Nrange HI HR HP0 mat0 (fun _ _ => True) B S TS HTS HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3
regsU (REGSU (YF7f.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0)) (STKU (YF7f.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0) eq_refl) PBUF0) as PFX.
unfold YF7a.cfgU in PFX. unfold cfg_at. replace md0 with (with_vm_backing (m_vm_lazy md0) mat0 md0) at 1 by (img_try (unfold mat0; img_apply with_vm_backing_id)).
eapply SRr_bind; [img_try (img_exact PFX)|]. clear PFX. intros W1 c1 _ HR1. pose proof (proj1 HR1) as EW. (subst W1; cbv beta).
eapply SRr_mono; [img_try (img_exact (SRr_with_AI _ _ _ (@YF7b.seg1 fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG Hn HSP Nrange HI HR _ _ HR1)))|].
clear HR1 c1. intros W1 c1 _ [HAI HN]. cbv beta. pose proof (proj1 HN) as EW. (subst W1; cbv beta).
pose proof HN as HNc. destruct HNc as (_ & ms1 & mat1 & E1 & Ec1 & _).
assert (EcM : cfg_model c1 = with_vm_backing (m_vm_lazy md0) mat1 md0) by (img_try (rewrite Ec1; img_refl)).
img_apply (@YF7l.nodeS fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG HSP Nrange HI HR B S HARm HQ _ S1 (YF7t.KSEC ly regs0 n ch S) (@YF7t.QLEAF fx _ imgk W ly regs0 mem0 md0 n ch B S) c1 HAR HEV HN HAI).
- intros z Hz. img_exact Hz.
-
intros c' HRf _ _ _. rewrite EcM in HRf. img_apply amreal_E.
img_exact (@YF7t.refuseS fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 0 HLY IMG HTP HRA HSP Nrange HI HR (fun _ _ => True) B S TS HARm Hidx_def Hres_def mat1 c' HAR HEV HRf).
-
intros a W3 ms E'. cbv zeta. rewrite EcM.
intros GOK L1 MW1 LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 AI2 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB.
set (A := bv_unsigned a) in *.
assert (EA : a = w64 A) by (img_try (unfold w64, A; symmetry; img_apply Z_to_bv_bv_unsigned)).
rewrite EA in GOK, AI2, MW2, IO2, EG2, VM2. rewrite EA.
pose proof (YF7f.size_facts n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
assert (MSB : 0 < YF7f.MSv n <= MALLOC_MAX + 4 * 4096) by (img_try (clear - Z1 Z8; unfold MALLOC_MAX in *; img_lia)).
pose proof (YF48.grant_parts _ (w64 A) _ GOK) as (GP1 & GP2 & GP3 & _).
pose proof (YF48.grant_zone B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GH.
pose proof (YF48.grant_apart B ly S _ _ (w64 A) _ HARm L1 MSB Z9 GOK) as GA.
assert (UA : bv_unsigned (w64 A) = A) by (img_try (rewrite <- EA; img_refl)). rewrite UA in GP1, GP2, GP3, GH, GA.
assert (HmapA : A mod 4096 = 0 /\ YF7f.mzone A (YF7f.MSv n)) by (img_try (split; [img_try (img_exact GP1) | img_try (img_exact GH)])).
assert (GAx : forall e, In e (static_extents ly ++ vis0_zones ly) -> zdisjoint (A, YF7f.MSv n) e).
{ intros e He. img_apply (proj1 (Forall_forall _ _) GA). rewrite app_assoc. img_apply in_app_iff. left. img_exact He. }
assert (HapartA : zdisjoint (A, YF7f.MSv n) (ly_T ly, kThreadObjSize) /\ zdisjoint (A, YF7f.MSv n) (ly_C ly, kCtxMapSize) /\
zdisjoint (A, YF7f.MSv n) (ly_prim ly, kPrimResvSize) /\ zdisjoint (A, YF7f.MSv n) (ly_Q ly, kPtrArrayResv) /\
zdisjoint (A, YF7f.MSv n) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (A, YF7f.MSv n) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (A, YF7f.MSv n) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
{ repeat split; img_apply GAx; unfold static_extents, owned_extents, vis0_zones; rewrite !in_app_iff; cbn [In]; tauto. }
destruct (Z.eq_dec idx res) as [EQ|NE].
+ img_exact (@YF7t.grantS_eq fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA mat0 (@YF7n.DPOSTS imgk ly regs0 ch B S W3) B S TS HTS HARm HGP Hidx_def Hres_def HQ W3 mat1 ms E' 0 HAR HEV Htr D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 EG2 VM2 HE' HS MEQ PRS HB (fun XZx HX1 HX2 mdX cX EQX HRX HAIX => @YF7v.dieV fx _ imgk W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG HSP Nrange HI HR HmapA HapartA (@YF7n.DPOSTS imgk ly regs0 ch B S W3) B S TS HARm Hidx_def W3 mdX XZx HX1 HX2 HDC EQX cX HRX HAIX) EQ).
+ img_exact (@YF7t.grantS_ne fx _ imgk W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 A HLY IMG Hn HTP HRA HSP Nrange HI HR HmapA HapartA mat0 (@YF7n.DPOSTS imgk ly regs0 ch B S W3) B S TS HTS HARm HGP Hidx_def Hres_def W3 mat1 ms E' 0 HAR HEV Htr D1 (fun z m => iff_refl _) GOK LE3 SUB3 MON3 A3 VISM3 VISH3 OUT3 MW2 IO2 VM2 HE' HS MEQ PRS HB NE).
- rewrite EcM. img_apply same_io_wvb.
Qed.
End f.
End d.
