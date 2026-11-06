(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGiy.v (a working branch 30a1993588f, c5 + memnorm; file sha256 ef93dce7a612) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* cgif_file's view facts: from ARm of the allocator state at the memory mem0, the machine facts the hit-g walk reads
   (the parts of AGif0cgif.hview, assembled in AGif1) for the cached chunk at the top of the per-thread cache of class cl.
   Ported from YFiy.v: the same scripts, restated without the walk's frame (no regs0, sp, DPOST or trace). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AGhy AGis.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Lemma In_combine_seq_last : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
induction l0 as [|y l0 IH]; intros x s; cbn.
- left. f_equal. lia.
- right. replace (s + Datatypes.S (length l0))%nat with (Datatypes.S s + length l0)%nat by lia. apply IH.
Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order (the
   argument lists are fixed by the section headers). *)
Set Default Proof Using "All".
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Section h.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pv := (@AGis.Pv ly cl).
Local Abbreviation PVv := (@AGis.PVv ly cl cnt).
Local Abbreviation Kv := (@AGis.Kv ly cl v).
Local Abbreviation SHBv := (@AGis.SHBv).
Local Abbreviation SKv := (@AGis.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGis.SSLOTv ly cl).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let m0 := mrestrict (w_H W) mem0.
Lemma cl_range : 1 <= cl <= 30.
Proof. pose proof (primary_geometry n Hn0 FP) as (G & _). rewrite <- Hcl_class in G. exact G. Qed.
Lemma cls_geom : 0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16.
Proof. pose proof cl_range as CR. pose proof (class_ok cl ltac:(lia)) as (K1 & K2 & K3 & K4 & _). repeat split; lia. Qed.
Lemma Kv_base : Kv = region_base ly cl + off.
Proof. unfold Kv, SB, region_base. pose proof cl_range. rewrite region_off_eq by zlia. zlia. Qed.
Lemma Hcl' : 1 <= cl <= 31. Proof. pose proof cl_range. zlia. Qed.
Lemma find_chunk_at_none : forall lst g, (forall k, In k lst -> ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)) -> find_chunk_at B ly lst g = None.
Proof.
induction lst as [|k t IH]; intros g H; [reflexivity|]. cbn [find_chunk_at].
destruct (Z.leb_spec (ck_base B ly k) g); destruct (Z.ltb_spec g (ck_base B ly k + ck_extent k)); cbn [andb];
try (apply IH; intros k' Hk'; apply H; right; exact Hk').
exfalso. apply (H k (or_introl eq_refl)). zlia.
Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (apply in_or_app; right). apply in_or_app. left. exact Hr. Qed.
Lemma T_zone : zone3 T kThreadObjSize.
Proof.
pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
exact (zone3_intro ly T kThreadObjSize IMG ltac:(unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)).
Qed.
Lemma In_acells_cache : forall c, In c (cache_cells S cl) -> In c (acells B ly S).
Proof.
intros c Hc. unfold acells. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists cl.
split; [apply In_zseq; pose proof cl_range; zlia | exact Hc].
Qed.
End h.
End f.
