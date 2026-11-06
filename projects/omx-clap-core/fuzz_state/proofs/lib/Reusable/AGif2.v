(* copied from proofs/cgif/cgif_file_fuzzer/lib/AGif2.v @ 95e6f1d72b6 (a Theorem Labs lane, frozen), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The VIEW of the secondary path of the frame-generic Allocate walk (n >= 64513): the machine facts the
   secondary seed (AGi9.SREG0 / AGi9.S0) reads, at the machine level, over the allocator instance [inst].

   It is the secondary twin of AGif0n.hview, and it is read by the same two kinds of file:
   - the seed files AGjw (SREG0_ok) / AGjx (PAIRS_ok, FACTS_ok, SEED_ok) and the const-cell users AGk1 / AGk2
     prove the walk's hypotheses from it, with no allocator model;
   - an instance (cgif_file: from AR / ARm; the shared preset/reply instance: from its own relation) proves
     [sview] once, as the field [if_sview] of the secondary interface (AGif4.AIfaceS).
   Every cell is INSTANCE-RELATIVE ([inst + o_sec...]): the walk never pins [inst] to cgif's TFIB_INST.
   The file is image-free: the binary's segments, TSD slot, image window, symbol facts and constant cells are the
   fields of the class ImgBase.AImg ([Context {IM : AImg}]); cgif_file's instance is AGif2cgif.AImg_cgif. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.

(* The secondary view, for the instance at [inst] with [idx] live secondary chunks and [res] reserved
   pointer-array slots.  The clauses follow AGi9.SREG0's regions, in its order. *)
Record sview (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) (idx res : Z) : Prop := {
  sv_ly : layout_ok ly;
  sv_img : im_img_cover ly;
  sv_tsd : ly_tsd ly = im_tsd;
  (* the image's constant cells (global literals, the thread and context objects' fixed words) *)
  sv_const : Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly);
  (* the instance's fields: primary.space at +0x20, the two words at +0xe20, and the secondary's fixed cells *)
  sv_space : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_space) 8 (ly_space ly);
  sv_e20 : val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000;
  sv_e28 : val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010;
  sv_page : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_sec) 8 4096;
  sv_chunks : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_sec_chunks) 8 (ly_Q ly);
  sv_chunks80 : val_mem im_segs (mrestrict (w_H W) mem) (inst + 80) 8 (ly_Q ly);
  sv_resv88 : val_mem im_segs (mrestrict (w_H W) mem) (inst + 88) 8 kPtrArrayResv;
  (* the secondary allocator's counters: the reserved slots, the live chunks, the free mutex *)
  sv_res : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_sec_reserved) 8 res;
  sv_n : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_sec_n) 8 idx;
  sv_mutex : val_mem im_segs (mrestrict (w_H W) mem) (inst + o_sec_mutex) 4 0;
  (* the thread's unwinding flag is clear; its stats words and the instance's stats words are present *)
  sv_unw : val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0;
  sv_tpres : forall a, ly_T ly + t_cache_stats <= a < ly_T ly + t_unwinding -> apresent (w_H W) mem a;
  (* the instance's own stats words are in the image, where a byte can come from the rom: the allocator's
     invariant gives them as VISIBLE (aview), not as present in [mem] *)
  sv_spres : forall a, inst + o_sec_stats <= a < inst + o_sec_mutex -> aview im_segs (w_H W) mem a <> None;
  sv_cpres : forall a, inst + o_comb_stats <= a < inst + o_comb_stats + 40 -> aview im_segs (w_H W) mem a <> None;
  (* the committed part of the pointer array *)
  sv_qarr : forall a, ly_Q ly <= a < ly_Q ly + 8 * res -> apresent (w_H W) mem a;
  (* the counters' model bounds *)
  sv_idx : 0 <= idx < kMaxNumChunks;
  sv_resb : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine facts the seed files read out of the view.                                                           *)
Section v.
Variables (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem0 : word -> option byte) (idx res : Z).
Hypothesis TS : im_syms B.
Hypothesis SV : sview B W ly inst mem0 idx res.
Local Ltac sv := pose proof SV as [SLY SIMG STSD SCONST SSPACE SE20 SE28 SPAGE SCH SCH80 SRESV SRES SN SMTX SUNW STP SSP SCP SQ SIX SRB].

Lemma sv_cell_lit : forall a (w : nat) x, cell_lookup (im_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem im_segs (mrestrict (w_H W) mem0) a w x.
Proof using All.
sv. intros a w x E. apply (cell_holds_val_mem im_segs B ly (w_H W) mem0 (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview im_segs (w_H W) mem0)) (as_const B ly)) SCONST).
rewrite (im_const_eq B ly TS). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma sv_cell_sym : forall e (w : nat) e', cell_lookup (im_const ly) e = Some (ACell e w (AV e')) ->
val_mem im_segs (mrestrict (w_H W) mem0) (aeval B ly e) w (aeval B ly e').
Proof using All.
sv. intros e w e' E. apply (cell_holds_val_mem im_segs B ly (w_H W) mem0 e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview im_segs (w_H W) mem0)) (as_const B ly)) SCONST).
rewrite (im_const_eq B ly TS). exact (cell_lookup_In _ _ _ E).
Qed.

(* An 8-byte word of a readable range: the bytes are there, so some value is stored. *)
Lemma sv_byte_of_view : forall a, aview im_segs (w_H W) mem0 a <> None ->
exists b, mbyte im_segs (mrestrict (w_H W) mem0) a = Some b.
Proof using All.
intros a HV. destruct (mbyte im_segs (mrestrict (w_H W) mem0) a) as [b|] eqn:E; [exists b; reflexivity|].
exfalso. apply HV. unfold aview. rewrite E. reflexivity.
Qed.
Lemma sv_word_of_present : forall a, (forall k, (k < 8)%nat -> aview im_segs (w_H W) mem0 (a + Z.of_nat k) <> None) ->
exists w, val_mem im_segs (mrestrict (w_H W) mem0) a 8 w.
Proof using All.
intros a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte im_segs (mrestrict (w_H W) mem0) (a + Z.of_nat k) = Some b)
by (intros k Hk; apply sv_byte_of_view; exact (PR k Hk)).
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte im_segs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte im_segs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
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

(* The thread's stats words, the instance's secondary stats words (the by_size_log cells are inside them) and
   the combined allocator's stats words: present, hence each holds some value. *)
Lemma sv_tjunk_word : forall a, ly_T ly + t_cache_stats <= a -> a + 8 <= ly_T ly + t_unwinding ->
exists w, val_mem im_segs (mrestrict (w_H W) mem0) a 8 w.
Proof using All.
sv. intros a H1 H2. apply sv_word_of_present. intros k Hk.
destruct (apresent_mbyte im_segs (w_H W) mem0 (a + Z.of_nat k) (STP (a + Z.of_nat k) ltac:(lia))) as [b Hb].
unfold aview. rewrite Hb. discriminate.
Qed.
Lemma sv_sjunk_word : forall a, inst + o_sec_stats <= a -> a + 8 <= inst + o_sec_mutex ->
exists w, val_mem im_segs (mrestrict (w_H W) mem0) a 8 w.
Proof using All. sv. intros a H1 H2. apply sv_word_of_present. intros k Hk. apply SSP. lia. Qed.
Lemma sv_cjunk_word : forall a, inst + o_comb_stats <= a -> a + 8 <= inst + o_comb_stats + 40 ->
exists w, val_mem im_segs (mrestrict (w_H W) mem0) a 8 w.
Proof using All. sv. intros a H1 H2. apply sv_word_of_present. intros k Hk. apply SCP. lia. Qed.

(* The junk values AGjw / AGjx / AGio need as the seed's atoms: the thread's stats words (T + 2784, 2800, 2808,
   2816, 2872, 2880, 2904), the combined stats words (inst + o_comb_stats + 16, + 24), the instance's secondary
   stats words (inst + o_sec_stats, + 16, + 24) and the by_size_log cell [bsl]. *)
Lemma sv_junk_values : forall bsl, inst + o_sec_stats + 32 <= bsl -> bsl + 8 <= inst + o_sec_mutex ->
exists j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3,
val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2784) 8 j0 /\ val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2800) 8 j1 /\
val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2808) 8 j2 /\ val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2816) 8 j3 /\
val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2872) 8 j4 /\ val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2880) 8 j5 /\
val_mem im_segs (mrestrict (w_H W) mem0) (ly_T ly + 2904) 8 j9 /\
val_mem im_segs (mrestrict (w_H W) mem0) (inst + o_comb_stats + 16) 8 j6 /\
val_mem im_segs (mrestrict (w_H W) mem0) (inst + o_comb_stats + 24) 8 j7 /\
val_mem im_segs (mrestrict (w_H W) mem0) bsl 8 j8 /\
val_mem im_segs (mrestrict (w_H W) mem0) (inst + o_sec_stats) 8 i1 /\
val_mem im_segs (mrestrict (w_H W) mem0) (inst + o_sec_stats + 16) 8 i2 /\
val_mem im_segs (mrestrict (w_H W) mem0) (inst + o_sec_stats + 24) 8 i3.
Proof using All.
intros bsl HB1 HB2.
destruct (sv_tjunk_word (ly_T ly + 2784)) as [x0 Q0]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2800)) as [x1 Q1]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2808)) as [x2 Q2]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2816)) as [x3 Q3]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2872)) as [x4 Q4]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2880)) as [x5 Q5]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_tjunk_word (ly_T ly + 2904)) as [x9 Q9]; [unfold t_cache_stats; lia | unfold t_unwinding; lia |].
destruct (sv_cjunk_word (inst + o_comb_stats + 16)) as [x6 Q6]; [lia | lia |].
destruct (sv_cjunk_word (inst + o_comb_stats + 24)) as [x7 Q7]; [lia | lia |].
destruct (sv_sjunk_word bsl) as [x8 Q8]; [lia | lia |].
destruct (sv_sjunk_word (inst + o_sec_stats)) as [y1 P1]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (sv_sjunk_word (inst + o_sec_stats + 16)) as [y2 P2]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
destruct (sv_sjunk_word (inst + o_sec_stats + 24)) as [y3 P3]; [lia | unfold o_sec_stats, o_sec_mutex; lia |].
exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, y1, y2, y3. repeat (split; [assumption|]). exact P3.
Qed.
End v.
End a.
