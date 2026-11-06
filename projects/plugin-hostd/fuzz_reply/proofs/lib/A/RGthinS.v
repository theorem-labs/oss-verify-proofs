(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGg1.v (a working branch 29b7505aa27, file sha256 2b6258d6474c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 24 image addresses moved by code-verified function pairs (12 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 1 code pcs the tool read as sizes, by the internal file funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction, and 5 pcs named in comments; 12 hand maps (the internal file agreloc-resolve-A.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); 2 model labels (YG00 mcheck / spin tags) kept; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (4 lines name this file); 29 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's MP delta to proofs/cgif/cgif_file_fuzzer/lib/DGg1.v (84ee52cd012 -> a working branch 5ad50e61fc6a, file sha256 5842e5fc5f09) applied at A' by the 3-way merge of record (the internal file p2merge.sh: base = the 84ee52cd012 text relocated cgif -> A', theirs = the 5ad50e61fc6a text relocated the same way, ours = this file): the call rules take the call memory MP first, as lib/Reusable/MnEnq.v now does. 0 conflicts; the added lines equal the source delta's; no numeral in the delta. *)
(* Modified by Theorem Labs, 2026-10-30: the cf layer's dv_zone bound change (proofs/cgif/cgif_file_fuzzer/lib/DGg1.v at 8e0ff8e049b4 -> 002b8cc32f7e, the request bound `1 <= nn < 2 ^ 28` -> `<= 2 ^ 28`) applied at A' by the 3-way merge of record (the internal file p2merge.sh), as round 6h did for the B' copies; 0 conflicts; no numeral in the delta. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/DGg1.v, with its module paths and module names changed; 147 of its 198 lines of code are new or changed and 1046 lines of the source are left out. *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinS.v (commit 66a127cb11e, sha256 996d87044933; internal record, reply A text, no relocation) with the statement edits preset A5 made to its copy (a Theorem Labs lane, commit d0fcb396eee): RTlaws.rl_blk's size bound widened from MALLOC_MAX (= 2 ^ 28, YG00.v:41) to 2 ^ 30 (the cf instance's live blocks are below cf_malloc_max = 2 ^ 30 - 2 ^ 20, CfParamsReply.v:9) and RTlaws.rl_stack's lower bound ASAN_CEIL + 16 <= a weakened to ASAN_CEIL <= a (YG0f.v:337 lo_stk_ceil gives only ASAN_CEIL <= ly_stk_lo); both fields are implied by the old ones (weaker premises of the segments); module paths: lib.Reusable -> lib.A for AllocG DeallocG ReallocG RGtop. *)
(* fuzz_reply.asan: the invariants of the thin realloc segments, the allocator relation's laws they use, and
   generic memory lemmas.  The segments (RGthinS2a.v, RGthinS2b.v, RGthinS3.v, RGthinS4.v, RGthinS6.v) prove RGtop's seg_mid_a,
   seg_mid_b, seg_ret, seg_nret and seg_npost on this image with
     segs = tfibsegs (fuzz_reply.asan), inst = 0xa2a58, oomb = 0x128320, pc0 = 0x54328, pcM = 0x964cc,
     pcA = 0x31bd8, pcD = 0x318c4,
   for any allocator relation ARX / owned set AOX that satisfies [RTlaws] (cgif's [inst = TFIB_INST /\ AR]
   satisfies them: RTlawsAR.v), and the invariants [K1], [K2], [K3], [Kn] below, which the prefix segments
   (seg_pre, seg_npre) establish at the Allocate call sites.

   The frames (offsets from realloc's entry sp, measured on the image, RGthinK.v): the interceptor saves ra, s0..s6 at
   -8..-64 and moves sp to -2144; the BufferedStackTrace object is at -2136; asan_realloc saves ra = 0x54398 at
   -2152 (sp -2160); Reallocate saves ra = 0x325fc at -2168 and s0..s4 at -2176..-2208 (sp -2208). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ReallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGthinK.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YP03 YO0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The callee-saved registers, one goal per register (r = 2, 3, 4, 8, 9, 18..27), r rewritten to its literal. *)
Ltac to_lit r Hr :=
  first [ replace r with (2%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (3%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (4%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (8%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (9%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (18%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (19%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (20%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (21%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (22%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (23%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (24%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (25%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (26%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity)
        | replace r with (27%bv : bv 5) by (apply bv_eq; rewrite Hr; vm_compute; reflexivity) ].
Ltac cs_cases :=
  intros rk rr Hrk Hrr; unfold acallee_saved in Hrk;
  assert (Kc : rk = 2 \/ rk = 3 \/ rk = 4 \/ rk = 8 \/ rk = 9 \/ rk = 18 \/ rk = 19 \/ rk = 20 \/ rk = 21 \/ rk = 22 \/
    rk = 23 \/ rk = 24 \/ rk = 25 \/ rk = 26 \/ rk = 27) by lia; clear Hrk;
  destruct Kc as [Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|[Kc|Kc]]]]]]]]]]]]]];
  rewrite Kc in Hrr; to_lit rr Hrr; clear Hrr Kc.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Memory lemmas.                                                                                                    *)

Lemma val_mem_pw : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall x, m' x = m x) -> val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v E V k Hk. rewrite <- (V k Hk). unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_pw : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, m' x = m x) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. apply aview_same. apply E. Qed.
Lemma apresent_pw : forall (H : word -> bool) (m m' : word -> option byte) a,
(forall x, m' x = m x) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E P. apply (apresent_same H m m' a (E _) P). Qed.
Lemma val_mem_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E V k Hk. specialize (V k Hk). specialize (E k Hk). unfold aview in E. rewrite V in E. cbn in E.
destruct (mbyte tfibsegs (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate]. cbn in E. injection E as E.
f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_raw : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v E V k Hk. rewrite <- (V k Hk). unfold mbyte, mrestrict. rewrite (E k Hk). reflexivity. Qed.
Lemma apresent_vis : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma vis_apresent_hi : forall (H : word -> bool) (m : word -> option byte) a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exact (mbyte_high_apresent H m a b Ha E).
Qed.
(* The word at an 8-byte present address (copied from lib/A/AFfu.v:34-64). *)
Lemma aview_vis_byte : forall H mem a, aview tfibsegs H mem a <> None ->
exists b, aview tfibsegs H mem a = Some b /\ 0 <= b < 256 /\ mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 b).
Proof.
intros H mem a Hv. destruct (aview tfibsegs H mem a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exists b. split; [reflexivity|]. pose proof E as E'. apply aview_some in E as (b8 & Hb & <-).
pose proof (bv_unsigned_in_range 8 b8) as R. change (bv_modulus 8) with 256 in R. split; [lia|]. exact (aview_byte _ _ _ _ E').
Qed.
Lemma vis_word : forall H mem a, (forall i, 0 <= i < 8 -> aview tfibsegs H mem (a + i) <> None) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 w.
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
exists w. split; [subst w; lia|].
assert (LB : forall k, (k < 8)%nat -> YO0f.le_byte w 8 k = nth k [b0; b1; b2; b3; b4; b5; b6; b7] 0).
{ intros k Hk. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small w (2 ^ 64)) by (subst w; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
[ change (2 ^ (8 * 0)) with 1 | change (2 ^ (8 * 1)) with 256 | change (2 ^ (8 * 2)) with 65536 | change (2 ^ (8 * 3)) with 16777216
| change (2 ^ (8 * 4)) with 4294967296 | change (2 ^ (8 * 5)) with 1099511627776 | change (2 ^ (8 * 6)) with 281474976710656
| change (2 ^ (8 * 7)) with 72057594037927936 ]; subst w; Z.div_mod_to_equations; nia. }
intros k Hk. rewrite (LB k Hk). rewrite Z.add_0_r in M0.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; assumption.
Qed.
Lemma win_word : forall (H : word -> bool) (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> apresent H m (a + i)) -> exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H m) a 8 w.
Proof. intros H m a Hp. apply vis_word. intros i Hi. apply apresent_vis. exact (Hp i Hi). Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. destruct md. repeat split; reflexivity. Qed.
Lemma sbm_wvb : forall md mat, same_but_materialized md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_but_materialized. destruct md. reflexivity. Qed.
Lemma w64_unsigned : forall w : word, w64 (bv_unsigned w) = w.
Proof. intros w. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Lemma w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> w64 a = w64 b -> a = b.
Proof.
intros a b Ha Hb E. rewrite <- (YP03.unsigned_lit_small a Ha), <- (YP03.unsigned_lit_small b Hb). unfold w64 in E. rewrite E. reflexivity.
Qed.
Lemma ap_get : forall (regs regs' : bvmap 5 word) (k : Z) (r : bv 5),
aregs_preserved regs regs' -> acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r.
Proof.
intros regs regs' k r P Hk Hr. replace r with (Z_to_bv 5 k) by (subst k; apply Z_to_bv_bv_unsigned). apply P. exact Hk.
Qed.
Lemma ap_mk : forall (regs regs' : bvmap 5 word),
(forall k (r : bv 5), acallee_saved k -> bv_unsigned r = k -> getr regs' r = getr regs r) -> aregs_preserved regs regs'.
Proof.
intros regs regs' Hm k Hk. apply (Hm k); [exact Hk|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. unfold acallee_saved in Hk. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The laws of the allocator relation that the thin segments use.                                                    *)

Record RTlaws (B : asyms) (ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) : Prop := {
  (* a live block: bounds, outside the image, present, not owned, not errno, its chunk header *)
  rl_blk : forall ly S W mem md p n, ARX RT_INST ly S W mem md -> In (p, n) (blocks S) ->
    4096 + 16 <= sptr_addr B ly p /\ sptr_addr B ly p + req_size n <= ASAN_CEIL /\
    (sptr_addr B ly p <= 0x10000 \/ 0x5fb000 + 16 <= sptr_addr B ly p) /\ 0 <= n < 2 ^ 30 /\
    (forall x, sptr_addr B ly p <= x < sptr_addr B ly p + req_size n ->
      apresent (w_H W) mem x /\ ~ AOX ly S x /\ ~ (RT_ERRNO <= x < RT_ERRNO + 4)) /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 1 2 /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 14) 2 0 /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n);
  (* two live blocks are disjoint *)
  rl_disj : forall ly S W mem md p n q m, ARX RT_INST ly S W mem md -> In (p, n) (blocks S) -> In (q, m) (blocks S) -> p <> q ->
    sptr_addr B ly p + req_size n <= sptr_addr B ly q \/ sptr_addr B ly q + req_size m <= sptr_addr B ly p;
  (* a live block's address does not move when the layout grows *)
  rl_layout : forall ly S W mem md ly' p n, ARX RT_INST ly S W mem md -> layout_le (length (st_secs S)) ly ly' ->
    In (p, n) (blocks S) -> sptr_addr B ly' p = sptr_addr B ly p;
  (* the stack: above the allocator's ceiling, not owned *)
  rl_stack : forall ly S W mem md a, ARX RT_INST ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
    ~ AOX ly S a /\ ASAN_CEIL <= a;
  rl_stkhi : forall ly S W mem md, ARX RT_INST ly S W mem md -> ly_stk_hi ly <= kHighMemEnd;
  (* the RELRO slot of REAL(memcpy) and REAL(memcpy) itself *)
  rl_const : forall ly S W mem md, ARX RT_INST ly S W mem md ->
    val_mem tfibsegs (mrestrict (w_H W) mem) RT_GOT_M 8 RT_REAL_M /\ val_mem tfibsegs (mrestrict (w_H W) mem) RT_REAL_M 8 RT_PCM;
  (* writes to the stack, errno and live blocks keep the relation *)
  rl_write : forall ly S W mem md mem' md', ARX RT_INST ly S W mem md ->
    (forall x : word, ~ (ly_stk_lo ly <= bv_unsigned x < ly_stk_hi ly) -> ~ (RT_ERRNO <= bv_unsigned x < RT_ERRNO + 4) ->
      ~ (exists p n, In (p, n) (blocks S) /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) ->
    (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem' a <> None) ->
    same_but_materialized md md' -> ARX RT_INST ly S W mem' md'
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The invariants at the call sites (relative to realloc's entry registers [regs]).                                  *)

(* The interceptor's saved words and asan_realloc's return pc. *)
Definition rt_frames (regs : bvmap 5 word) (H : word -> bool) (m : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict H m) (spZ regs - 2152) 8 RT_RA_I /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 8) 8 (raZ regs) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
val_mem tfibsegs (mrestrict H m) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)).
(* gp, tp and s7..s11 as at realloc's entry. *)
Definition kregs (regs regsX : bvmap 5 word) : Prop :=
forall r : bv 5, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regsX r = getr regs r.
(* The BufferedStackTrace object at [so] and its buffer [bp] holding the trace [tr]. *)
Definition so_ok (ly : alayout) (H : word -> bool) (m : word -> option byte) (sp so bp : Z) (tr : list Z) : Prop :=
sp <= so /\ so + 16 <= ly_stk_hi ly /\ so mod 8 = 0 /\ sp <= bp /\ bp + 8 * 30 <= ly_stk_hi ly /\ bp mod 8 = 0 /\
(1 <= length tr <= 30)%nat /\
val_mem tfibsegs (mrestrict H m) so 8 bp /\ val_mem tfibsegs (mrestrict H m) (so + 8) 8 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H m) (bp + 8 * Z.of_nat i) 8 (nth i tr 0)).
(* The stack part of the layout is the entry's. *)
Definition stk_same (ly ly' : alayout) : Prop :=
ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\ ly_top ly' = ly_top ly.

Section b.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.

(* K1: at Reallocate's `jal Allocate` (0x32674; Allocate's entry, ra = 0x32678). *)
Definition K1r : K1_t tfibsegs := fun ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA =>
spZ regsA = spZ regs - 2208 /\ getr regsA 1 = w64 RT_RA_A /\ getr regsA 8 = w64 (spZ regs - 2136) /\
getr regsA 13 = w64 (spZ regs - 2136) /\
getr regsA 9 = getr regs 10 /\ getr regsA 18 = w64 RT_INST /\ getr regsA 19 = getr regs 11 /\ kregs regs regsA /\
rt_frames regs (w_H W1) memA /\ val_mem tfibsegs (mrestrict (w_H W1) memA) (spZ regs - 2168) 8 RT_RA_R /\
rwin tfibsegs regs W1 memA /\
(forall i, 0 <= i < req_size n_old ->
  aview tfibsegs (w_H W1) memA (sptr_addr B ly p + i) = aview tfibsegs (w_H W) mem (sptr_addr B ly p + i)).

(* K2: at Reallocate's `jalr a3` (0x326ec; REAL(memcpy)'s entry, ra = 0x326f0). *)
Definition K2r : K2_t tfibsegs := fun ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM =>
spZ regsM = spZ regs - 2208 /\ getr regsM 1 = w64 RT_RA_M /\ getr regsM 8 = w64 (spZ regs - 2136) /\
getr regsM 9 = getr regs 10 /\ getr regsM 18 = w64 RT_INST /\ getr regsM 20 = w64 (sptr_addr B ly2 q) /\ kregs regs regsM /\
rt_frames regs (w_H W3) memM /\ val_mem tfibsegs (mrestrict (w_H W3) memM) (spZ regs - 2168) 8 RT_RA_R /\
rwin tfibsegs regs W3 memM /\
ARX RT_INST ly2 S2 W3 memM mdM /\ sptr_addr B ly2 p = sptr_addr B ly p /\ In (q, n) (blocks S2) /\ stk_same ly ly2 /\
ly_bot ly < spZ regs - 2208 /\
(exists bp, so_ok ly2 (w_H W3) memM (spZ regs - 2208) (spZ regs - 2136) bp (call_trace ly RT_PC0 regs ch)).

(* K3: at Reallocate's `jal Deallocate` (0x32708; Deallocate's entry, ra = 0x3270c). *)
Definition K3r : K2_t tfibsegs := fun ly S W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD =>
spZ regsD = spZ regs - 2208 /\ getr regsD 1 = w64 RT_RA_D /\ getr regsD 20 = w64 (sptr_addr B ly2 q) /\ kregs regs regsD /\
rt_frames regs (w_H W4) memD /\ val_mem tfibsegs (mrestrict (w_H W4) memD) (spZ regs - 2168) 8 RT_RA_R /\
rwin tfibsegs regs W4 memD /\ stk_same ly ly2 /\ 4096 <= sptr_addr B ly2 q <= 2 ^ 47.

(* Kn: at asan_realloc's NULL-input `jal Allocate` (0x325d4; Allocate's entry, ra = 0x325d8). *)
Definition Knr : Kn_t tfibsegs := fun ly S W regs mem md n ch S1 W1 regsA memA mdA =>
spZ regsA = spZ regs - 2160 /\ getr regsA 1 = w64 RT_RA_NA /\ kregs regs regsA /\
rt_frames regs (w_H W1) memA /\ rwin tfibsegs regs W1 memA.
End b.
End a.
