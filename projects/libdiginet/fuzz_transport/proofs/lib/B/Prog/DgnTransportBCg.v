(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths and module names changed; 782 of its 853 lines of code are new or changed and 69 lines of the source are left out. *)
(* DgnTransportBCg: the definitions every program statement (lib/B/Prog/*_cg.v) of the pinned
   fuzz_transport.asan-ubsan image (sha256 41113a03c82f) shares.
   STATEMENTS and decided facts only: nothing here is a walk. Image B's twin of lib/A/Prog/DgnTransportCg.v: the same
   definitions, at image B's segments (lib/B/YB1v.v tfibsegs), runtime cells (lib/B/AsanCells.v), harness globals
   (lib/B/TransportGB.v G_HARNESS_B) and read-only bytes.
   - decode_utrace: the trace the allocator records at a call.
   - TRANS_RO_RD: the read-only bytes a walk, or a callee it passes their address to, reads through the image view: the
     jump tables of LLVMFuzzerTestOneInput's op switch and of notice's kind switch, four constant-pool words, and the
     payloads of the image's 22 registered read-only globals (15 in .rodata, 7 in .data.rel.ro). The .data.rel.ro
     ones lie in a writable PT_LOAD (the RELRO range [TRANS_RLO, TRANS_RHI), .data.rel.ro to the end of .got, the
     second disjunct of lib/B/YCeg.v in_ro_tfa), every other one in the read-only first PT_LOAD.
     trans_ro_rd_unowned / trans_rom_no_errno are the two facts about the record B that keep them visible through a
     journal.
   - transport_cells: the runtime cells the program reads, as constant cells of the record, and the shadow of the
     read-only globals' payloads (decode_zshadow_at for whole granules, a constant cell for the partial granule).
   - transport_leaf_at / transport_leaf_wr_at: a leaf statement of the kit lib/B/Prog/LeafCgKit.v read at this unit's
     model.
   - decode_twr_ok / decode_rd_ok / decode_off_win / decode_in_block / decode_in_fake: the write right a caller gives a
     callee for a range of its own frame, the facts that let a callee read a range that is not a heap block, "the range
     is outside the callee's stack window", and the two block / frame placements of a range.
   - trans_src_ok: where the bytes a callee reads may lie: a heap block of the caller, or (with decode_rd_ok) a caller's
     side-stack frame, a harness global (lib/B/TransportGB.v G_HARNESS_B; each byte in some range of it, and
     trans_src_ok_G_range for a range inside one global), the machine stack of the call state's layout
     [ly_stk_lo, ly_stk_hi), or TRANS_RO_RD. A harness-global or TRANS_RO_RD range also carries trans_sh_any: its
     shadow facts at every AR state (those shadow bytes are the runtime's own, so no caller keeps them; the record
     fixes them). The callee's own window is excluded by decode_off_win.
   - the walk lemmas over trans_src_ok: trans_src_ok_rd (decode_rd_ok in every case), trans_src_ok_place (where the
     range lies: below alloc_ceiling, or in the machine stack), trans_src_ok_sub / decode_off_win_sub (a sub-range),
     trans_src_ok_view (a later memory of the walk's own runs), trans_src_ok_inner (an inner call state),
     trans_src_ok_acall / trans_src_ok_acall_g (across a donor callee, YCbq.v acall_kept, and across a G-form callee,
     lib/A/Prog/TransportGCg.v acall_kept_g), trans_src_ok_disj_own (apart from a callee's new side-stack frame);
     the shadow lemmas stack_zshadow_ra (the machine stack), decode_zshadow_ra (a zero-shadow range of the record),
     decode_rd_ok_fake_kept (a side-stack frame whose shadow is kept); the G facts inG_G_HARNESS_hull,
     G_HARNESS_gx_ok, G_HARNESS_gx_noerrno. The forms that also carry an EMPTY range (0 <= n in place of 0 < n; the
     hull of an empty range at q is not empty unless q is on 64 bytes, trans_hull_in): trans_src_ok_sub_ge0,
     trans_src_ok_acall_ge0, trans_src_ok_acall_g_ge0, trans_src_ok_kept_ge0, decode_rd_ok_fake_kept_ge0,
     stack_zshadow_ra_ge0, trans_zrow_ra_ge0; each 0 < n lemma of the same name without _ge0 is its instance.
   - trans_out_ok: where the range a callee WRITES for its caller may lie (a caller's side-stack frame or a harness
     global, with decode_rd_ok), and trans_out_ok_far / trans_out_ok_sub.
   - decode_cg_post: what a caller-journal call leaves (the caller's journal extended, callee-saved registers kept, no
     side-stack frame added, the caller's blocks exactly, every byte outside the call's stack window and its written
     range E kept, the meter charged at most COST), with a statement-specific part X; decode_cg_post_dcg reads it as
     TransportGCg.v dcg_post, the callee post gx_call_cg takes.
   - the record facts trans_g_unowned / trans_g_no_errno (no G_HARNESS_B byte is an owned static or errno) and
     trans_gs_zshadow (g_s's payload is a zero-shadow range of the record), decided at the closing record.
   - frame_f_cells / frame_f_bytes / FRAME_F_SIZE: the 64 bytes of struct diginet_frame that diginet_frame_parse leaves
     (lib/Prog/diginet_frame_parse_c.v parse_cells); image-free, the model of libdiginet/fuzz_frame's walks of
     diginet_frame_parse and diginet_announce_parse. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The trace the allocator records at a call: the call's return address and the return addresses of the
   frame-pointer chain after it (YG00.v unwind_of_chain; YG0d.v call_trace at ras = raZ regs :: spine ch). *)
Definition decode_utrace (pc0 : Z) (ras : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) ras).

(* Every runtime cell of AsanCells.asan_cells lies inside one loaded segment of the image (decided by vm_compute). *)
Definition decode_seg_covers (a n : Z) : bool :=
  existsb (fun s : Segment => (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
    tfibsegs.
Definition decode_asan_cell_ranges : list (Z * Z) :=
  [(FCells.CELL_K, 8); (FCells.GOT_CELL_K, 8); (FCells.INITED, 1); (FCells.REPLACE, 1); (FCells.GOT_REPLACE, 8);
   (FCells.UAR, 4); (FCells.GOT_UAR, 8); (FCells.CANPOISON, 1); (FCells.HIEND, 8); (FCells.GOT_HIEND, 8);
   (FCells.MIDBEG, 8); (FCells.GOT_MIDBEG, 8); (FCells.MIDEND, 8); (FCells.GOT_MIDEND, 8); (FCells.REAL_MEMCPY, 8);
   (FCells.REAL_MEMSET, 8); (FCells.GOT_REAL_MEMSET, 8)].
Lemma decode_asan_cells_in_seg : forallb (fun r => decode_seg_covers (fst r) (snd r)) decode_asan_cell_ranges = true.
Proof. vm_compute. reflexivity. Qed.

(* The read-only bytes, as (base, size) ranges (in_zr, YG0n.v). The jump tables are compiler data with no
   asan_globals entry, read by plain `lw`: LLVMFuzzerTestOneInput's op switch (8 entries) and notice's kind switch
   (6 entries). The four constant-pool words are read by plain `ld` (two by LLVMFuzzerTestOneInput, one each by
   check_latest_sent and diginet_session_poll). The registered globals are read by instrumented loads
   (LLVMFuzzerTestOneInput.SCALE, op_frame.CMD / SRC / DST, op_announce.NAME, personalities), passed to __asan_memcpy,
   the bcmp interceptor or build_and_receive (HOST, DESK, SPEC_BCAST, SPEC_OUI, BROADCAST, the strings SPEC_C24 /
   SPEC_PC point to, __const.LLVMFuzzerTestOneInput.io), or reached through a pointer of a table above (DESK2, NOTDD,
   OTHER, the string .str.6 (TRANS_STR4), the two names personalities points to). Each size is the payload of the
   global's asan_globals descriptor. The names are image A's (lib/A/Prog/DgnTransportCg.v); TRANS_K_LLVMF2 and
   TRANS_K_SENT are image B's own. *)
Definition TRANS_JT_LLVMF : Z := 0x20f5c.
Definition TRANS_JT_NOTICE : Z := 0x20f7c.
Definition TRANS_K_LLVMF : Z := 0x10310.
Definition TRANS_K_LLVMF2 : Z := 0x103a8.
Definition TRANS_K_SENT : Z := 0x10338.
Definition TRANS_K_POLL : Z := 0x10360.
Definition TRANS_SCALE : Z := 0x20fa0.
Definition TRANS_HOST : Z := 0x20fe0.
Definition TRANS_DESK : Z := 0x21000.
Definition TRANS_SPEC_BCAST : Z := 0x21020.
Definition TRANS_SPEC_OUI : Z := 0x21040.
Definition TRANS_STR_C24 : Z := 0x21060.
Definition TRANS_STR_PC : Z := 0x21080.
Definition TRANS_CMD : Z := 0x210a0.
Definition TRANS_DESK2 : Z := 0x210c0.
Definition TRANS_NOTDD : Z := 0x210e0.
Definition TRANS_OTHER : Z := 0x21100.
Definition TRANS_STR4 : Z := 0x21120.
Definition TRANS_BROADCAST : Z := 0x21160.
Definition TRANS_PNAME0 : Z := 0x211a0.
Definition TRANS_PNAME1 : Z := 0x211c0.
Definition TRANS_IO : Z := 0xa39c0.
Definition TRANS_SPEC_C24 : Z := 0xa3a00.
Definition TRANS_SPEC_PC : Z := 0xa3a20.
Definition TRANS_SRC : Z := 0xa3a40.
Definition TRANS_DST : Z := 0xa3a80.
Definition TRANS_NAME : Z := 0xa3ac0.
Definition TRANS_PERS : Z := 0xa3b00.
(* The registered read-only globals, (base, payload size). *)
Definition TRANS_RO_GLOBALS : list (Z * Z) :=
  [(TRANS_SCALE, 32); (TRANS_HOST, 6); (TRANS_DESK, 6); (TRANS_SPEC_BCAST, 6); (TRANS_SPEC_OUI, 3);
   (TRANS_STR_C24, 9); (TRANS_STR_PC, 9); (TRANS_CMD, 7); (TRANS_DESK2, 6); (TRANS_NOTDD, 6); (TRANS_OTHER, 6);
   (TRANS_STR4, 6); (TRANS_BROADCAST, 6); (TRANS_PNAME0, 9); (TRANS_PNAME1, 9);
   (TRANS_IO, 32); (TRANS_SPEC_C24, 16); (TRANS_SPEC_PC, 16); (TRANS_SRC, 32); (TRANS_DST, 32); (TRANS_NAME, 24);
   (TRANS_PERS, 48)].
Definition TRANS_RO_RD : list (Z * Z) :=
  [(TRANS_JT_LLVMF, 32); (TRANS_JT_NOTICE, 24); (TRANS_K_LLVMF, 8); (TRANS_K_LLVMF2, 8); (TRANS_K_SENT, 8);
   (TRANS_K_POLL, 8)] ++ TRANS_RO_GLOBALS.
(* The RELRO range of the pinned fuzz_transport.asan-ubsan image (sha256 41113a03c82f): .data.rel.ro (sh_addr 0xa35e0)
   to the end of .got (sh_addr 0xa3c90 + sh_size 0xd58 = 0xa49e8). *)
Definition TRANS_RLO : Z := 0xa35e0.
Definition TRANS_RHI : Z := 0xa49e8.
Definition trans_in_ro_rd (a : Z) : Prop := Exists (in_zr a) TRANS_RO_RD.
(* The image view at the TRANS_RO_RD bytes only: rom_view (YG0d.v) scoped to what the walks read, the RELRO bytes
   included (arodata_okS, YE01.v, at [TRANS_RLO, TRANS_RHI)). *)
Definition trans_rom_view_rd (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  forall a, trans_in_ro_rd a ->
    aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).

(* Every TRANS_RO_RD byte lies in a non-writable loaded segment or in [TRANS_RLO, TRANS_RHI), and the image holds a
   byte there (decided by vm_compute). *)
Definition decode_rom_b (a : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                             (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.
Definition trans_relro_b (a : Z) : bool := ((TRANS_RLO <=? a) && (a <? TRANS_RHI))%bool.
Definition decode_img_b (a : Z) : bool :=
  match YK11.seg_rom tfibsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition decode_zr_bytes (r : Z * Z) : list Z := map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r))).
Lemma trans_ro_rd_clean :
  forallb (fun r => forallb (fun z => (decode_rom_b z || trans_relro_b z) && decode_img_b z)%bool (decode_zr_bytes r))
    TRANS_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma decode_zr_enum (P : Z -> bool) (Lr : list (Z * Z)) (a : Z) :
  forallb (fun r => forallb P (decode_zr_bytes r)) Lr = true -> Exists (in_zr a) Lr -> P a = true.
Proof.
  intros HF HE. apply Exists_exists in HE as [r [Hin [H1 H2]]].
  rewrite forallb_forall in HF. specialize (HF r Hin). rewrite forallb_forall in HF.
  apply HF. unfold decode_zr_bytes. apply in_map_iff. exists (Z.to_nat (a - fst r)). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.
Lemma decode_rom_b_in_rom (a : Z) : decode_rom_b a = true -> in_rom tfibsegs a.
Proof.
  unfold decode_rom_b, in_rom. intro H. apply existsb_exists in H as [sg [Hin H]].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists sg. repeat split; auto; lia.
Qed.
Lemma trans_relro_b_range (a : Z) : trans_relro_b a = true -> TRANS_RLO <= a < TRANS_RHI.
Proof. unfold trans_relro_b. intro H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.
Lemma decode_img_b_some (a : Z) :
  decode_img_b a = true -> exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  unfold decode_img_b. destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; intro H;
    [exists b; reflexivity | discriminate H].
Qed.
Lemma trans_ro_rd_rom_clean (a : Z) :
  trans_in_ro_rd a -> (in_rom tfibsegs a \/ TRANS_RLO <= a < TRANS_RHI) /\
    exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  intro H. pose proof (decode_zr_enum _ _ a trans_ro_rd_clean H) as HP.
  cbv beta in HP. apply andb_true_iff in HP as [HR HI]. split; [|exact (decode_img_b_some a HI)].
  apply orb_true_iff in HR as [HR|HR]; [left; exact (decode_rom_b_in_rom a HR) | right; exact (trans_relro_b_range a HR)].
Qed.

(* The two instance facts about the record B (rows of the closing file, decided at the concrete record): no
   TRANS_RO_RD byte is an owned static (the record owns the read-only globals' redzones, not their payloads), and
   errno is neither in the read-only image nor in [TRANS_RLO, TRANS_RHI). *)
Definition trans_ro_rd_unowned (B : asyms) : Prop :=
  forall a, trans_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B).
Definition trans_rom_no_errno (B : asyms) : Prop :=
  forall a, (in_rom tfibsegs a \/ TRANS_RLO <= a < TRANS_RHI) -> ~ (as_errno B <= a < as_errno B + 4).
(* From them, the scoped fact the journal's image clause (YCbq.v ajournal) and arodata_okS (YE01.v) need at each
   TRANS_RO_RD byte. *)
Lemma trans_ro_rd_scoped (B : asyms) : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall a, trans_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros HO HE a H. destruct (trans_ro_rd_rom_clean a H) as [HR _]. split.
  - exact (HO a H).
  - exact (HE a HR).
Qed.

(* A value-0 shadow range [lo, hi) of unowned image bytes as a fact of the record: it lies inside a range of
   as_zero_shadow B (YG0f.v; the record's Tfib_zero_shadow), whose shadow ARm's am_zshadow (YG0n.v zshadow_ok) reads
   as 0 at every AR state; decode_zshadow_rd is that read at one granule. *)
Definition decode_zshadow_at (B : asyms) (lo hi : Z) : Prop :=
  exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= lo /\ hi <= fst r + snd r.
Lemma decode_zshadow_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (lo hi T : Z) :
  @AR rc tfibsegs B ly S W mem md -> T mod 8 = 0 -> lo <= T -> T + 8 <= hi -> decode_zshadow_at B lo hi ->
  aview tfibsegs (w_H W) mem (FCells.shadow_addr T) = Some 0.
Proof.
  intros [M _] HT Hlo Hhi (r & Hin & H8 & H1 & H2).
  pose proof (am_zshadow _ _ _ _ M) as Z. unfold zshadow_ok in Z. rewrite Forall_forall in Z.
  assert (Hr : In r (zero_shadow_ranges B ly)) by (unfold zero_shadow_ranges; right; exact Hin).
  specialize (Z r Hr). hnf in Z.
  assert (Ea : fst r = 8 * (fst r / 8)) by (pose proof (Z.div_mod (fst r) 8 ltac:(lia)); lia).
  assert (Et : T = 8 * (T / 8)) by (pose proof (Z.div_mod T 8 ltac:(lia)); lia).
  assert (Ei : (T - fst r) / 8 = T / 8 - fst r / 8).
  { replace (T - fst r) with ((T / 8 - fst r / 8) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hs : T / 8 - fst r / 8 + 1 <= snd r / 8) by (apply Z.div_le_lower_bound; lia).
  specialize (Z ((T - fst r) / 8) ltac:(rewrite Ei; lia)).
  replace (FCells.shadow_addr T) with (shadow_of_addr SHADOW_OFF (fst r) + (T - fst r) / 8); [exact Z|].
  rewrite Ei. unfold shadow_of_addr, FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. lia.
Qed.

(* A reader that gives 0 at the shadow byte of every granule of [lo, hi) gives a range whose 64-byte blocks lie in
   [lo, hi) its two shadow facts: every byte addressable (its granule's shadow byte is 0) and every shadow byte of its
   hull (YG0d.v shadow_hull_vis) visible. The range may be empty: the hull of an empty range is empty when q is on 64
   bytes, else the 8 shadow bytes of q's 64-byte block. *)
Lemma trans_zrow_ra_ge0 (rd : Z -> option Z) (lo hi q n : Z) :
  (forall T, T mod 8 = 0 -> lo <= T -> T + 8 <= hi -> rd (shadow_addr T) = Some 0) ->
  0 <= n -> lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable rd SHADOW_OFF q n /\ shadow_hull_vis rd q n.
Proof.
  intros HZ Hn Hlo Hhi.
  pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr (x / 8 * 8))
      by (unfold shadow_of_addr, shadow_addr; rewrite Z.div_mul by lia; reflexivity).
    apply HZ; [apply Z_mod_mult | lia | lia].
  - intros s Hs.
    assert (ES : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
    rewrite <- ES. rewrite (HZ _ (Z_mod_mult _ _)); [discriminate | |].
    all: unfold shadow_addr, SHADOW_OFF in Hs |- *.
    all: pose proof (Z.div_mod q 8 ltac:(lia)); pose proof (Z.mod_pos_bound q 8 ltac:(lia));
      pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)); lia.
Qed.
Lemma trans_zrow_ra (rd : Z -> option Z) (lo hi q n : Z) :
  (forall T, T mod 8 = 0 -> lo <= T -> T + 8 <= hi -> rd (shadow_addr T) = Some 0) ->
  0 < n -> lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable rd SHADOW_OFF q n /\ shadow_hull_vis rd q n.
Proof. intros HZ Hn. exact (trans_zrow_ra_ge0 rd lo hi q n HZ (Z.lt_le_incl _ _ Hn)). Qed.

(* G / RO: a range whose 64-byte blocks lie in a zero-shadow range of the record has its two shadow facts at every AR
   state (decode_zshadow_rd at each granule). *)
Lemma decode_zshadow_ra {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (lo hi q n : Z) :
  @AR rc tfibsegs B ly S W mem md -> decode_zshadow_at B lo hi -> 0 < n ->
  lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) q n.
Proof.
  intros HAR HZ Hn Hlo Hhi. apply (trans_zrow_ra _ lo hi q n); [|exact Hn | exact Hlo | exact Hhi].
  intros T HT H1 H2.
  replace (shadow_addr T) with (FCells.shadow_addr T)
    by (unfold FCells.shadow_addr, FCells.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  exact (decode_zshadow_rd B ly S W mem md lo hi T HAR HT H1 H2 HZ).
Qed.

(* The machine stack: zero_shadow_ranges (YG0n.v) puts [ly_stk_lo, ly_stk_hi) first and ARm's am_zshadow reads its
   shadow as 0 at every AR state; both bounds are page-aligned (layout_ok lo_top). So a range of the machine stack, empty
   or not, has its two shadow facts at every AR state. *)
Lemma stack_zshadow_ra_ge0 {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (q n : Z) :
  @AR rc tfibsegs B ly S W mem md -> 0 <= n -> ly_stk_lo ly <= q -> q + n <= ly_stk_hi ly ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) q n.
Proof.
  intros HAR Hn Hlo Hhi. destruct HAR as (M & _).
  pose proof (am_layout _ _ _ _ M) as LO. pose proof (lo_top _ LO) as (_ & _ & _ & _ & Hlo4 & Hhi4 & _).
  pose proof (am_zshadow _ _ _ _ M) as HZs. unfold zshadow_ok in HZs. rewrite Forall_forall in HZs.
  specialize (HZs (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(left; reflexivity)). hnf in HZs.
  cbn [fst snd] in HZs. unfold page_aligned in Hlo4, Hhi4.
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)). pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)).
  apply (trans_zrow_ra_ge0 _ (ly_stk_lo ly) (ly_stk_hi ly) q n); [| exact Hn | |].
  - intros T HT H1 H2.
    pose proof (Z.div_mod T 8 ltac:(lia)).
    pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ly_stk_lo ly) 8 ltac:(lia)).
    pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
    specialize (HZs (T / 8 - ly_stk_lo ly / 8) ltac:(lia)). unfold shadow_of_addr in HZs.
    replace (shadow_addr T) with (SHADOW_OFF + ly_stk_lo ly / 8 + (T / 8 - ly_stk_lo ly / 8))
      by (unfold shadow_addr; lia).
    exact HZs.
  - pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)). lia.
  - pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)). lia.
Qed.
Lemma stack_zshadow_ra {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (q n : Z) :
  @AR rc tfibsegs B ly S W mem md -> 0 < n -> ly_stk_lo ly <= q -> q + n <= ly_stk_hi ly ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) q n.
Proof. intros HAR Hn. exact (stack_zshadow_ra_ge0 B ly S W mem md q n HAR (Z.lt_le_incl _ _ Hn)). Qed.

(* The hull of a sub-range lies in the hull of the range. *)
Lemma trans_hull_sub (rd : Z -> option Z) (q n q' n' : Z) :
  shadow_hull_vis rd q n -> q <= q' -> q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros Hh H1 H2 s Hs. apply Hh.
  assert (A1 : shadow_addr q / 8 * 8 <= shadow_addr q' / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (A2 : shadow_addr (q' + n' - 1) / 8 * 8 <= shadow_addr (q + n - 1) / 8 * 8)
    by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; [lia|];
        unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  lia.
Qed.

(* The hull of a range, empty or not, inside a range [lo, hi) whose ends are on 64 bytes is made of shadow bytes of
   granules of [lo, hi) (the form of YG0s.v hull_inside, which takes 1 <= n). *)
Lemma trans_hull_in (lo hi q n s : Z) :
  lo mod 64 = 0 -> hi mod 64 = 0 -> lo <= q -> q + n <= hi -> 0 <= n ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 ->
  exists g, g mod 8 = 0 /\ lo <= g /\ g + 8 <= hi /\ s = shadow_addr g.
Proof.
  intros Hlo Hhi H1 H2 Hn Hs. exists ((s - SHADOW_OFF) * 8).
  assert (ES : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
  split; [apply Z_mod_mult|]. split; [|split; [|exact (eq_sym ES)]].
  all: unfold shadow_addr, SHADOW_OFF in Hs |- *.
  all: pose proof (Z.div_mod lo 64 ltac:(lia)); pose proof (Z.div_mod hi 64 ltac:(lia));
    pose proof (Z.div_mod q 8 ltac:(lia)); pose proof (Z.mod_pos_bound q 8 ltac:(lia));
    pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia));
    pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia));
    pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia));
    pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)); lia.
Qed.

(* Every TRANS_RO_RD byte lies in [4096, 0xa4000) (decided by vm_compute). *)
Lemma trans_ro_rd_bounds (a : Z) : trans_in_ro_rd a -> 4096 <= a < 0xa4000.
Proof.
  intro H.
  pose proof (decode_zr_enum (fun z => (4096 <=? z) && (z <? 0xa4000))%bool TRANS_RO_RD a
    ltac:(vm_compute; reflexivity) H) as E.
  cbv beta in E. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(* A byte of a range list each of whose ranges lies inside one loaded segment is an image byte; every range of
   G_HARNESS_B and of TRANS_RO_RD lies inside one loaded segment (decided by vm_compute). *)
Lemma decode_seg_covers_img (L : list (Z * Z)) (a : Z) :
  forallb (fun r => decode_seg_covers (fst r) (snd r)) L = true -> Exists (in_zr a) L -> in_img tfibsegs a.
Proof.
  intros HF HE. apply Exists_exists in HE as [r [Hin Hr]].
  rewrite forallb_forall in HF. specialize (HF r Hin). unfold decode_seg_covers in HF.
  apply existsb_exists in HF as [sg [Hsg H]]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_zr in Hr.
  exists sg. split; [exact Hsg | lia].
Qed.
Lemma trans_g_covers : forallb (fun r => decode_seg_covers (fst r) (snd r)) TransportGB.G_HARNESS_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma trans_ro_covers : forallb (fun r => decode_seg_covers (fst r) (snd r)) TRANS_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma trans_g_img (a : Z) : W_journalG.inG TransportGB.G_HARNESS_B a -> in_img tfibsegs a.
Proof. exact (decode_seg_covers_img _ a trans_g_covers). Qed.
Lemma trans_ro_img (a : Z) : trans_in_ro_rd a -> in_img tfibsegs a.
Proof. exact (decode_seg_covers_img _ a trans_ro_covers). Qed.

(* A byte of G_HARNESS_B lies in its hull [G_HARNESS_B_LO, G_HARNESS_B_HI) (lib/B/TransportGB.v
   G_HARNESS_B_in_hull). *)
Lemma inG_G_HARNESS_hull (a : Z) : W_journalG.inG TransportGB.G_HARNESS_B a ->
  TransportGB.G_HARNESS_B_LO <= a < TransportGB.G_HARNESS_B_HI.
Proof.
  intro Ha. unfold W_journalG.inG in Ha. apply Exists_exists in Ha as (r & Hr & Ha).
  pose proof (TransportGB.G_HARNESS_B_in_hull r Hr). unfold in_zr in Ha. lia.
Qed.

(* The G instance facts about the record B (rows of the closing file, decided at the concrete record: the record's
   owned statics hold the globals' redzones, not their payloads, lib/B/YF0m.v Tfib_owned_static; errno, TFIB_ERRNO,
   lies outside G_HARNESS_B): no byte of G_HARNESS_B is an owned static, and none is errno. With them G_HARNESS_B is a
   G of
   lib/A/W_journalG.v (gx_ok) and of lib/A/Prog/TransportGCg.v (gx_noerrno). *)
Definition trans_g_unowned (B : asyms) : Prop :=
  forall a, W_journalG.inG TransportGB.G_HARNESS_B a -> ~ Exists (in_zr a) (as_owned_static B).
Definition trans_g_no_errno (B : asyms) : Prop :=
  forall a, W_journalG.inG TransportGB.G_HARNESS_B a -> ~ (as_errno B <= a < as_errno B + 4).
Lemma G_HARNESS_gx_ok (B : asyms) : trans_g_unowned B -> W_journalG.gx_ok tfibsegs B TransportGB.G_HARNESS_B.
Proof. intros HU a Ha. split; [exact (trans_g_img a Ha) | exact (HU a Ha)]. Qed.
Lemma G_HARNESS_gx_noerrno (B : asyms) : trans_g_no_errno B -> TransportGCg.gx_noerrno B TransportGB.G_HARNESS_B.
Proof. intro H. exact H. Qed.

(* g_s (lib/B/TransportGB.v: (0x5df640, 18264), 2283 whole granules) is a zero-shadow range of the record B: a fact of
   the closing file, decided there by the record's row of Tfib_zero_shadow (lib/B/YF0m.v, TransportSyms ts_zsh) that
   holds [0x5df640, 0x5e3d98) (its asan_globals descriptor: size 18264, size_with_redzone 0x5920). With
   trans_sh_any_zshadow it gives trans_sh_any of a range whose 64-byte blocks lie in g_s (dmac = g_s + 120 and
   smac = g_s + 0, the 6-byte MACs send_control and send_data pass to diginet_frame_build). *)
Definition trans_gs_zshadow (B : asyms) : Prop := decode_zshadow_at B 0x5df640 (0x5df640 + 18264).

(* The runtime cells the program reads, as constant cells of the record B: as_const (YG0f.v) is re-read at every AR
   state (YG0n.v ARm am_const), so a walk reads them after any call. Rows 1-17 are AsanCells.asan_cells
   (lib/B/AsanCells.v) in its order, with its widths and values; each is a row of the record (lib/B/YF0m.v
   Tfib_const_abs).
   Rows 18-43: the shadow of the payload of each registered read-only global, in address order: the shadow bytes of its
   whole granules are 0 (a range of as_zero_shadow B, read through decode_zshadow_rd), and the shadow byte of its last,
   partial granule is the number of payload bytes in it (a row of the record's Tfib_const_shadow). *)
Definition transport_cells (B : asyms) : Prop :=
  forall ly,
    In (z8 (ANum FCells.CELL_K) FCells.ASAN_K) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_CELL_K) FCells.CELL_K) (as_const B ly) /\
    In (z1 (ANum FCells.INITED) 1) (as_const B ly) /\
    In (z1 (ANum FCells.REPLACE) 1) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_REPLACE) FCells.REPLACE) (as_const B ly) /\
    In (z4 (ANum FCells.UAR) 1) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_UAR) FCells.UAR) (as_const B ly) /\
    In (z1 (ANum FCells.CANPOISON) 1) (as_const B ly) /\
    In (z8 (ANum FCells.HIEND) 0x7fffffffffff) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_HIEND) FCells.HIEND) (as_const B ly) /\
    In (z8 (ANum FCells.MIDBEG) 0) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_MIDBEG) FCells.MIDBEG) (as_const B ly) /\
    In (z8 (ANum FCells.MIDEND) 0) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_MIDEND) FCells.MIDEND) (as_const B ly) /\
    In (z8 (ANum FCells.REAL_MEMCPY) FCells.MUSL_MEMCPY) (as_const B ly) /\
    In (z8 (ANum FCells.REAL_MEMSET) FCells.MUSL_MEMSET) (as_const B ly) /\
    In (z8 (ANum FCells.GOT_REAL_MEMSET) FCells.REAL_MEMSET) (as_const B ly) /\
    decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_HOST)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_DESK)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_SPEC_BCAST)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_SPEC_OUI)) 3) (as_const B ly) /\
    decode_zshadow_at B TRANS_STR_C24 (TRANS_STR_C24 + 8) /\
    In (z1 (ANum (FCells.shadow_addr (TRANS_STR_C24 + 8))) 1) (as_const B ly) /\
    decode_zshadow_at B TRANS_STR_PC (TRANS_STR_PC + 8) /\
    In (z1 (ANum (FCells.shadow_addr (TRANS_STR_PC + 8))) 1) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_CMD)) 7) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_DESK2)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_NOTDD)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_OTHER)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_STR4)) 6) (as_const B ly) /\
    In (z1 (ANum (FCells.shadow_addr TRANS_BROADCAST)) 6) (as_const B ly) /\
    decode_zshadow_at B TRANS_PNAME0 (TRANS_PNAME0 + 8) /\
    In (z1 (ANum (FCells.shadow_addr (TRANS_PNAME0 + 8))) 1) (as_const B ly) /\
    decode_zshadow_at B TRANS_PNAME1 (TRANS_PNAME1 + 8) /\
    In (z1 (ANum (FCells.shadow_addr (TRANS_PNAME1 + 8))) 1) (as_const B ly) /\
    decode_zshadow_at B TRANS_IO (TRANS_IO + 32) /\
    decode_zshadow_at B TRANS_SPEC_C24 (TRANS_SPEC_C24 + 16) /\
    decode_zshadow_at B TRANS_SPEC_PC (TRANS_SPEC_PC + 16) /\
    decode_zshadow_at B TRANS_SRC (TRANS_SRC + 32) /\
    decode_zshadow_at B TRANS_DST (TRANS_DST + 32) /\
    decode_zshadow_at B TRANS_NAME (TRANS_NAME + 24) /\
    decode_zshadow_at B TRANS_PERS (TRANS_PERS + 48).

Section leaf. Context {rc : YM05.RunCeil}.
Variable B : asyms.
(* A leaf statement of lib/B/Prog/<leaf>_cg.v, closed over the Section Variables of the shared kit
   lib/B/Prog/LeafCgKit.v (world .. as_tp), read at this unit's allocator model, image B's segments and the record
   B. *)
Definition transport_leaf_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
(* A leaf that writes a range of its caller also takes aowned, for the kit's premise `forall x, in_wr WR x -> ~ aowned
   ly S x /\ ~ in_img x` (LeafCgKit.v leaf_cg_of_evtF_stmt): the range is inside its caller's live side-stack
   frame. A byte of a live frame is an aclient_byte (YG0n.v), so it is never aowned, and AR_laws' al_client_img
   (YG0d.v) keeps it out of the image. *)
Definition transport_leaf_wr_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> (alayout -> astate -> Z -> Prop) -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B).
End leaf.

Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.

(* The caller's right to let a callee write [q, q + n): every byte is one the caller's journal may change (awr_byte,
   YCbq.v: in the caller's stack window, a heap byte of its footprint, a block allocated since the journal's start, or
   a byte of a side-stack frame in the journal's own list), present, not the runtime's own, and not in the ESTACK
   bytes below sp. *)
Definition decode_twr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
    (sp q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
    apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp).

(* A range [q, q + n) a callee reads that is not one of the caller's heap blocks: every byte visible, the range
   addressable in the shadow map and its shadow bytes visible (what aintrin_realizes / abcmp_realizes and the
   instrumented checks need, YG0d.v), in application memory. *)
Definition decode_rd_ok (W : world segs) (memc : word -> option byte) (q n : Z) : Prop :=
  (forall a, q <= a < q + n -> aview segs (w_H W) memc a <> None) /\
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n /\
  shadow_hull_vis (aview segs (w_H W) memc) q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.

(* The range [q, q + n) lies outside the callee's stack window [sp - FSTK, sp). *)
Definition decode_off_win (regs : bvmap 5 word) (FSTK q n : Z) : Prop :=
  q + n <= spZ regs - FSTK \/ spZ regs <= q.

(* [q, q + n) lies inside one of the caller's heap blocks. *)
Definition decode_in_block (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= q /\ q + n <= bA + nA.

(* [q, q + n) lies inside one of the caller's live side-stack frames. A callee that writes a range of its caller's
   frame needs this besides decode_twr_ok: acall_kept (YCbq.v) keeps every byte at or above alloc_ceiling outside the
   call's stack window whatever the written range is, and the image bytes outside the owned statics and errno; a byte
   of a frame of Sc lies below alloc_ceiling (AR_sep_law) and outside the image (AR_client_img_law), and acall_kept
   keeps it only outside the written range. *)
Definition decode_in_fake (lyc : alayout) (Sc : astate) (q n : Z) : Prop :=
  exists cid pos, In (cid, pos) (frames Sc) /\
    frame_addr lyc cid pos <= q /\ q + n <= frame_addr lyc cid pos + fs_frame_bytes cid.

(* decode_rd_ok of a sub-range: each conjunct restricts. *)
Lemma trans_rd_ok_sub : forall (W : world segs) (memc : word -> option byte) (q n q' n' : Z),
  decode_rd_ok W memc q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' -> decode_rd_ok W memc q' n'.
Proof.
  intros W memc q n q' n' (Hv & Ha & Hh & Hm & H0 & H63) H1 H2 H3.
  split; [intros a Ha'; apply Hv; lia|].
  split; [exact (range_addressable_sub _ _ q n q' n' Ha H1 H2)|].
  split; [exact (trans_hull_sub _ q n q' n' Hh H1 H2)|].
  split; [unfold amem_range in *; lia|]. split; lia.
Qed.

(* decode_rd_ok at a later memory whose view keeps the range's bytes and every byte of the shadow band
   [kLowMemEnd, kHighShadowEnd) (amem_range puts the range's shadow bytes and its hull there). *)
Lemma trans_rd_ok_view : forall (W W2 : world segs) memc mem2 q n,
  decode_rd_ok W memc q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  decode_rd_ok W2 mem2 q n.
Proof.
  intros W W2 memc mem2 q n (R1 & R2 & R3 & R4 & R5 & R6) K1 K2.
  assert (Hq : q + n <= kHighMemEnd - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  unfold kHighMemEnd in Hq.
  split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
  - intros a Ha. rewrite (K1 a Ha). exact (R1 a Ha).
  - intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite K2; [exact Hs|]. unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
  - intros s Hs. rewrite K2; [exact (R3 s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
    unfold kLowMemEnd, kHighShadowEnd.
    pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
    pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

(* decode_rd_ok at a later memory from the range's bytes kept and its two shadow facts there. *)
Lemma trans_rd_ok_sh : forall (W W2 : world segs) memc mem2 q n,
  decode_rd_ok W memc q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q n -> shadow_hull_vis (aview segs (w_H W2) mem2) q n ->
  decode_rd_ok W2 mem2 q n.
Proof.
  intros W W2 memc mem2 q n (R1 & _ & _ & R4 & R5 & R6) K1 Ha Hh.
  split; [intros a Hx; rewrite (K1 a Hx); exact (R1 a Hx)|]. exact (conj Ha (conj Hh (conj R4 (conj R5 R6)))).
Qed.

(* decode_off_win of a sub-range. *)
Lemma decode_off_win_sub : forall regs FSTK q n q' n',
  decode_off_win regs FSTK q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' -> decode_off_win regs FSTK q' n'.
Proof. intros regs FSTK q n q' n' H H1 H2 H3. unfold decode_off_win in *. lia. Qed.

(* The machine stack lies at or above alloc_ceiling and below 2 ^ 47 (layout_ok lo_stk_ceil, lo_top). *)
Lemma trans_stk_bounds : forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md ->
  alloc_ceiling <= ly_stk_lo ly /\ ly_stk_hi ly <= 2 ^ 47.
Proof.
  intros ly S W mem md (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (_ & _ & _ & Hhi & _). pose proof (lo_stk_ceil _ LO) as Hce.
  unfold ASAN_CEIL, kHighMemEnd in *. lia.
Qed.

(* [q, q + n)'s two shadow facts at every AR state. A harness-global or TRANS_RO_RD range carries it in trans_src_ok
   and trans_out_ok: its shadow bytes are the runtime's own (the record's zero-shadow rows and constant shadow cells,
   YG0n.v ARm am_zshadow / am_const), so no ajournal or acall_kept clause keeps them across a call, while AR fixes
   them. A caller proves it from the record (trans_sh_any_zshadow for a zero-shadow range). *)
Definition trans_sh_any (q n : Z) : Prop :=
  forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H W) mem) q n.

(* Where the bytes [q, q + n) a callee READS may lie: in a heap block of the caller, or, with decode_rd_ok, in a
   caller's side-stack frame, in a harness global (with trans_sh_any), in the machine stack of the call state's layout
   (a caller's machine frame, at any depth: [ly_stk_lo, ly_stk_hi) is the same at every state of the run, YG0f.v
   layout_le), or in TRANS_RO_RD (with trans_sh_any; LLVMFuzzerTestOneInput passes SPEC_BCAST and DESK to
   build_and_receive). The callee's own window is excluded by decode_off_win. *)
Definition trans_src_ok (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (q n : Z) : Prop :=
  decode_in_block lyc Sc q n \/
  ((decode_in_fake lyc Sc q n \/
    ((forall a, q <= a < q + n -> W_journalG.inG TransportGB.G_HARNESS_B a) /\ trans_sh_any q n) \/
    (ly_stk_lo lyc <= q /\ q + n <= ly_stk_hi lyc) \/
    ((forall a, q <= a < q + n -> trans_in_ro_rd a) /\ trans_sh_any q n)) /\
   decode_rd_ok W memc q n).

(* The G case of trans_src_ok for a range inside one harness global's payload. *)
Lemma trans_src_ok_G_range (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
    (q n g gn : Z) :
  In (g, gn) TransportGB.G_HARNESS_B -> g <= q -> q + n <= g + gn -> trans_sh_any q n -> decode_rd_ok W memc q n ->
  trans_src_ok lyc Sc W memc q n.
Proof.
  intros Hin H1 H2 Hsh Hrd. right. split; [|exact Hrd]. right. left. split; [|exact Hsh].
  intros a Ha. unfold W_journalG.inG. apply Exists_exists. exists (g, gn). split; [exact Hin|]. unfold in_zr. cbn. lia.
Qed.

(* The empty range at 0 (send_control's body NULL with length 0 to diginet_frame_build, and on to
   diginet_body_check): the G case holds vacuously (the hull of [0, 0) is empty: shadow_addr 0 / 8 * 8 =
   shadow_addr (-1) / 8 * 8 + 8). *)
Lemma trans_src_ok_null : forall lyc Sc (W : world segs) memc, trans_src_ok lyc Sc W memc 0 0.
Proof.
  intros lyc Sc W memc.
  assert (HH : forall rd : Z -> option Z, shadow_hull_vis rd 0 0)
    by (intros rd s Hs; exfalso; unfold shadow_addr, SHADOW_OFF in Hs; cbn in Hs; lia).
  assert (HR : forall rd : Z -> option Z, range_addressable rd SHADOW_OFF 0 0) by (intros rd x Hx; lia).
  right. split.
  - right. left. split; [intros a Ha; lia|]. intros ly S W' mem md _. exact (conj (HR _) (HH _)).
  - split; [intros a Ha; lia|]. split; [exact (HR _)|]. split; [exact (HH _)|].
    split; [unfold amem_range, kLowMemEnd; lia|]. split; lia.
Qed.

(* trans_sh_any of a range whose 64-byte blocks lie in a zero-shadow range of the record (decode_zshadow_ra). *)
Lemma trans_sh_any_zshadow (lo hi q n : Z) :
  decode_zshadow_at B lo hi -> 0 < n -> lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi -> trans_sh_any q n.
Proof. intros HZ Hn H1 H2 ly S W mem md HAR. exact (decode_zshadow_ra B ly S W mem md lo hi q n HAR HZ Hn H1 H2). Qed.

(* trans_sh_any of a sub-range. *)
Lemma trans_sh_any_sub : forall q n q' n', trans_sh_any q n -> q <= q' -> q' + n' <= q + n -> trans_sh_any q' n'.
Proof.
  intros q n q' n' H H1 H2 ly S W mem md HAR. destruct (H ly S W mem md HAR) as [Ha Hh].
  split; [exact (range_addressable_sub _ _ q n q' n' Ha H1 H2) | exact (trans_hull_sub _ q n q' n' Hh H1 H2)].
Qed.

(* decode_rd_ok in every case: the non-heap cases carry it; a heap block gives it from AR_laws (al_blocks: present,
   in [4096, alloc_ceiling); range_addressable_of_block, shadow_hull_vis_of_block, amem_range_of_block). *)
Lemma trans_src_ok_rd : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok lyc Sc W memc q n -> 0 < n ->
  decode_rd_ok W memc q n.
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR [(bA & nA & Hin & H1 & H2) | (_ & Hrd)] Hn; [|exact Hrd].
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & Hpr & _ & Hn0).
  pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
  pose proof asan_consts as (C1 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply aview_some_of_apresent. exact (proj1 (Hpr a ltac:(lia))).
  - exact (range_addressable_of_block segs B LAWS lyc Sc W memc mdc bA nA q n HAR Hin H1 ltac:(lia)).
  - exact (shadow_hull_vis_of_block segs B LAWS lyc Sc W memc mdc bA nA q n HAR Hin H1 ltac:(lia) Hn).
  - exact (amem_range_of_block segs B LAWS lyc Sc W memc mdc bA nA q n HAR Hin H1 ltac:(lia)).
  - lia.
  - lia.
Qed.

(* Where the range lies, in every case: in [4096, alloc_ceiling) (a heap block: al_blocks; a side-stack frame:
   frames_bounds; a harness global: G_HARNESS_B_HI; TRANS_RO_RD: below 0xa4000), or in the machine stack, which lies in
   [alloc_ceiling, 2 ^ 47) (trans_stk_bounds). It gives 0 < q in every case. *)
Lemma trans_src_ok_place : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok lyc Sc W memc q n -> 0 < n ->
  (4096 <= q /\ q + n <= alloc_ceiling) \/
  (alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc <= q /\ q + n <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47).
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hs as [(bA & nA & Hin & H1 & H2) | (HL & _)].
  - left. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. lia.
  - destruct HL as [(cid & pos & Hin & H1 & H2) | [(HG & _) | [(H1 & H2) | (HR & _)]]].
    + left. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _). lia.
    + left. pose proof (inG_G_HARNESS_hull q (HG q ltac:(lia))) as Gq.
      pose proof (inG_G_HARNESS_hull (q + n - 1) (HG (q + n - 1) ltac:(lia))) as Gn.
      unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in *. lia.
    + right. destruct (trans_stk_bounds lyc Sc W memc mdc HAR) as [S1 S2]. lia.
    + left. pose proof (trans_ro_rd_bounds q (HR q ltac:(lia))) as Rq.
      pose proof (trans_ro_rd_bounds (q + n - 1) (HR (q + n - 1) ltac:(lia))) as Rn. lia.
Qed.

(* A sub-range, empty or not: each placement shrinks, and decode_rd_ok and trans_sh_any restrict. *)
Lemma trans_src_ok_sub_ge0 : forall lyc Sc (W : world segs) memc q n q' n',
  trans_src_ok lyc Sc W memc q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
  trans_src_ok lyc Sc W memc q' n'.
Proof.
  intros lyc Sc W memc q n q' n' Hs H1 Hn H2.
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact Hin | lia].
  - right. split; [|exact (trans_rd_ok_sub W memc q n q' n' Hrd H1 H2 ltac:(lia))].
    destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & Hsh) | [(S1 & S2) | (HR & Hsh)]]].
    + left. exists cid, pos. split; [exact Hin | lia].
    + right. left. split; [intros a Ha; apply HG; lia | exact (trans_sh_any_sub q n q' n' Hsh H1 H2)].
    + right. right. left. lia.
    + right. right. right. split; [intros a Ha; apply HR; lia | exact (trans_sh_any_sub q n q' n' Hsh H1 H2)].
Qed.
Lemma trans_src_ok_sub : forall lyc Sc (W : world segs) memc q n q' n',
  trans_src_ok lyc Sc W memc q n -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  trans_src_ok lyc Sc W memc q' n'.
Proof.
  intros lyc Sc W memc q n q' n' Hs H1 Hn H2.
  exact (trans_src_ok_sub_ge0 lyc Sc W memc q n q' n' Hs H1 (Z.lt_le_incl _ _ Hn) H2).
Qed.

(* The same placement at a later memory of the walk's own runs, when they keep the range's bytes and the shadow band
   (the placements do not read memory). *)
Lemma trans_src_ok_view : forall lyc Sc (W W2 : world segs) memc mem2 q n,
  trans_src_ok lyc Sc W memc q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok lyc Sc W2 mem2 q n.
Proof.
  intros lyc Sc W W2 memc mem2 q n [Hb | (HL & Hrd)] K1 K2; [left; exact Hb|].
  right. split; [exact HL | exact (trans_rd_ok_view W W2 memc mem2 q n Hrd K1 K2)].
Qed.

(* The placement at another call state (ly2, S2): an inner journal's state, or the state after a callee. Its blocks
   and frames contain the caller's at the same addresses, and its machine stack is the same (YG0f.v layout_le); the
   reads need decode_rd_ok at that state's memory. *)
Lemma trans_src_ok_inner : forall lyc Sc (W : world segs) memc ly2 S2 (W2 : world segs) mem2 q n,
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  decode_rd_ok W2 mem2 q n ->
  trans_src_ok lyc Sc W memc q n -> trans_src_ok ly2 S2 W2 mem2 q n.
Proof.
  intros lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hfr Hfa Elo Ehi Hrd [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - right. split; [|exact Hrd].
    destruct HL as [(cid & pos & Hin & F1 & F2) | [HG | [(S1 & S3) | HR]]].
    + left. exists cid, pos. rewrite !Hfa. split; [exact (Hfr _ Hin) | lia].
    + right. left. exact HG.
    + right. right. left. rewrite Elo, Ehi. lia.
    + right. right. right. exact HR.
Qed.

(* FAKE: decode_rd_ok at a later memory that keeps the range's bytes and the shadow bytes of the caller's frames:
   the frame starts on 64 bytes and has a multiple of 64 bytes (TransportGCg.v dkg_frame_al64), so the range's hull,
   empty or not, lies in the frame's shadow (trans_hull_in). *)
Lemma decode_rd_ok_fake_kept_ge0 : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 <= n ->
  (forall a, q <= a < q + n -> aview segs (w_H W') mem' a = aview segs (w_H W) memc a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s) ->
  decode_rd_ok W' mem' q n.
Proof.
  intros LAWS lyc Sc W W' memc mem' mdc q n HAR (cid & pos & Hin & F1 & F2) (R1 & R2 & R3 & R4 & R5 & R6) Hn K1 K2.
  assert (AL : frame_addr lyc cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
    by (eapply TransportGCg.dkg_frame_al64; eassumption).
  destruct AL as (A1 & A2 & A3).
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (B1 & B2 & _).
  assert (KG : forall g, frame_addr lyc cid pos <= g < frame_addr lyc cid pos + fs_frame_bytes cid ->
    aview segs (w_H W') mem' (shadow_addr g) = aview segs (w_H W) memc (shadow_addr g)).
  { intros g Hg. apply (K2 cid pos); [exact Hin|]. unfold in_zr, shadow_addr. cbn [fst snd].
    pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
    pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
    pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia. }
  split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
  - intros a Ha. rewrite (K1 a Ha). exact (R1 a Ha).
  - intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
    rewrite (KG x ltac:(lia)). exact Hs.
  - intros s Hs.
    assert (Hhi : (frame_addr lyc cid pos + fs_frame_bytes cid) mod 64 = 0)
      by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
    destruct (trans_hull_in (frame_addr lyc cid pos) (frame_addr lyc cid pos + fs_frame_bytes cid) q n s
      A1 Hhi F1 F2 Hn Hs) as (g & Hg8 & Hg1 & Hg2 & ->).
    rewrite (KG g ltac:(lia)). exact (R3 _ Hs).
Qed.
Lemma decode_rd_ok_fake_kept : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 < n ->
  (forall a, q <= a < q + n -> aview segs (w_H W') mem' a = aview segs (w_H W) memc a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s) ->
  decode_rd_ok W' mem' q n.
Proof.
  intros LAWS lyc Sc W W' memc mem' mdc q n HAR HF Hrd Hn K1 K2.
  exact (decode_rd_ok_fake_kept_ge0 LAWS lyc Sc W W' memc mem' mdc q n HAR HF Hrd (Z.lt_le_incl _ _ Hn) K1 K2).
Qed.

(* The placement at the state after a call, from the range's bytes kept and the caller's frames' shadow bytes kept,
   for a range empty or not: FAKE by decode_rd_ok_fake_kept_ge0, the machine stack by stack_zshadow_ra_ge0 at the new
   state, G and TRANS_RO_RD by trans_sh_any at the new state. *)
Lemma trans_src_ok_kept_ge0 : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok lyc Sc W memc q n -> 0 <= n -> trans_src_ok ly2 S2 W2 mem2 q n.
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi K1 K2 Hs Hn.
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (Hf : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; exact Hf).
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & Hrd)].
  - left. exists bA, nA. split; [exact (Hbl _ Hin) | lia].
  - assert (Hrd2 : decode_rd_ok W2 mem2 q n).
    { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
      - exact (decode_rd_ok_fake_kept_ge0 LAWS lyc Sc W W2 memc mem2 mdc q n HAR HF Hrd Hn K1 K2).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh).
      - destruct (stack_zshadow_ra_ge0 B ly2 S2 W2 mem2 md2 q n HAR2 Hn ltac:(rewrite Elo; lia)
                    ltac:(rewrite Ehi; lia))
          as [Ha Hh].
        exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh).
      - destruct (Hsh ly2 S2 W2 mem2 md2 HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W2 memc mem2 q n Hrd K1 Ha Hh). }
    exact (trans_src_ok_inner lyc Sc W memc ly2 S2 W2 mem2 q n Hbl Hf Hfa Elo Ehi Hrd2 (or_intror (conj HL Hrd))).
Qed.
Lemma trans_src_ok_kept : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok lyc Sc W memc q n -> 0 < n -> trans_src_ok ly2 S2 W2 mem2 q n.
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi K1 K2 Hs Hn.
  exact (trans_src_ok_kept_ge0 LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi K1 K2 Hs
           (Z.lt_le_incl _ _ Hn)).
Qed.

(* Across a donor callee (its post's YCbq.v acall_kept at the call state, E its written range, [slo, shi) its stack
   window), for a range empty or not: the range's bytes kept (a heap block: the block clause; FAKE: the frame clause;
   G and TRANS_RO_RD: the image clause, with the record's facts that no such byte is an owned static or errno; the
   machine stack: the clause at or above alloc_ceiling, outside the callee's window), the frames' shadow bytes kept
   (the frame clause; E misses the shadow band), and so the placement at the state after the call. *)
Lemma trans_src_ok_acall_ge0 : AR_laws segs B -> trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  @acall_kept rc segs B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HGU HGE HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HnE HnEs Hoff Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + pose proof (HG a Ha) as Ga. exact (K3 a (trans_g_img a Ga) (HGU a Ga) (HGE a Ga)).
      + destruct (trans_stk_bounds lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        exact (K3 a (trans_ro_img a Ra) Ho He). }
  split; [|exact KV].
  exact (trans_src_ok_kept_ge0 LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS Hs
           Hn).
Qed.
Lemma trans_src_ok_acall : AR_laws segs B -> trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  @acall_kept rc segs B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok lyc Sc W memc q n -> 0 < n ->
  trans_src_ok ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HGU HGE HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    HK HnE HnEs Hoff Hs Hn.
  exact (trans_src_ok_acall_ge0 LAWS HGU HGE HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2
           Hperm Hfr Hfa Elo Ehi HK HnE HnEs Hoff Hs (Z.lt_le_incl _ _ Hn)).
Qed.

(* The same across a G-form callee (TransportGCg.v acall_kept_g G_HARNESS_B, whose image clause leaves G out), for a
   range empty or not: the G bytes from the callee's gx_kept, a TRANS_RO_RD byte from the image clause (it lies below
   G_HARNESS_B_LO). *)
Lemma trans_src_ok_acall_g_ge0 : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  TransportGCg.acall_kept_g segs B TransportGB.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  TransportGCg.gx_kept segs TransportGB.G_HARNESS_B W memc W2 mem2 ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HGK HnE HnEs Hoff Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exact (HGK a (HG a Ha)).
      + destruct (trans_stk_bounds lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TransportGB.G_HARNESS_B_LO in Gh. lia. }
  split; [|exact KV].
  exact (trans_src_ok_kept_ge0 LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS Hs
           Hn).
Qed.
Lemma trans_src_ok_acall_g : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  TransportGCg.acall_kept_g segs B TransportGB.G_HARNESS_B lyc Sc W memc W2 mem2 slo shi E ->
  TransportGCg.gx_kept segs TransportGB.G_HARNESS_B W memc W2 mem2 ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok lyc Sc W memc q n -> 0 < n ->
  trans_src_ok ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    HK HGK HnE HnEs Hoff Hs Hn.
  exact (trans_src_ok_acall_g_ge0 LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2
           Hperm Hfr Hfa Elo Ehi HK HGK HnE HnEs Hoff Hs (Z.lt_le_incl _ _ Hn)).
Qed.

(* The range is apart from a callee's new side-stack frame (cid, pos), the head of frames S2: a heap block by
   sep_block_frame; FAKE by sep_frames_pos; G and TRANS_RO_RD are image bytes and a frame byte is not (frm_img); the
   machine stack lies at or above alloc_ceiling, the frame below it (frames_bounds). *)
Lemma trans_src_ok_disj_own : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 cid pos q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (cid, pos) :: frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  trans_src_ok lyc Sc W memc q n -> 0 < n ->
  q + n <= frame_addr ly2 cid pos \/ frame_addr ly2 cid pos + fs_frame_bytes cid <= q.
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 cid pos q n HAR HAR2 Hfr Hperm Hfa Hs Hn.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR2 Hin2) as (F1 & F2 & _).
  assert (AL : frame_addr ly2 cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
    by (eapply TransportGCg.dkg_frame_al64; eassumption).
  destruct AL as (_ & _ & Hfs).
  destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - assert (HinB : In (bA, nA) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
    pose proof (sep_block_frame segs B LAWS ly2 S2 W2 mem2 md2 bA nA cid pos HAR2 HinB Hin2) as Hd.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 bA nA HAR2 HinB) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - destruct HL as [(c & p & Hin & G1 & G2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + destruct (in_split _ _ Hin) as (l2 & l3 & El).
      pose proof (sep_frames_pos segs B LAWS ly2 S2 W2 mem2 md2 (cid, pos) (c, p) [] l2 l3 HAR2
        ltac:(rewrite Hfr, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite (Hfa c p) in Hd. lia.
    + destruct (Z_le_gt_dec (q + n) (frame_addr ly2 cid pos)) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (frame_addr ly2 cid pos + fs_frame_bytes cid) q) as [H2|H2]; [right; exact H2|].
      exfalso.
      apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 cid pos (Z.max q (frame_addr ly2 cid pos)) HAR2 Hin2); [lia|].
      set (x := Z.max q (frame_addr ly2 cid pos)). exact (trans_g_img x (HG x ltac:(unfold x; lia))).
    + right. destruct (trans_stk_bounds lyc Sc W memc mdc HAR) as [T1 T2]. lia.
    + destruct (Z_le_gt_dec (q + n) (frame_addr ly2 cid pos)) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (frame_addr ly2 cid pos + fs_frame_bytes cid) q) as [H2|H2]; [right; exact H2|].
      exfalso.
      apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 cid pos (Z.max q (frame_addr ly2 cid pos)) HAR2 Hin2); [lia|].
      set (x := Z.max q (frame_addr ly2 cid pos)). exact (trans_ro_img x (HR x ltac:(unfold x; lia))).
Qed.

(* Where the range [q, q + n) a callee WRITES for its caller may lie (diginet_frame_build's out in the G form): a
   caller's side-stack frame (send_control's class-2 frame) or a harness global (send_data's g_s.inflight_frame, with
   trans_sh_any), with decode_rd_ok (the stores and copies check its shadow). A machine-stack out is not covered: the
   G-form post's acall_kept_g keeps every byte at or above alloc_ceiling outside the callee's window. *)
Definition trans_out_ok (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (q n : Z) : Prop :=
  (decode_in_fake lyc Sc q n \/
   ((forall a, q <= a < q + n -> W_journalG.inG TransportGB.G_HARNESS_B a) /\ trans_sh_any q n)) /\
  decode_rd_ok W memc q n.

(* out lies in [4096, alloc_ceiling) and in application memory below the low shadow or in high memory (a frame:
   frames_bounds; G: below G_HARNESS_B_HI < kLowShadowBeg). *)
Lemma trans_out_ok_far : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_out_ok lyc Sc W memc q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling /\ (q + n <= kLowShadowBeg \/ kHighMemBeg <= q).
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR [[(cid & pos & Hin & F1 & F2) | (HG & _)] _] Hn.
  - destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (B1 & B2 & B3).
    unfold in_app, ASAN_CEIL in B3. lia.
  - pose proof asan_consts as (C1 & _). pose proof (inG_G_HARNESS_hull q (HG q ltac:(lia))) as Gq.
    pose proof (inG_G_HARNESS_hull (q + n - 1) (HG (q + n - 1) ltac:(lia))) as Gn.
    unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI, kLowShadowBeg in *. lia.
Qed.

(* trans_out_ok of a sub-range. *)
Lemma trans_out_ok_sub : forall lyc Sc (W : world segs) memc q n q' n',
  trans_out_ok lyc Sc W memc q n -> q <= q' -> 0 < n' -> q' + n' <= q + n -> trans_out_ok lyc Sc W memc q' n'.
Proof.
  intros lyc Sc W memc q n q' n' [HL Hrd] H1 Hn H2.
  split; [|exact (trans_rd_ok_sub W memc q n q' n' Hrd H1 H2 ltac:(lia))].
  destruct HL as [(cid & pos & Hin & F1 & F2) | (HG & Hsh)].
  - left. exists cid, pos. split; [exact Hin | lia].
  - right. split; [intros a Ha; apply HG; lia | exact (trans_sh_any_sub q n q' n' Hsh H1 H2)].
Qed.

(* What a caller-journal call leaves, at a written range E: the caller's journal extended by at most EV events,
   callee-saved registers kept, the side-stack frames of the call state exactly (every frame the call takes is
   released), the caller's blocks exactly (every block the call allocates is freed), every byte outside the call's
   stack window [spZ regs - FSTK, spZ regs) and outside E kept (YCbq.v acall_kept), the meter charged at most COST,
   and the statement's own facts X about the return registers and the memory. The return pc is the entry ra and the
   float state is the entry's. *)
Definition decode_cg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (FSTK EV COST : Z) (E : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 e,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    0 <= e <= EV /\ @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - FSTK) (spZ regs) E /\
    mo_le MT Sc S2 COST /\
    X regs2 W2 mem2.

(* decode_cg_post is TransportGCg.v's dcg_post at this unit's segments and sink head (the same conjuncts at
   `@ajournal rc tfib_sink_head`): the callee post TransportGCg.v gx_call_cg takes, which quantifies over its Context
   sink head. *)
Lemma decode_cg_post_dcg : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc k
    regs FSTK EV COST (E : Z -> Prop) X W2 c2,
  decode_cg_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2 ->
  @TransportGCg.dcg_post fx rc tfib_sink_head segs B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    FSTK EV COST E X W2 c2.
Proof. intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2 H. exact H. Qed.
End cj.

(* struct diginet_frame (include/diginet/diginet.h), 64 bytes, as diginet_frame_parse leaves it for the input bytes
   b at buf when fj are the 64 bytes before the call: parse_cells (lib/Prog/diginet_frame_parse_c.v) when the code is
   0, else fj (the plain contract's two cases). *)
Definition frame_f_cells (buf : Z) (b fj : list byte) : list LC.cell :=
  if DSpec.fr_code b =? 0 then PParse.parse_cells buf b fj else [LC.CB 64 fj].
Definition FRAME_F_SIZE : Z := 64.
Definition frame_f_bytes (buf : Z) (b fj : list byte) : list Z :=
  map (fun x : byte => bv_unsigned x) (LC.cells_bytes (frame_f_cells buf b fj)).
