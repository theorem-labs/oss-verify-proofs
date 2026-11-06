(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths and module names changed; 82 of its 158 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/UciCg.v (commit ba35beec1417; itself the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v at recipes commit 88154566652a) for reac-repacer/fuzz_uci's image B: module paths changed (the B core's tfibsegs lib/B/YB1v.v, its journal file lib/B/YCbq.v, lib/B/AsanCells.v); the read-only reads and the cells are fuzz_uci.asan-ubsan's, measured on the pinned image (MARGIN_MAX 0x20ca0 and musl memchr's window [0x10350, 0x10370) are at image A's addresses; the instruction addresses in the comments are image B's). *)
(* WireCg: the definitions every program statement of fuzz_wire.asan-ubsan (lib/B/Prog/*_cg.v) shares. STATEMENTS and
   decided facts only: nothing here is a walk.
   - wire_utrace: the trace the allocator records at a call (decode's dec_utrace);
   - WIRE_RO_RD: the read-only bytes the walks read through the image view, with wire_ro_rd_unowned /
     wire_rom_no_errno, the two facts about the record B that keep them visible through a journal;
   - wire_tab_zshadow_at: a value-0 shadow granule of an unowned global, as a fact of the record;
   - wire_cells: the runtime cells the program and its leaves read, as constant cells of the record;
   - wire_leaf_at / wire_leaf_wr_at: a leaf statement of the kit lib/B/Prog/LeafCgKit.v read at this unit's model. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require AsanCells.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module WCells := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The trace the allocator records at a call: the call's return address and the return addresses of the
   frame-pointer chain after it (YG00.v unwind_of_chain; YG0d.v call_trace at ras = raZ regs :: spine ch). The
   functions of fuzz_wire.asan-ubsan on an allocation path (LLVMFuzzerTestOneInput, malloc / free at 0x7fc7c, 0x7fd04,
   0x7fd4c, 0x7fd54; check_copy at 0x80b08, 0x80c98) keep no frame pointer (lib/B/YCej.v; only check_meter, 0x801a4,
   and check_read, 0x80630, set one up, and neither allocates), so every trace the program records is
   [pc0; return address]. *)
Definition wire_utrace (pc0 : Z) (ras : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) ras).

(* Every runtime cell of AsanCells.asan_cells lies inside one loaded segment of the image (decided by vm_compute). *)
Definition wire_seg_covers (a n : Z) : bool :=
  existsb (fun s : Segment => (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
    tfibsegs.
Definition wire_asan_cell_ranges : list (Z * Z) :=
  [(WCells.CELL_K, 8); (WCells.GOT_CELL_K, 8); (WCells.INITED, 1); (WCells.REPLACE, 1); (WCells.GOT_REPLACE, 8);
   (WCells.UAR, 4); (WCells.GOT_UAR, 8); (WCells.CANPOISON, 1); (WCells.HIEND, 8); (WCells.GOT_HIEND, 8);
   (WCells.MIDBEG, 8); (WCells.GOT_MIDBEG, 8); (WCells.MIDEND, 8); (WCells.GOT_MIDEND, 8);
   (WCells.REAL_MEMCPY, 8); (WCells.GOT_REAL_MEMCPY, 8); (WCells.REAL_MEMSET, 8); (WCells.GOT_REAL_MEMSET, 8);
   (WCells.REAL_BCMP, 8)].
Lemma wire_asan_cells_in_seg : forallb (fun r => wire_seg_covers (fst r) (snd r)) wire_asan_cell_ranges = true.
Proof. vm_compute. reflexivity. Qed.

(* The read-only bytes the walks read through the image view, as (base, size) ranges (in_zr, YG0n.v):
     (0x10300, 8), (0x103b0, 8)  the two 8-byte .rodata constants reac_frame_clean_len loads (`ld` at 0x818f4 from
                                 0x10300 = 0x8e38e38e38e38e39 and at 0x818fc from 0x103b0 = 0x071c71c71c71c71d, each
                                 formed by auipc; lib/B/Prog/WirePAddr.v wire_obj 10, 11); neither lies in the record's
                                 owned statics (lib/B/YF0m.v Tfib_owned_static).
   The one other .rodata word a program function loads, 0x10328 (rp_frame_channels, `ld` at 0x813c4; wire_obj 9), is
   an owned static (lib/B/YF0m.v:271) and a constant cell of the record (:253), so it reaches the walks as wire_cells'
   last row below. Both ranges lie in fuzz_wire.asan-ubsan's first PT_LOAD [0x10000, 0x2ef5c), which is read-only. *)
Definition WIRE_RO_RD : list (Z * Z) := [(0x10300, 8); (0x103b0, 8)].
Definition wire_in_ro_rd (a : Z) : Prop := Exists (in_zr a) WIRE_RO_RD.
(* The read-only view at the WIRE_RO_RD bytes only: rom_view (YG0d.v) scoped to what the walks read. *)
Definition wire_rom_view_rd (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  forall a, wire_in_ro_rd a ->
    aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).

(* Every WIRE_RO_RD byte lies in a non-writable loaded segment, and the image holds a byte there (decided by
   vm_compute). *)
Definition wire_rom_b (a : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                             (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.
Definition wire_img_b (a : Z) : bool :=
  match YK11.seg_rom tfibsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition wire_zr_bytes (r : Z * Z) : list Z := map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r))).
Lemma wire_ro_rd_clean :
  forallb (fun r => forallb (fun z => wire_rom_b z && wire_img_b z)%bool (wire_zr_bytes r)) WIRE_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma wire_zr_enum (P : Z -> bool) (Lr : list (Z * Z)) (a : Z) :
  forallb (fun r => forallb P (wire_zr_bytes r)) Lr = true -> Exists (in_zr a) Lr -> P a = true.
Proof.
  intros HF HE. apply Exists_exists in HE as [r [Hin [H1 H2]]].
  rewrite forallb_forall in HF. specialize (HF r Hin). rewrite forallb_forall in HF.
  apply HF. unfold wire_zr_bytes. apply in_map_iff. exists (Z.to_nat (a - fst r)). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.
Lemma wire_rom_b_in_rom (a : Z) : wire_rom_b a = true -> in_rom tfibsegs a.
Proof.
  unfold wire_rom_b, in_rom. intro H. apply existsb_exists in H as [sg [Hin H]].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists sg. repeat split; auto; lia.
Qed.
Lemma wire_img_b_some (a : Z) : wire_img_b a = true -> exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  unfold wire_img_b. destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; intro H; [exists b; reflexivity | discriminate H].
Qed.
Lemma wire_ro_rd_rom_clean (a : Z) :
  wire_in_ro_rd a -> in_rom tfibsegs a /\ exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  intro H. pose proof (wire_zr_enum _ _ a wire_ro_rd_clean H) as HP.
  cbv beta in HP. apply andb_true_iff in HP as [HR HI].
  split; [exact (wire_rom_b_in_rom a HR) | exact (wire_img_b_some a HI)].
Qed.

(* The two instance facts about the record B (rows of the closing file, decided at the concrete record): no
   WIRE_RO_RD byte is an owned static, and errno (writable .bss) is not in the read-only image. The first is scoped to
   WIRE_RO_RD: the record owns read-only bytes elsewhere in the first PT_LOAD (0x10328, for one; lib/B/YF0m.v
   Tfib_owned_static). *)
Definition wire_ro_rd_unowned (B : asyms) : Prop :=
  forall a, wire_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B).
Definition wire_rom_no_errno (B : asyms) : Prop :=
  forall a, in_rom tfibsegs a -> ~ (as_errno B <= a < as_errno B + 4).
(* From them, the scoped fact the journal's image clause (YCbq.v ajournal) and arodata_okS (YE01.v) need at each
   WIRE_RO_RD byte. *)
Lemma wire_ro_rd_scoped (B : asyms) : wire_ro_rd_unowned B -> wire_rom_no_errno B ->
  forall a, wire_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros HO HE a H. destruct (wire_ro_rd_rom_clean a H) as [HR _]. split.
  - exact (HO a H).
  - exact (HE a HR).
Qed.

(* The value-0 shadow granule at T of an unowned global (the granule [T, T + 8)) as a fact of the record: it lies
   inside a range of as_zero_shadow B (YG0f.v; the record's Tfib_zero_shadow by ts_zsh). ARm's am_zshadow (YG0n.v
   zshadow_ok) reads every as_zero_shadow range's shadow as 0 at every AR state; wire_tab_zshadow_rd is that read. *)
Definition wire_tab_zshadow_at (B : asyms) (T : Z) : Prop :=
  exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= T /\ T + 8 <= fst r + snd r.
Lemma wire_tab_zshadow_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (T : Z) :
  @AR rc tfibsegs B ly S W mem md -> T mod 8 = 0 -> wire_tab_zshadow_at B T ->
  aview tfibsegs (w_H W) mem (WCells.shadow_addr T) = Some 0.
Proof.
  intros [M _] HT (r & Hin & H8 & H1 & H2).
  pose proof (am_zshadow _ _ _ _ M) as Z. unfold zshadow_ok in Z. rewrite Forall_forall in Z.
  assert (Hr : In r (zero_shadow_ranges B ly)) by (unfold zero_shadow_ranges; right; exact Hin).
  specialize (Z r Hr). hnf in Z.
  assert (Ea : fst r = 8 * (fst r / 8)) by (pose proof (Z.div_mod (fst r) 8 ltac:(lia)); lia).
  assert (Et : T = 8 * (T / 8)) by (pose proof (Z.div_mod T 8 ltac:(lia)); lia).
  assert (Ei : (T - fst r) / 8 = T / 8 - fst r / 8).
  { replace (T - fst r) with ((T / 8 - fst r / 8) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hs : T / 8 - fst r / 8 + 1 <= snd r / 8) by (apply Z.div_le_lower_bound; lia).
  specialize (Z ((T - fst r) / 8) ltac:(rewrite Ei; lia)).
  replace (WCells.shadow_addr T) with (shadow_of_addr SHADOW_OFF (fst r) + (T - fst r) / 8); [exact Z|].
  rewrite Ei. unfold shadow_of_addr, WCells.shadow_addr, WCells.ASAN_K, SHADOW_OFF. lia.
Qed.

(* The owned .rodata word rp_frame_channels loads (`ld` at 0x813c4 from 0x10328), with its image value. *)
Definition WIRE_RO_FCH : Z := 0x10328.
Definition WIRE_RO_FCH_VAL : Z := 0xe38e38e38e38e38f.

(* The runtime cells the program and its leaves read, as constant cells of the record B: as_const (YG0f.v) is
   re-read at every AR state (YG0n.v ARm am_const), so a walk reads them after any call. Rows 1-19 are
   AsanCells.asan_cells (lib/B/AsanCells.v), in its order and with its widths and values; row 20 is the owned .rodata
   word WIRE_RO_FCH (lib/B/YF0m.v:253). Each is a row of the B core's record (lib/B/YF0m.v Tfib_const_abs).
   LLVMFuzzerTestOneInput reads the shadow base through GOT_CELL_K (the `ld` at 0x7fc38). *)
Definition wire_cells (B : asyms) : Prop :=
  forall ly,
    In (z8 (ANum WCells.CELL_K) WCells.ASAN_K) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_CELL_K) WCells.CELL_K) (as_const B ly) /\
    In (z1 (ANum WCells.INITED) 1) (as_const B ly) /\
    In (z1 (ANum WCells.REPLACE) 1) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_REPLACE) WCells.REPLACE) (as_const B ly) /\
    In (z4 (ANum WCells.UAR) 1) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_UAR) WCells.UAR) (as_const B ly) /\
    In (z1 (ANum WCells.CANPOISON) 1) (as_const B ly) /\
    In (z8 (ANum WCells.HIEND) 0x7fffffffffff) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_HIEND) WCells.HIEND) (as_const B ly) /\
    In (z8 (ANum WCells.MIDBEG) 0) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_MIDBEG) WCells.MIDBEG) (as_const B ly) /\
    In (z8 (ANum WCells.MIDEND) 0) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_MIDEND) WCells.MIDEND) (as_const B ly) /\
    In (z8 (ANum WCells.REAL_MEMCPY) WCells.MUSL_MEMCPY) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_REAL_MEMCPY) WCells.REAL_MEMCPY) (as_const B ly) /\
    In (z8 (ANum WCells.REAL_MEMSET) WCells.MUSL_MEMSET) (as_const B ly) /\
    In (z8 (ANum WCells.GOT_REAL_MEMSET) WCells.REAL_MEMSET) (as_const B ly) /\
    In (z8 (ANum WCells.REAL_BCMP) WCells.MUSL_BCMP) (as_const B ly) /\
    In (z8 (ANum WIRE_RO_FCH) WIRE_RO_FCH_VAL) (as_const B ly).

(* The C int bounds, for the statements' range premises (the names and values of fuzz_uci's lib/Spec/UciModel.v:15;
   the core files lib/B/YE3j.v / YE3k.v / YE3n.v keep their own INT_MAX, equal to this one, and no statement imports
   them; a file that Requires both writes WireCg.INT_MAX). The same names are image A's (lib/A/Prog/WireCg.v). *)
Definition INT_MIN : Z := - 2 ^ 31.
Definition INT_MAX : Z := 2 ^ 31 - 1.

(* A live block of the record's allocator model means a non-empty depot (lib/Reusable/YG0n.v am_alloc_depot over
   YG0d.v ablocks / YG01.v blocks): the premise st_depot S <> [] of the journal's malloc rule (lib/B/YC5d.v
   amalloc04_rule). The same lemma as image A's lib/A/Prog/WireCg.v. *)
Lemma wire_depot_of_block {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (p n : Z) :
  @AR rc tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> st_depot S <> [].
Proof.
  intros [HM _] Hin.
  pose proof (am_alloc_depot _ _ _ _ HM) as D. unfold am_alloc_depot_d in D.
  apply D. unfold ablocks, blocks in Hin.
  apply in_map_iff in Hin as ([sp r] & _ & Hin).
  apply in_map_iff in Hin as (k & _ & Hk).
  apply filter_In in Hk as [Hk _].
  exists k. exact Hk.
Qed.

Section leaf. Context {rc : YM05.RunCeil}.
Variable B : asyms.
(* A leaf statement of lib/B/Prog/<leaf>_cg.v, closed over the Section Variables of the shared kit
   lib/B/Prog/LeafCgKit.v (world .. as_tp), read at this unit's allocator model (lib/Reusable YA0n / YG0f / YG0n /
   YG0d / YK04 / YK0s), image B's segments and the record B. *)
Definition wire_leaf_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
(* A leaf that writes a caller buffer also takes aowned, for the kit's premise `forall x, in_wr WR x -> ... ~ aowned
   ly S x /\ ~ in_img x` (LeafCgKit.v leaf_cg_of_evtF_stmt). A byte of a caller's live fake frame is an aclient_byte
   (YG0n.v), so it is never aowned (aowned requires ~ aclient_byte), and AR_laws' al_client_img (YG0d.v) keeps it out
   of the image. *)
Definition wire_leaf_wr_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> (alayout -> astate -> Z -> Prop) -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B).
End leaf.
