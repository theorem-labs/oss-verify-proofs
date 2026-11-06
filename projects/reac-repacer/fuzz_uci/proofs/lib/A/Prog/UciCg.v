(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* UciCg: the definitions every program statement of fuzz_uci.asan (lib/A/Prog/*_cg.v) shares. STATEMENTS and
   decided facts only: nothing here is a walk.
   - uci_utrace: the trace the allocator records at a call (decode's dec_utrace);
   - UCI_RO_RD: the read-only bytes the walks read through the image view, with uci_ro_rd_unowned /
     uci_rom_no_errno, the two facts about the record B that keep them visible through a journal;
   - uci_tab_zshadow_at: a value-0 shadow granule of an unowned global, as a fact of the record;
   - uci_cells: the runtime cells the program and its leaves read, as constant cells of the record;
   - uci_leaf_at / uci_leaf_wr_at: a leaf statement of the kit lib/A/Prog/LeafCgKit.v read at this unit's model. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AsanCells.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module UCells := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The trace the allocator records at a call: the call's return address and the return addresses of the
   frame-pointer chain after it (YG00.v unwind_of_chain; YG0d.v call_trace at ras = raZ regs :: spine ch). No
   function of fuzz_uci.asan on an allocation path keeps a frame pointer (lib/A/ACej.v), so every trace the program
   records is [pc0; return address]. *)
Definition uci_utrace (pc0 : Z) (ras : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) ras).

(* Every runtime cell of AsanCells.asan_cells lies inside one loaded segment of the image (decided by vm_compute). *)
Definition uci_seg_covers (a n : Z) : bool :=
  existsb (fun s : Segment => (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
    tfibsegs.
Definition uci_asan_cell_ranges : list (Z * Z) :=
  [(UCells.CELL_K, 8); (UCells.GOT_CELL_K, 8); (UCells.INITED, 1); (UCells.REPLACE, 1); (UCells.GOT_REPLACE, 8);
   (UCells.UAR, 4); (UCells.GOT_UAR, 8); (UCells.CANPOISON, 1); (UCells.HIEND, 8); (UCells.GOT_HIEND, 8);
   (UCells.MIDBEG, 8); (UCells.GOT_MIDBEG, 8); (UCells.MIDEND, 8); (UCells.GOT_MIDEND, 8); (UCells.REAL_MEMCPY, 8);
   (UCells.REAL_MEMCHR, 8); (UCells.GOT_REAL_MEMCPY, 8)].
Lemma uci_asan_cells_in_seg : forallb (fun r => uci_seg_covers (fst r) (snd r)) uci_asan_cell_ranges = true.
Proof. vm_compute. reflexivity. Qed.

(* The read-only bytes the walks read through the image view, as (base, size) ranges (in_zr, YG0n.v):
     (0x20ca0, 8)    MARGIN_MAX, the two 4-byte bounds LLVMFuzzerTestOneInput reads (`lw s2, 0(a0)` at 0x7f380,
                     a0 = 0x20ca0 + 4 * (data[0] & 1)); a registered ASan global (asan_globals at 0x9b8d0: beg 0x20ca0,
                     size 8, size_with_redzone 0x20), so it is program data, never an owned static;
     (0x10350, 0x20) musl memchr's constant window (lib/A/AE39.v mc_bounds), which the memchr interceptor that
                     rp_uci_int calls reads.
   Both ranges lie in fuzz_uci.asan's first PT_LOAD [0x10000, 0x2ebf0), which is read-only. *)
Definition UCI_RO_RD : list (Z * Z) := [(0x20ca0, 8); (0x10350, 0x20)].
Definition uci_in_ro_rd (a : Z) : Prop := Exists (in_zr a) UCI_RO_RD.
(* The read-only view at the UCI_RO_RD bytes only: rom_view (YG0d.v) scoped to what the walks read. *)
Definition uci_rom_view_rd (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  forall a, uci_in_ro_rd a ->
    aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).

(* Every UCI_RO_RD byte lies in a non-writable loaded segment, and the image holds a byte there (decided by
   vm_compute). *)
Definition uci_rom_b (a : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                             (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool tfibsegs.
Definition uci_img_b (a : Z) : bool :=
  match YK11.seg_rom tfibsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition uci_zr_bytes (r : Z * Z) : list Z := map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r))).
Lemma uci_ro_rd_clean :
  forallb (fun r => forallb (fun z => uci_rom_b z && uci_img_b z)%bool (uci_zr_bytes r)) UCI_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma uci_zr_enum (P : Z -> bool) (Lr : list (Z * Z)) (a : Z) :
  forallb (fun r => forallb P (uci_zr_bytes r)) Lr = true -> Exists (in_zr a) Lr -> P a = true.
Proof.
  intros HF HE. apply Exists_exists in HE as [r [Hin [H1 H2]]].
  rewrite forallb_forall in HF. specialize (HF r Hin). rewrite forallb_forall in HF.
  apply HF. unfold uci_zr_bytes. apply in_map_iff. exists (Z.to_nat (a - fst r)). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.
Lemma uci_rom_b_in_rom (a : Z) : uci_rom_b a = true -> in_rom tfibsegs a.
Proof.
  unfold uci_rom_b, in_rom. intro H. apply existsb_exists in H as [sg [Hin H]].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists sg. repeat split; auto; lia.
Qed.
Lemma uci_img_b_some (a : Z) : uci_img_b a = true -> exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  unfold uci_img_b. destruct (YK11.seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; intro H; [exists b; reflexivity | discriminate H].
Qed.
Lemma uci_ro_rd_rom_clean (a : Z) :
  uci_in_ro_rd a -> in_rom tfibsegs a /\ exists b : byte, YK11.seg_rom tfibsegs (Z_to_bv 64 a) = Some b.
Proof.
  intro H. pose proof (uci_zr_enum _ _ a uci_ro_rd_clean H) as HP.
  cbv beta in HP. apply andb_true_iff in HP as [HR HI].
  split; [exact (uci_rom_b_in_rom a HR) | exact (uci_img_b_some a HI)].
Qed.

(* The two instance facts about the record B (rows of the closing file, decided at the concrete record): no
   UCI_RO_RD byte is an owned static, and errno (writable .bss) is not in the read-only image. The first is scoped to
   UCI_RO_RD: the record owns read-only bytes elsewhere in the first PT_LOAD (0x102e8, for one). *)
Definition uci_ro_rd_unowned (B : asyms) : Prop :=
  forall a, uci_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B).
Definition uci_rom_no_errno (B : asyms) : Prop :=
  forall a, in_rom tfibsegs a -> ~ (as_errno B <= a < as_errno B + 4).
(* From them, the scoped fact the journal's image clause (YCbq.v ajournal) and arodata_okS (YE01.v) need at each
   UCI_RO_RD byte. *)
Lemma uci_ro_rd_scoped (B : asyms) : uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  forall a, uci_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros HO HE a H. destruct (uci_ro_rd_rom_clean a H) as [HR _]. split.
  - exact (HO a H).
  - exact (HE a HR).
Qed.

(* The value-0 shadow granule at T of an unowned global (the granule [T, T + 8)) as a fact of the record: it lies
   inside a range of as_zero_shadow B (YG0f.v; the record's Tfib_zero_shadow by ts_zsh). ARm's am_zshadow (YG0n.v
   zshadow_ok) reads every as_zero_shadow range's shadow as 0 at every AR state; uci_tab_zshadow_rd is that read. *)
Definition uci_tab_zshadow_at (B : asyms) (T : Z) : Prop :=
  exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= T /\ T + 8 <= fst r + snd r.
Lemma uci_tab_zshadow_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (T : Z) :
  @AR rc tfibsegs B ly S W mem md -> T mod 8 = 0 -> uci_tab_zshadow_at B T ->
  aview tfibsegs (w_H W) mem (UCells.shadow_addr T) = Some 0.
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
  replace (UCells.shadow_addr T) with (shadow_of_addr SHADOW_OFF (fst r) + (T - fst r) / 8); [exact Z|].
  rewrite Ei. unfold shadow_of_addr, UCells.shadow_addr, UCells.ASAN_K, SHADOW_OFF. lia.
Qed.

(* MARGIN_MAX (0x20ca0, 8 bytes, a registered global with redzone [0x20ca8, 0x20cc0)). *)
Definition UCI_MARGIN_MAX : Z := 0x20ca0.

(* The runtime cells the program and its leaves read, as constant cells of the record B: as_const (YG0f.v) is
   re-read at every AR state (YG0n.v ARm am_const), so a walk reads them after any call. Rows 1-17 are
   AsanCells.asan_cells (lib/A/AsanCells.v), in its order and with its widths and values; each is a row of the core's
   record (lib/A/AF0m.v Tfib_const_abs). Row 18: MARGIN_MAX's granule has shadow 0 (lib/A/AF0m.v Tfib_zero_shadow
   (0x10000, 0x20ca8 - 0x10000)), which refutes LLVMFuzzerTestOneInput's __asan_report_load4 at 0x7f4e4. *)
Definition uci_cells (B : asyms) : Prop :=
  forall ly,
    In (z8 (ANum UCells.CELL_K) UCells.ASAN_K) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_CELL_K) UCells.CELL_K) (as_const B ly) /\
    In (z1 (ANum UCells.INITED) 1) (as_const B ly) /\
    In (z1 (ANum UCells.REPLACE) 1) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_REPLACE) UCells.REPLACE) (as_const B ly) /\
    In (z4 (ANum UCells.UAR) 1) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_UAR) UCells.UAR) (as_const B ly) /\
    In (z1 (ANum UCells.CANPOISON) 1) (as_const B ly) /\
    In (z8 (ANum UCells.HIEND) 0x7fffffffffff) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_HIEND) UCells.HIEND) (as_const B ly) /\
    In (z8 (ANum UCells.MIDBEG) 0) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_MIDBEG) UCells.MIDBEG) (as_const B ly) /\
    In (z8 (ANum UCells.MIDEND) 0) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_MIDEND) UCells.MIDEND) (as_const B ly) /\
    In (z8 (ANum UCells.REAL_MEMCPY) UCells.MUSL_MEMCPY) (as_const B ly) /\
    In (z8 (ANum UCells.REAL_MEMCHR) UCells.MUSL_MEMCHR) (as_const B ly) /\
    In (z8 (ANum UCells.GOT_REAL_MEMCPY) UCells.REAL_MEMCPY) (as_const B ly) /\
    uci_tab_zshadow_at B UCI_MARGIN_MAX.

Section leaf. Context {rc : YM05.RunCeil}.
Variable B : asyms.
(* A leaf statement of lib/A/Prog/<leaf>_cg.v, closed over the Section Variables of the shared kit
   lib/A/Prog/LeafCgKit.v (world .. as_tp), read at this unit's allocator model (lib/Reusable YA0n / YG0f / YG0n /
   YG0d / YK04 / YK0s), image A's segments and the record B. *)
Definition uci_leaf_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
(* A leaf that writes a caller buffer also takes aowned, for the kit's premise `forall x, in_wr WR x -> ... ~ aowned
   ly S x /\ ~ in_img x` (LeafCgKit.v leaf_cg_of_evtF_stmt). rp_hot_clamp writes the 20 bytes of check_clamp's local
   struct inside check_clamp's live class-1 fake frame: a byte of a live frame is an aclient_byte (YG0n.v), so it is
   never aowned (aowned requires ~ aclient_byte), and AR_laws' al_client_img (YG0d.v) keeps it out of the image. *)
Definition uci_leaf_wr_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> (alayout -> astate -> Z -> Prop) -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world tfibsegs) (@w_H tfibsegs) (SRr tfibsegs) alayout astate (@AR rc tfibsegs B) (aview tfibsegs)
    same_but_materialized ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B).
End leaf.
