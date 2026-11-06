(* check_round_trip_cg: the ASan walk contract of check_round_trip (fuzz_decode.asan-ubsan, listing
   name DB_check_round_trip, AF_check_round_trip of lib/B/Prog/DecodeBList.v), in cgif_file_fuzzer's program-contract form, as
   STATEMENTS only (no proof). Form: cgif's allocator-calling caller-journal contract (origin/ossv/recipes c8557374ad2e,
   proofs/cgif/cgif_file_fuzzer/lib/YCey.v:167 trfc_specX, lib/YC20.v:350 tlzw_spec): the caller's journal is the
   premise, the post extends it by the call's events, the allocations are metered (mo_ok / mo_le), and the blocks the
   call allocates are all freed (Permutation of ablocks). A callee (reac_braid_encode, and the float code of
   check_round_trip itself) writes float registers, so the return is cgif's exists-fx' form (lib/YL0g.v:58-64).

   The C (projects/libreac/fuzz_decode/source/fuzz_decode.c:103-129): planes = malloc(4 nch ns), planar = malloc(8 nch),
   again = calloc(3 nch ns, 1) (abort on NULL), the planar 24-bit samples of pcm to floats, reac_braid_encode into again,
   memcmp(again, audio, 3 nch ns) (abort when not 0), free(again), free(planar), free(planes) (the last one a tail call).
   The listing's calls: two PCall DB___interceptor_trampoline_malloc, one PCall DB___interceptor_trampoline_calloc,
   one PCall DB_reac_braid_encode, one PCall DB___interceptor_trampoline_bcmp, two PCall and one PTail
   DB___interceptor_trampoline_free; the abort / report calls are on paths the premises exclude.

   The core definitions that are not yet on fuzz_decode are Section Variables named and typed as cgif_file_fuzzer names
   them, so the swap to the relocated core is a rename. The allocator model the calloc kit relocated (lib/Reusable YG0*,
   YCbq, YC5d, YGCalloc) is used directly. Every sink_head / FPState / RunCeil instance is passed explicitly, and the
   plain build's global instances are removed below so that none can be inferred. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require check_braid_c reac_braid_encode_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DCBc := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_c.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.AsanCells.
Module LBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_braid_encode_cg.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_round_trip's own frame: 160 bytes (its first instruction, `addi sp, sp, -160`, at DB_check_round_trip). Its
   allocator calls use ASTACK below their sp, as the malloc rule asks (YC5d.v:61). *)
Definition DEC_CRT_FRAME : Z := 160.
Definition DEC_CRT_STK : Z := DEC_CRT_FRAME + ASTACK.
(* malloc, malloc, calloc, free, free, free: one model event each (YC5d.v:71, :92; YGCalloc.v:245). *)
Definition DEC_CRT_EV : Z := 6.
(* Live bytes it adds: 4 nch ns + 8 nch + 3 nch ns <= 7 * 480 + 8 * 127 = 4376 under its geometry premises. *)
Definition DEC_CRT_LIVE : Z := 2 ^ 13.

(* The trace the allocator records at a call: the call's return address and the return addresses of the
   frame-pointer chain after it (YG00.v:375 unwind_of_chain; YG0d.v call_trace0 and YGCalloc.v:216 ctrace0 are this at
   ras = raZ regs :: spine ch). *)
Definition dec_utrace (pc0 : Z) (ras : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) ras).

(* The return addresses of check_round_trip's allocator calls, as offsets from its entry (the jal is 4 bytes before):
   malloc at +0x64 and +0x74, calloc at +0x90, free at +0x2a0 and +0x2a8. The tail free (`j` at +0x2e8, a PTail of the
   listing) returns to check_round_trip's own caller. *)
Definition DEC_CRT_RA_MALLOC1 : Z := decodeb_sigma DB_check_round_trip + 0x68.
Definition DEC_CRT_RA_MALLOC2 : Z := decodeb_sigma DB_check_round_trip + 0x78.
Definition DEC_CRT_RA_CALLOC : Z := decodeb_sigma DB_check_round_trip + 0x94.
Definition DEC_CRT_RA_FREE1 : Z := decodeb_sigma DB_check_round_trip + 0x2a4.
Definition DEC_CRT_RA_FREE2 : Z := decodeb_sigma DB_check_round_trip + 0x2ac.

(* Every cell of asan_cells lies inside one loaded segment of the image (bookkeeping, decided by vm_compute). *)
Definition dec_seg_covers (a n : Z) : bool :=
  existsb (fun s : Segment => (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
    decodesegsB0.
Definition dec_asan_cell_ranges : list (Z * Z) :=
  [(DCells.CELL_K, 8); (DCells.GOT_CELL_K, 8); (DCells.INITED, 1); (DCells.REPLACE, 1); (DCells.GOT_REPLACE, 8);
   (DCells.UAR, 4); (DCells.GOT_UAR, 8); (DCells.CANPOISON, 1); (DCells.HIEND, 8); (DCells.GOT_HIEND, 8);
   (DCells.MIDBEG, 8); (DCells.GOT_MIDBEG, 8); (DCells.MIDEND, 8); (DCells.GOT_MIDEND, 8); (DCells.REAL_MEMCPY, 8);
   (DCells.REAL_MEMSET, 8); (DCells.GOT_REAL_MEMSET, 8)].
Lemma dec_asan_cells_in_seg : forallb (fun r => dec_seg_covers (fst r) (snd r)) dec_asan_cell_ranges = true.
Proof. vm_compute. reflexivity. Qed.

(* The read-only bytes the walks read through the image view, as (base, size) ranges (in_zr, YG0n.v:197):
   the union of the direct read-only loads of LLVMFuzzerTestOneInput, check_round_trip, reac_braid_encode and
   reac_frame_clean_len, measured on the pinned image (decode/RO-READS.md, ro_reads.py, image B), and the REAC_MODE
   table words:
     (0x10310, 8)  ÷36 multiplier 0x8e38e38e38e38e39: `ld` at 0x803e8 (LLVMFuzzerTestOneInput), 0x81598 (clean_len A_M)
     (0x10360, 8)  0x71c71c71c71c71c: `ld` at 0x803f4 (LLVMFuzzerTestOneInput)
     (0x103c8, 8)  0x71c71c71c71c71d: `ld` at 0x815a0 (clean_len A_T)
     (0x20dcc, 4)  FCLAMP_HI 0x4afffffe: `flw` at 0x81d78 (reac_braid_encode)
     (0x20d64, 8)  REAC_MODE_44K1 + 4 (channels, 40) and + 8 (samples, 12)
     (0x20d84, 8)  REAC_MODE_48K + 4 (channels, 40) and + 8 (samples, 12)
     (0x20da4, 8)  REAC_MODE_96K + 4 (channels, 40) and + 8 (samples, 12)
   check_round_trip has no read-only read. The walks reach the table words through the .got pointer cells (the
   pointer rows of dec_crt_cells). The three tables are registered ASan globals (asan_globals at 0x9dbb0: beg
   0x20d60 / 0x20d80 / 0x20da0, size 12, size_with_redzone 32): their payload is program data, never an owned static,
   so it cannot be a constant cell (YG0n.v:212 am_const_owned) and is read through the image view. The div-by-36 word
   0x10338 is not here: it is an owned constant cell (dec_crt_cells' last row).
   `dec_in_ro_rd` is the membership the lanes' cut Props use (crtA_in_ro_rd's shape). *)
Definition DEC_RO_RD : list (Z * Z) :=
  [(0x10310, 8); (0x10360, 8); (0x103c8, 8); (0x20dcc, 4); (0x20d64, 8); (0x20d84, 8); (0x20da4, 8)].
Definition dec_in_ro_rd (a : Z) : Prop := Exists (in_zr a) DEC_RO_RD.
(* The read-only view at the DEC_RO_RD bytes only: rom_view (YG0d.v:382) scoped to what the walks read. *)
Definition dec_rom_view_rd (W : world decodesegsB0) (mem : word -> option byte) : Prop :=
  forall a, dec_in_ro_rd a ->
    aview decodesegsB0 (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom decodesegsB0 (Z_to_bv 64 a)).

(* Every DEC_RO_RD byte lies in a non-writable loaded segment, and the image holds a byte there, so the read-only
   view at it is Some (decided by vm_compute). The table words lie inside their globals' ASan slots; what keeps every
   DEC_RO_RD byte out of the owned statics is the instance fact dec_ro_rd_unowned below. *)
Definition dec_rom_b (a : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
                             (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool decodesegsB0.
Definition dec_img_b (a : Z) : bool :=
  match YK11.seg_rom decodesegsB0 (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition dec_zr_bytes (r : Z * Z) : list Z := map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r))).
Lemma dec_ro_rd_clean :
  forallb (fun r => forallb (fun z => dec_rom_b z && dec_img_b z)%bool (dec_zr_bytes r)) DEC_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_zr_enum (P : Z -> bool) (Lr : list (Z * Z)) (a : Z) :
  forallb (fun r => forallb P (dec_zr_bytes r)) Lr = true -> Exists (in_zr a) Lr -> P a = true.
Proof.
  intros HF HE. apply Exists_exists in HE as [r [Hin [H1 H2]]].
  rewrite forallb_forall in HF. specialize (HF r Hin). rewrite forallb_forall in HF.
  apply HF. unfold dec_zr_bytes. apply in_map_iff. exists (Z.to_nat (a - fst r)). split.
  - rewrite Z2Nat.id by lia. lia.
  - apply in_seq. split; [lia|]. rewrite Nat.add_0_l. apply Z2Nat.inj_lt; lia.
Qed.
Lemma dec_rom_b_in_rom (a : Z) : dec_rom_b a = true -> in_rom decodesegsB0 a.
Proof.
  unfold dec_rom_b, in_rom. intro H. apply existsb_exists in H as [sg [Hin H]].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists sg. repeat split; auto; lia.
Qed.
Lemma dec_img_b_some (a : Z) : dec_img_b a = true -> exists b : byte, YK11.seg_rom decodesegsB0 (Z_to_bv 64 a) = Some b.
Proof.
  unfold dec_img_b. destruct (YK11.seg_rom decodesegsB0 (Z_to_bv 64 a)) as [b|]; intro H; [exists b; reflexivity | discriminate H].
Qed.
(* Two conjuncts (the walks destruct it as [Hrom _]): the byte is read-only, and the image holds it. *)
Lemma dec_ro_rd_rom_clean (a : Z) :
  dec_in_ro_rd a -> in_rom decodesegsB0 a /\ exists b : byte, YK11.seg_rom decodesegsB0 (Z_to_bv 64 a) = Some b.
Proof.
  intro H. pose proof (dec_zr_enum _ _ a dec_ro_rd_clean H) as HP.
  cbv beta in HP. apply andb_true_iff in HP as [HR HI].
  split; [exact (dec_rom_b_in_rom a HR) | exact (dec_img_b_some a HI)].
Qed.

(* The two instance facts about the asyms record B (OBLIGATIONS, owner: the core / start-up side; discharged at the
   concrete record): no DEC_RO_RD byte is an owned static (by vm_compute over as_owned_static B, the record's
   ts_owned), and errno (writable .bss) is not in the read-only image. The first is scoped to DEC_RO_RD: image A's
   generated record owns read-only bytes outside every ASan slot (0x102e8, for one), so a fact about all read-only
   owned statics would be false there. *)
Definition dec_ro_rd_unowned (B : asyms) : Prop :=
  forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B).
Definition dec_rom_no_errno (B : asyms) : Prop :=
  forall a, in_rom decodesegsB0 a -> ~ (as_errno B <= a < as_errno B + 4).
(* From them, the scoped fact the journal's image clause (YCbq.v:362) needs at each DEC_RO_RD byte. *)
Lemma dec_ro_rd_scoped (B : asyms) : dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  forall a, dec_in_ro_rd a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros HO HE a H. destruct (dec_ro_rd_rom_clean a H) as [HR _]. split.
  - exact (HO a H).
  - exact (HE a HR).
Qed.

(* The value-0 shadow granule at T of a table (the granule [T, T + 8) of its payload) as a fact of the record: it lies
   inside a range of as_zero_shadow B (YG0f.v:177; the record's Tfib_zero_shadow by ts_zsh). It cannot be a constant
   cell: a constant cell must be owned_core (YG0n.v:201-204, :212 am_const_owned), and a shadow byte is owned_core only
   as the shadow of an owned static, while [T, T + 8) is unowned program data. ARm's am_zshadow (YG0n.v:218,
   zshadow_ok :188-191) reads every as_zero_shadow range's shadow as 0 at every AR state; dec_tab_zshadow_rd below is
   that read at T. *)
Definition dec_tab_zshadow_at (B : asyms) (T : Z) : Prop :=
  exists r, In r (as_zero_shadow B) /\ fst r mod 8 = 0 /\ fst r <= T /\ T + 8 <= fst r + snd r.
Lemma dec_tab_zshadow_rd {rc : YM05.RunCeil} (B : asyms) ly S (W : world decodesegsB0) mem md (T : Z) :
  @AR rc decodesegsB0 B ly S W mem md -> T mod 8 = 0 -> dec_tab_zshadow_at B T ->
  aview decodesegsB0 (w_H W) mem (DCells.shadow_addr T) = Some 0.
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
  replace (DCells.shadow_addr T) with (shadow_of_addr SHADOW_OFF (fst r) + (T - fst r) / 8); [exact Z|].
  rewrite Ei. unfold shadow_of_addr, DCells.shadow_addr, DCells.ASAN_K, SHADOW_OFF. lia.
Qed.

Section crt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* cgif's tfib_sink_head (cgif lib/YE2k.v:44), at fuzz_decode's own sink head: lib/A/DecodeCalloc.v's
   dec_B_sink_head (musl's ofl_head of image B). *)
Local Abbreviation tfib_sink_head := dec_B_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The meter cost of one call: its three allocations and three frees (cgif lib/YCey.v:69 RFC_COST form). *)
Definition dec_crt_cost (nch ns : Z) : Z :=
  mo_malloc MT (4 * (nch * ns)) + mo_malloc MT (8 * nch) + mo_malloc MT (3 * (nch * ns)) +
  (mo_free MT + mo_free MT + mo_free MT).

(* The braid relation of audio and pcm (lib/B/Prog/check_braid_c.v:17-21 braid_map, read through cgif's view of the
   world instead of decode's mrd): sample (ch, s) of pcm is the three bytes the braid puts it in. *)
Definition dec_crt_braid (rd : reader) (audio pcm nch ns : Z) : Prop :=
  forall ch s j, 0 <= ch < nch -> 0 <= s < ns -> 0 <= j < 3 ->
    exists b : Z, rd (pcm + 3 * (ch * ns + s) + j) = Some b /\
      rd (audio + 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j) = Some b.

(* The runtime cells the program leaves read (asan_cells, lib/B/AsanCells.v:55-65), kept the way cgif keeps its
   runtime cells across allocator calls: as constant cells of the asyms record. as_const (lib/Reusable/YG0f.v:174) is
   re-read at every state, since AR (YG0n.v:490) includes ARm and ARm.am_const (YG0n.v:211) is
   `Forall (cell_holds B ly rd) (as_const B ly)` at rd = aview (YG0f.v:263-266); cgif's B lists its cells in
   Tfib_const_abs (lib/A/AF0m.v:28, as_const := Tfib_const at lib/A/AD2l.v:33). asyms_ok asks only the four shadow / uar
   cells, so fuzz_decode's B must list all 17, with asan_cells' widths (z8 / z4 / z1, YG0f.v:115-118) and values:
   CELL_K = ASAN_K (0x7fff8000, cgif's SHADOW_OFF), INITED / REPLACE / CANPOISON = 1, UAR = 1, HIEND = 0x7fffffffffff,
   MIDBEG / MIDEND = 0, the GOT words = their cells, REAL_MEMCPY / REAL_MEMSET = musl's memcpy / memset. These values
   must equal the generated AF0m's and the start-up state's (G15). cell_holds reads aview; every cell lies in a loaded
   segment (dec_asan_cells_in_seg), where the world hides no byte (YA0n.v w_Hoff, YK04.v:38 H_off_segments), so aview
   there is mrd, which asan_cells reads. *)
Definition dec_crt_cells : Prop :=
  forall ly,
    In (z8 (ANum DCells.CELL_K) DCells.ASAN_K) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_CELL_K) DCells.CELL_K) (as_const B ly) /\
    In (z1 (ANum DCells.INITED) 1) (as_const B ly) /\
    In (z1 (ANum DCells.REPLACE) 1) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_REPLACE) DCells.REPLACE) (as_const B ly) /\
    In (z4 (ANum DCells.UAR) 1) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_UAR) DCells.UAR) (as_const B ly) /\
    In (z1 (ANum DCells.CANPOISON) 1) (as_const B ly) /\
    In (z8 (ANum DCells.HIEND) 0x7fffffffffff) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_HIEND) DCells.HIEND) (as_const B ly) /\
    In (z8 (ANum DCells.MIDBEG) 0) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_MIDBEG) DCells.MIDBEG) (as_const B ly) /\
    In (z8 (ANum DCells.MIDEND) 0) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_MIDEND) DCells.MIDEND) (as_const B ly) /\
    In (z8 (ANum DCells.REAL_MEMCPY) DCells.MUSL_MEMCPY) (as_const B ly) /\
    In (z8 (ANum DCells.REAL_MEMSET) DCells.MUSL_MEMSET) (as_const B ly) /\
    In (z8 (ANum DCells.GOT_REAL_MEMSET) DCells.REAL_MEMSET) (as_const B ly) /\
    (* The three GOT pointer words LLVMFuzzerTestOneInput reads to pick the sample format: decodeb_obj 4 / 5 / 6
       (0x99f60 / 0x99f68 / 0x99f70), in .got (file-backed, never relocated in this static image); read on the pinned image. *)
    In (z8 (ANum (decodeb_obj 4%nat)) 0x20d60) (as_const B ly) /\  (* REAC_MODE_44K1: pointer word *)
    In (z8 (ANum (decodeb_obj 5%nat)) 0x20da0) (as_const B ly) /\  (* REAC_MODE_96K: pointer word *)
    In (z8 (ANum (decodeb_obj 6%nat)) 0x20d80) (as_const B ly) /\  (* REAC_MODE_48K: pointer word *)
    (* The shadow of the three REAC_MODE tables, this image's asan_globals (section asan_globals, 3 descriptors,
       beg = 0x20d60 / 0x20d80 / 0x20da0, size 12, size_with_redzone 32; symbols REAC_MODE_44K1 / _48K / _96K,
       st_size 32 = the 12-byte object + ASan padding): 0 for the granule at the base and 4 for the next one
       (12 = 8 + a 4-byte partial granule); start-up writes it (__asan_register_elf_globals), and a Theorem Labs lane's
       at-main state gates the values. The rows use the unit's shadow mapping, DCells.shadow_addr a = a / 8 + ASAN_K
       with ASAN_K = 0x7fff8000 (lib/B/AsanCells.v:21, the SHADOW_OFF + a / 8 of lib/Reusable/YG0f.v:87): the
       granules of [T + 4, T + 12) are the ones at T and T + 8. Shadow 4 is what the leaves' `addressable m (mode + 4) 8`
       needs: shadow_ok a 4 holds for a mod 8 < 4, which is T + 8 .. T + 11. The value-4 granule's shadow byte is a
       constant cell (it is also the shadow of the owned redzone tail T + 12). The value-0 granule's is not (see
       dec_tab_zshadow_at): its row states that [T, T + 8) lies in an as_zero_shadow B range, and
       dec_tab_zshadow_rd reads the 0 from AR. The rows keep their positions (21-26). The table words themselves are
       not rows: the walks read them through the image view (DEC_RO_RD). *)
    dec_tab_zshadow_at B 0x20d60 /\  (* REAC_MODE_44K1: shadow granule 0 is 0 (as_zero_shadow) *)
    In (z1 (ANum (DCells.shadow_addr 0x20d68)) 4) (as_const B ly) /\  (* REAC_MODE_44K1: shadow granule 1, 4 bytes addressable *)
    dec_tab_zshadow_at B 0x20da0 /\  (* REAC_MODE_96K: shadow granule 0 is 0 (as_zero_shadow) *)
    In (z1 (ANum (DCells.shadow_addr 0x20da8)) 4) (as_const B ly) /\  (* REAC_MODE_96K: shadow granule 1, 4 bytes addressable *)
    dec_tab_zshadow_at B 0x20d80 /\  (* REAC_MODE_48K: shadow granule 0 is 0 (as_zero_shadow) *)
    In (z1 (ANum (DCells.shadow_addr 0x20d88)) 4) (as_const B ly) /\  (* REAC_MODE_48K: shadow granule 1, 4 bytes addressable *)
    (* The div-by-36 magic the listing calls decodeb_obj 9 (0x10338, both images): LLVMFuzzerTestOneInput loads it
       with an 8-byte `ld` at 0x80904, and reac_upstream_channels / reac_upstream_decode read it too. *)
    In (z8 (ANum (decodeb_obj 9%nat)) 0xe38e38e38e38e38f) (as_const B ly).

(* What a call leaves: the caller's journal extended by DEC_CRT_EV events, callee-saved registers kept, no fake frame
   added, the caller's blocks exactly (all three temporaries freed), every byte outside the call's stack window kept
   (YCbq.v:824 acall_kept with no written range), the meter charged dec_crt_cost, and any float state with the
   rounding mode still zero (YL0g.v:60-62). *)
Definition dec_crt_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (nch ns : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx' regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    frm_zero (@fp_csr fx') /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + DEC_CRT_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - DEC_CRT_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 (dec_crt_cost nch ns).

(* The contract at entry address a, for call contexts CTX (cgif lib/YC20.v:350 tlzw_spec's (a, CTX) parameters).
   audio (a0) and pcm (a1) lie inside two of the caller's blocks, nch (a2) is even in 2..127, ns (a3) in 1..12 and the
   region 3 nch ns at most REAC_AUDIO_BYTES = 1440 (the plain contract's premises, lib/Prog/check_round_trip_c.v:33),
   and the braid relation holds, so the memcmp finds the region equal and no abort is reached. The calloc rule
   (YGCalloc.v:255 acalloc04_rule, at lib/Lib/DecodeCallocKit.v's DEC_CALLOC_MAX = 4572 and DEC_CALLOC_DEPTH = 2192) asks
   nm * sz <= 4572, which 3 * nch * ns <= 1440 gives (nm = 3 nch ns, sz = 1), and ly_bot lyc + 2192 < sp at its call,
   where sp = spZ regs - DEC_CRT_FRAME: that is the stack-depth premise below. ly_bot (YG0f.v:63, ly_top - kStackSpan)
   is kept by every journal step (layout_le keeps ly_top, YG0f.v:65-68), so the caller discharges it from its own
   astk_ok (YCbq.v:333-335). The read-only view is asked only at the bytes the walks read,
   dec_rom_view_rd W memc (the DEC_RO_RD bytes). The caller derives it from rom_view at LLVMFuzzerTestOneInput's entry
   (dec_lib_pre_x), the journal's image clause (YCbq.v:362), which keeps aview outside the owned statics and errno,
   and dec_ro_rd_scoped, which puts every DEC_RO_RD byte outside both under the holds statement's two instance facts.
   The full rom_view is not asked here: the journal does not keep the owned redzone bytes. *)
Definition dec_check_round_trip_cg (a : Z) (CTX : list (list Z)) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (audio pcm nch ns bA nA bP nP T : Z) ch,
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 audio -> YK11.getr regs 11 = w64 pcm ->
    YK11.getr regs 12 = w64 nch -> YK11.getr regs 13 = w64 ns ->
    @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - DEC_CRT_STK -> spZ regs <= sp0 ->
    frm_zero (@fp_csr fx) ->
    Z.even nch = true -> 2 <= nch <= 127 -> 1 <= ns <= 12 -> 3 * nch * ns <= 1440 ->
    ly_bot lyc + DEC_CALLOC_DEPTH + DEC_CRT_FRAME < spZ regs ->
    In (bA, nA) (ablocks B lyc Sc) -> bA <= audio -> audio + 3 * nch * ns <= bA + nA ->
    In (bP, nP) (ablocks B lyc Sc) -> bP <= pcm -> pcm + 3 * nch * ns <= bP + nP ->
    dec_crt_braid (aview segs (w_H W) memc) audio pcm nch ns ->
    dec_rom_view_rd W memc ->
    st_nev S + k + DEC_CRT_EV <= EV_MAX -> blocks_bytes Sc + DEC_CRT_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> dec_crt_cost nch ns <= T ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (dec_crt_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).

(* A leaf statement of lib/B/Prog/<leaf>_cg.v, closed over the Section Variables of the shared kit
   lib/B/Prog/LeafCgKit.v (world .. as_tp, and aowned for the four leaves that write a buffer), read at this unit's
   allocator model (lib/Reusable YA0n / YG0f / YG0n / YG0d / YK04 / YK0s), image B's segments and the asyms B. *)
Definition dec_leaf_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
    ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
(* The four leaves that write a caller buffer (reac_decode, reac_decode_plain_le, reac_upstream_decode,
   reac_braid_encode) also take aowned, for their premise `forall x, in_wr WR x -> ... ~ aowned ly S x /\ ~ in_img x`
   (LeafCgKit.v:140). Every buffer they write is a live block of the caller's AR (malloc'd or calloc'd), so the premise
   comes from AR_laws: al_blocks (YG0d.v:423-429: apresent, not aowned) and al_client_img (YG0d.v:490-495: not in the
   image). *)
Definition dec_leaf_wr_at
    (L : YK11.FPState -> forall world : Type, (world -> word -> bool) ->
         (world -> config -> (world -> config -> Prop) -> Prop) -> forall alayout astate : Type,
         (alayout -> astate -> world -> (word -> option byte) -> Model -> Prop) ->
         ((word -> bool) -> (word -> option byte) -> Z -> option Z) -> (Model -> Model -> Prop) ->
         (alayout -> Z) -> (alayout -> Z) -> (word -> Prop) -> Z -> Z -> (alayout -> astate -> Z -> Prop) -> Prop)
    (fx' : YK11.FPState) : Prop :=
  L fx' (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
    ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B).

(* The traces the six allocator calls record, which the call rules ask to be in the trace universe (YC5d.v:66, :86;
   YGCalloc.v:240). Which chain each call sees is fixed by s0 at the call (YG0d.v:218-223 chain_pre, YG00.v:367
   bad_next):
   - the tail free (+0x2e8): the epilogue has restored ra and s0, so the trace is the free's pc followed by the entry
     context c = raZ :: spine ch itself (cgif's HUCTX form, lib/A/AC8s.v:79-83);
   - the two mallocs and the calloc: s0 holds nch * ns (`mul s0, a3, a2` at +0x54, before the first malloc), at most
     1440, so below sp, hence bad_next and an empty chain; the two frees: s0 holds again (reloaded from 8(sp) at +0x26c),
     a block below alloc_ceiling and so below sp, the same: these five traces are fixed. *)
(* The trace pc0 values are the record's for fuzz_decode's ORIGINAL image B (a Theorem Labs lane's audit rows T1-T12, long
   branch, malloc_context_size 30): pc_malloc_ra0 (as_code B) 0x52250, pc_free_ra0 (as_code B) 0x520f0, DEC_B_calloc_ra0 0x52484.
   They enter only through as_code B and DecodeCalloc.v; the short-branch values are wrong. *)
Definition dec_crt_uctx (CTX : list (list Z)) : Prop :=
  forall c, In c CTX -> In (dec_utrace (pc_free_ra0 (as_code B)) c) (as_universe B).
Definition dec_crt_ufix : Prop :=
  In (dec_utrace (pc_malloc_ra0 (as_code B)) [DEC_CRT_RA_MALLOC1]) (as_universe B) /\
  In (dec_utrace (pc_malloc_ra0 (as_code B)) [DEC_CRT_RA_MALLOC2]) (as_universe B) /\
  In (dec_utrace DEC_B_calloc_ra0 [DEC_CRT_RA_CALLOC]) (as_universe B) /\
  In (dec_utrace (pc_free_ra0 (as_code B)) [DEC_CRT_RA_FREE1]) (as_universe B) /\
  In (dec_utrace (pc_free_ra0 (as_code B)) [DEC_CRT_RA_FREE2]) (as_universe B).

(* The code addresses the call rules are stated at (amalloc04_rule at pc_wrap_malloc, afree04_rule at pc_wrap_free,
   YC5d.v:68, :89) are the listing's trampolines, in cgif's PALib form (lib/YC1f.v:309-310 pal_free / pal_malloc). The
   calloc and bcmp rules take the listing's address directly. *)

(* The statement the walk will prove: the callee contracts and the trace-universe facts give the contract at
   DB_check_round_trip for the contexts CTX. The calls after the float code (bcmp, the frees) run under another float
   state, so the runtime contracts are taken for every one. *)
Definition dec_check_round_trip_cg_holds_stmt (CTX : list (list Z)) : Prop :=
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_crt_cells ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  dec_crt_uctx CTX -> dec_crt_ufix ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @acalloc04_rule fx' segs B (as_universe B) ajournal (@acall_kept rc segs B)
     (mo_ok MT) (mo_le MT) (mo_malloc MT) (decodeb_sigma DB___interceptor_trampoline_calloc) DEC_B_calloc_ra0
     DEC_CALLOC_MAX DEC_CALLOC_DEPTH) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, dec_leaf_wr_at (@LBraid.dec_reac_braid_encode_cg) fx') ->
  dec_check_round_trip_cg (decodeb_sigma DB_check_round_trip) CTX.
End crt.
