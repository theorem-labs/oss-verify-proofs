(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 121 of its 179 lines of code are new or changed and 1315 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_ret.v; 338 of its 365 lines of code are new or changed and 152 lines of the source are left out. *)
(* The struct pj kit for fs's ASan walks: the reader specs' Lib form of a struct pj field (lib/Prog/PjStruct.v pj_u64 /
   pj_u32 / pj_hdr, over Lib/Mem.v bytes_at) carried to YI04's val_mem form, and from a spec's pj_hdr to the object
   region a walk puts in FSW_K.v fsw_entryT_argsX's rs, with the atom facts for its gf. ONE copy for pj_set, grow,
   pj_get, pj_free, pj_get_str and the writer lanes. Every lemma is general in the segments and the memory, so it reads
   the reader specs' `PjStruct.pj_hdr segs (rdW W mem) ...` at segs := tfibsegs, m := mrestrict (w_H W) mem (rdW, FSH_Gen.v
   / FSH_Fn_reader.v). A-specific: the X lemmas (the kit's env Ereg regs (fs_extraT ++ xs)) and the disjointness lemmas
   (fsT_regions' two shadow-base cells).
   struct pj (preset_file.h, 56 bytes; the offsets the code uses, a Theorem Labs lane's state-port/pj_set-grow-shape.md): type
   (u32) at 0, num 8, str 16, kids 24, keys 32, n 40, cap 48. The object region has base atom b (the register or extra
   atom that holds the object's address), extent [0, 56) and one chunk per field that pj_set and grow load: type
   (CVal 4), kids, keys, n, cap (CVal 8), each holding its field atom. Its WRITE WINDOW must lie inside the walk's FP
   (every byte of a window needs awr_byte), so it is a parameter: pj_obj_regionW b wlo whi ... (window [wlo, whi), empty
   or inside [0, 56)), pj_obj_regionR (read only, window empty) and pj_obj_region (window [0, 56), = pj_obj_regionW at
   [0, 56), pj_obj_region_W; its lemmas are corollaries of the W ones). These whole-object lemmas take pj_hdr AT THE
   REGION'S MEMORY. Under the kit's ATOM CONVENTION (FSW_K.v xatom, env Ereg regs (fs_extraT ++ xs)), the X forms
   (pj_obj_regionWX / RX / X b j) take the five field atoms from xatom j on in field order, xs holding pj_fields ty kids
   keys n cap at j (j = 4 after the four alloc.c statics). A walk whose FP covers SEVERAL pieces of the object (grow:
   [v + 24, v + 40) and [v + 48, v + 56)), whose address registers after a call hold v + d, or which holds only val_mem
   field facts at a post-call memory, splits the object into parts: fsw_pj_part_okR (read only: bounds and chunks),
   fsw_pj_part_okW (a window: bounds, pobj's writability conjunct, chunks), fsw_pj_part_ok (pj_rw), each for any base
   atom, extent and chunk list inside [v, v + 56); chunks from YI04 chunk_ok_val (val_mem) or fsw_pj_chunk8 /
   fsw_pj_chunk4 (pj_u64 / pj_u32); fsw_pj_parts_disjX for rs.
   PORTED, the donor bodies copied rather than imported, so that no plain-image module (Contract, Img0) enters this ASan
   file. Donors (object ids identical on ossv/recipes 566eb6ffa5d, release/pau-projects-recipes b6a0088adcb, S0
   71efad42f00 and kit 259ea2daea9): lib/KindBGlue.v 6cb1bd7d29, lib/Prog/pj_write.v 3ad1a23c18, lib/Prog/put_kb.v
   24a463fa6a. Each ported lemma names its donor line below.
   NEW TEXT: the val_mem forms of pj_u64 / pj_u32 (the measured route), the chunk / part / region / atom-fact /
   disjointness lemmas, pj_obj_region(W / R)(X), pj_in_obj, pj_fields, pj_obj_facts(X).
   The released lib/Prog and lib/Lib modules are Required, never Imported (their getr / mkst / seg_rom shadow YK11's).
   A kit: no function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ---- byte helpers, ported ---- *)
(* Port-from: lib/KindBGlue.v:100 kb_nth_le_bytes, verbatim (Section Words, general in segs). *)
Lemma fpj_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.
(* Port-from: lib/KindBGlue.v:109 kb_le_byte_bv; le_byte written YO0f.le_byte (the one YI04's val_mem and YO0d's
   word_mem use; YG0f, imported above for the kit, has a second le_byte). *)
Lemma fpj_le_byte_bv8 : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (YO0f.le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.
(* Port-from: lib/Prog/put_kb.v:188 le_byte_bv (le_byte -> YO0f.le_byte, Z_to_bv8_mod -> Mem.Z_to_bv8_mod). *)
Lemma fpj_le_byte_bv : forall v w k,
  Z_to_bv 8 (YO0f.le_byte v w k) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)).
Proof. intros. unfold YO0f.le_byte. apply Mem.Z_to_bv8_mod. apply Z.mod_mod. lia. Qed.
(* Port-from: lib/Prog/put_kb.v:191 mbyte_mrd, restated over segs (the donor is pinned to rsegs). *)
Lemma fpj_mbyte_mrd : forall m a, mbyte segs m a = Mem.mrd segs m (Mem.wa a).
Proof. reflexivity. Qed.
(* Port-from: lib/Prog/put_kb.v:207 le4_byte (Z_to_bv8_mod / shiftr_mod_mod8 -> Mem.). *)
Lemma fpj_le4_byte : forall v k, (k < 4)%nat ->
  Z_to_bv 8 (Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k)) =
  Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat 4)) (8 * Z.of_nat k)).
Proof.
  intros v k Hk. apply Mem.Z_to_bv8_mod. change (8 * Z.of_nat 4) with 32.
  rewrite !Mem.shiftr_mod_mod8 by lia. reflexivity.
Qed.

(* ---- the 8-byte field ---- *)
(* Port-from: lib/KindBGlue.v:193 bytes_at_le8_word (kb_nth_le_bytes / kb_le_byte_bv -> the copies above). *)
Lemma fsw_pj_bytes_at_le8_word : forall mem a w,
  Mem.bytes_at segs mem a (Mem.le8 w) -> YO0d.word_mem segs mem a (bv_unsigned w).
Proof.
  intros mem a w (Ha & Hb & H) k Hk.
  pose proof (bv_unsigned_in_range 64 w) as Hr.
  rewrite fpj_le_byte_bv8 by exact Hr.
  rewrite Mem.length_le8 in H. specialize (H k Hk). unfold Mem.le8, word_to_le_bytes in H.
  rewrite fpj_nth_le_bytes in H by exact Hk. exact H.
Qed.
(* Port-from: lib/KindBGlue.v:185 word_mem_le8 (the converse; helpers -> the copies above). *)
Lemma fsw_pj_word_mem_le8 : forall mem a v, YO0d.word_mem segs mem a v -> 0 <= v < 2 ^ 64 -> 0 <= a ->
  a + 8 <= 2 ^ 64 -> Mem.bytes_at segs mem a (Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros mem a v Hw Hv Ha Hb. split; [exact Ha|]. rewrite Mem.length_le8. split; [lia|].
  intros i Hi. unfold Mem.le8, word_to_le_bytes. rewrite fpj_nth_le_bytes by exact Hi.
  rewrite MState.unsigned_lit by lia. rewrite <- fpj_le_byte_bv8 by exact Hv. exact (Hw i Hi).
Qed.
(* NEW: the measured route (a Theorem Labs lane): split pj_u64, bytes_at_le8_word, MState.unsigned_lit, YI04.v:143
   val_mem_word_mem. *)
Lemma fsw_pj_u64_val : forall m a v, PjStruct.pj_u64 segs m a v -> val_mem segs m a 8 v.
Proof.
  intros m a v (Hv & Hb). apply val_mem_word_mem.
  pose proof (fsw_pj_bytes_at_le8_word m a _ Hb) as H. rewrite MState.unsigned_lit in H by exact Hv. exact H.
Qed.
(* NEW: the converse, for a walk's post (FSW_K.v fsw_field gives the val_mem of a field chunk). *)
Lemma fsw_val_pj_u64 : forall m a v, val_mem segs m a 8 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  PjStruct.pj_u64 segs m a v.
Proof.
  intros m a v H Hv Ha Hb. split; [exact Hv|].
  apply fsw_pj_word_mem_le8; [apply val_mem_word_mem; exact H | exact Hv | exact Ha | exact Hb].
Qed.

(* ---- the 4-byte field ---- *)
(* Port-from: lib/Prog/pj_write.v:92 pjw_word4_iff, RESTATED over segs: word4_mem B (Prog/put_c.v:44, the body of
   YI04's val_mem m a 4) -> val_mem segs, bytes_at rsegs -> Mem.bytes_at segs, and Hypothesis SEGS (pj_write.v:85,
   ms_segs B = rsegs) dropped. Body changes: `unfold word4_mem. rewrite SEGS.` -> `unfold val_mem.`; length_le4 / le4
   -> Mem.length_le4 / Mem.le4; mbyte_mrd / nth_Z_to_le / le_byte_bv / le4_byte -> fpj_mbyte_mrd (restated over segs) /
   fpj_nth_le_bytes (KindBGlue's copy of the same statement) / fpj_le_byte_bv / fpj_le4_byte. Nothing else. *)
Lemma fsw_pj_word4_iff : forall m a v, 0 <= a -> a + 4 <= 2 ^ 64 ->
  (val_mem segs m a 4 v <-> Mem.bytes_at segs m a (Mem.le4 (Z_to_bv 64 v))).
Proof.
  intros m a v Ha Hb. unfold val_mem. split.
  - intros H. split; [lia|]. split; [rewrite Mem.length_le4; lia|].
    intros i Hi. rewrite Mem.length_le4 in Hi. rewrite <- fpj_mbyte_mrd, H by exact Hi.
    unfold Mem.le4. rewrite fpj_nth_le_bytes by exact Hi. rewrite fpj_le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite fpj_le4_byte by exact Hi. reflexivity.
  - intros (_ & _ & H) k Hk. rewrite fpj_mbyte_mrd, H by (rewrite Mem.length_le4; exact Hk).
    unfold Mem.le4. rewrite fpj_nth_le_bytes by exact Hk. rewrite fpj_le_byte_bv, Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite fpj_le4_byte by exact Hk. reflexivity.
Qed.
(* NEW: pj_u32 in val_mem form (bytes_at carries the bounds), and the converse *)
Lemma fsw_pj_u32_val : forall m a v, PjStruct.pj_u32 segs m a v -> val_mem segs m a 4 v.
Proof.
  intros m a v (Hv & Hb). pose proof Hb as (Ha & Hl & _). rewrite Mem.length_le4 in Hl.
  apply (proj2 (fsw_pj_word4_iff m a v Ha ltac:(lia))). exact Hb.
Qed.
Lemma fsw_val_pj_u32 : forall m a v, val_mem segs m a 4 v -> 0 <= v < 2 ^ 32 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  PjStruct.pj_u32 segs m a v.
Proof.
  intros m a v H Hv Ha Hb. split; [exact Hv|]. apply (proj1 (fsw_pj_word4_iff m a v Ha Hb)). exact H.
Qed.

(* ---- NEW: chunks and the object region ---- *)
(* a field fact at base + off is the chunk off of a region based at base, holding any e that denotes the value *)
Lemma fsw_pj_chunk8 : forall E m base off (e : sv) x,
  PjStruct.pj_u64 segs m (base + off) x -> sv_denot E e = Z_to_bv 64 x ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E m base off e x Hx He. pose proof Hx as (Hr & _).
  apply (chunk_ok_val segs E m base off 8 e x He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  change (N.to_nat 8) with 8%nat. exact (fsw_pj_u64_val m (base + off) x Hx).
Qed.
Lemma fsw_pj_chunk4 : forall E m base off (e : sv) x,
  PjStruct.pj_u32 segs m (base + off) x -> sv_denot E e = Z_to_bv 64 x ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 4 e)).
Proof.
  intros E m base off e x Hx He. pose proof Hx as (Hr & _).
  apply (chunk_ok_val segs E m base off 4 e x He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  change (N.to_nat 4) with 4%nat. exact (fsw_pj_u32_val m (base + off) x Hx).
Qed.
(* NEW: a PART of a struct pj at v, based at atom b whose value p need not be v (an after-call state may hold v + 48 in
   s0): the extent [p + lo, p + hi) inside [v, v + 56), the write window [wlo, whi) empty or inside the extent
   (region_wf's window clause). A walk whose FP covers several pieces of the object puts one part per piece: grow's FP
   on v is [v + 24, v + 40) and [v + 48, v + 56), so n (v + 40) lies in no write window. The premises are what a walk
   holds at a POST-CALL memory: the bounds, and for a window the writability conjunct of FSH_Fn_reader.v pobj (its last
   conjunct, verbatim); the chunks come from val_mem facts (YI04 chunk_ok_val) or from pj_u64 / pj_u32 (fsw_pj_chunk8 /
   fsw_pj_chunk4). *)
Lemma fsw_pj_part_okW : forall E m b v p lo hi wlo whi cs,
  0 <= v -> v + 56 <= 2 ^ 64 -> (forall i, 0 <= i < 56 -> YP09.writable_at segs m (v + i)) ->
  bv_unsigned (ew E b) = p -> v <= p + lo -> p + hi <= v + 56 ->
  (whi <= wlo \/ lo <= wlo /\ whi <= hi) -> Forall (YP09.chunk_ok segs E m p) cs ->
  YP09.region_ok segs E m (YP09.mkRegion (Some b) lo hi wlo whi cs).
Proof.
  intros E m b v p lo hi wlo whi cs Hv0 Hv1 Hw Eb Hpl Hph Hwin Hcs. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eb.
  split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. destruct Hwin as [Hwin|Hwin]; [lia|].
  replace (p + o) with (v + (p + o - v)) by lia. apply Hw. lia.
Qed.
(* ... a READ-ONLY part (window empty): the bounds and the chunks, no writability *)
Lemma fsw_pj_part_okR : forall E m b v p lo hi cs,
  0 <= v -> v + 56 <= 2 ^ 64 ->
  bv_unsigned (ew E b) = p -> v <= p + lo -> p + hi <= v + 56 -> Forall (YP09.chunk_ok segs E m p) cs ->
  YP09.region_ok segs E m (YP09.mkRegion (Some b) lo hi 0 0 cs).
Proof.
  intros E m b v p lo hi cs Hv0 Hv1 Eb Hpl Hph Hcs. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eb.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
Qed.
(* ... where the walk holds PjStruct.pj_rw at that memory (e.g. from pj_hdr at a spec's entry): fsw_pj_part_okW *)
Lemma fsw_pj_part_ok : forall E m b v p lo hi wlo whi cs,
  PjStruct.pj_rw segs m v -> bv_unsigned (ew E b) = p -> v <= p + lo -> p + hi <= v + 56 ->
  (whi <= wlo \/ lo <= wlo /\ whi <= hi) -> Forall (YP09.chunk_ok segs E m p) cs ->
  YP09.region_ok segs E m (YP09.mkRegion (Some b) lo hi wlo whi cs).
Proof.
  intros E m b v p lo hi wlo whi cs (H8 & Hlo & Hhi & Hw) Eb Hpl Hph Hwin Hcs.
  exact (fsw_pj_part_okW E m b v p lo hi wlo whi cs Hlo Hhi (fun i Hi => proj1 (Hw (v + i) ltac:(lia)))
    Eb Hpl Hph Hwin Hcs).
Qed.
(* the whole object at v, based at atom b, all 56 bytes writable: fsw_pj_part_ok at p = v, extent and window [0, 56) *)
Lemma fsw_pj_region_ok : forall E m b v cs,
  PjStruct.pj_rw segs m v -> ew E b = Z_to_bv 64 v -> Forall (YP09.chunk_ok segs E m v) cs ->
  YP09.region_ok segs E m (YP09.mkRegion (Some b) 0 56 0 56 cs).
Proof.
  intros E m b v cs Hrw Eb Hcs. pose proof Hrw as (_ & Hlo & Hhi & _).
  apply (fsw_pj_part_ok E m b v v 0 56 0 56 cs Hrw);
    [rewrite Eb; apply MState.unsigned_lit; lia | lia | lia | right; lia | exact Hcs].
Qed.
End p.

(* the object region of the fields pj_set and grow load, the whole object writable (a walk that owns all 56 bytes) *)
Definition pj_obj_region (b aty akids akeys an acap : nat) : YP09.region :=
  YP09.mkRegion (Some b) 0 56 0 56
    [YP09.mkChunk 0 (CVal 4 (SOff aty 0)); YP09.mkChunk 24 (CVal 8 (SOff akids 0));
     YP09.mkChunk 32 (CVal 8 (SOff akeys 0)); YP09.mkChunk 40 (CVal 8 (SOff an 0));
     YP09.mkChunk 48 (CVal 8 (SOff acap 0))].
(* the same region with its write window [wlo, whi) a PARAMETER: pass the piece of the object the walk's FP covers
   (pj_set's FP on obj is [obj + 24, obj + 56): window [24, 56)); pj_obj_regionR is the read-only case (window empty), for
   a walk that only reads fields. pj_obj_region is pj_obj_regionW at [0, 56) (pj_obj_region_W). *)
Definition pj_obj_regionW (b : nat) (wlo whi : Z) (aty akids akeys an acap : nat) : YP09.region :=
  YP09.mkRegion (Some b) 0 56 wlo whi
    [YP09.mkChunk 0 (CVal 4 (SOff aty 0)); YP09.mkChunk 24 (CVal 8 (SOff akids 0));
     YP09.mkChunk 32 (CVal 8 (SOff akeys 0)); YP09.mkChunk 40 (CVal 8 (SOff an 0));
     YP09.mkChunk 48 (CVal 8 (SOff acap 0))].
Definition pj_obj_regionR (b aty akids akeys an acap : nat) : YP09.region :=
  pj_obj_regionW b 0 0 aty akids akeys an acap.
Lemma pj_obj_region_W : forall b aty akids akeys an acap,
  pj_obj_region b aty akids akeys an acap = pj_obj_regionW b 0 56 aty akids akeys an acap.
Proof. reflexivity. Qed.
(* the five field words in field order, and the region with its field atoms from xatom j (FSW_K.v ATOM CONVENTION) *)
Definition pj_fields (ty kids keys n cap : Z) : list word :=
  [Z_to_bv 64 ty; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 cap].
Definition pj_obj_regionX (b j : nat) : YP09.region :=
  pj_obj_region b (xatom j) (xatom (j + 1)) (xatom (j + 2)) (xatom (j + 3)) (xatom (j + 4)).
Definition pj_obj_regionWX (b j : nat) (wlo whi : Z) : YP09.region :=
  pj_obj_regionW b wlo whi (xatom j) (xatom (j + 1)) (xatom (j + 2)) (xatom (j + 3)) (xatom (j + 4)).
Definition pj_obj_regionRX (b j : nat) : YP09.region := pj_obj_regionWX b j 0 0.
Lemma pj_obj_regionX_WX : forall b j, pj_obj_regionX b j = pj_obj_regionWX b j 0 56.
Proof. reflexivity. Qed.
(* gf entries: the base atom (8-aligned, in [lo, hi]) and the type atom (in [tlo, thi]) *)
Definition pj_obj_facts (b aty : nat) (lo hi tlo thi : Z) : list (nat * afact) :=
  [(b, mkAF lo hi 3); (aty, mkAF tlo thi 0)].
Definition pj_obj_factsX (b j : nat) (lo hi tlo thi : Z) : list (nat * afact) :=
  pj_obj_facts b (xatom j) lo hi tlo thi.
(* region r's extent under E lies inside the object [v, v + 56) (for fsw_pj_parts_disjX) *)
Definition pj_in_obj (E : env) (v : Z) (r : YP09.region) : Prop :=
  v <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= v + 56.
Lemma fpj_all_disjoint_obj : forall E r rs v,
  base_val E (YP09.r_base r) + YP09.r_hi r <= v \/ v + 56 <= base_val E (YP09.r_base r) + YP09.r_lo r ->
  Forall (pj_in_obj E v) rs -> YP09.all_disjoint E r rs.
Proof.
  intros E r rs v Hr H. induction H as [|r' rs (H1 & H2) _ IH]; cbn [YP09.all_disjoint]; [exact I|].
  split; [|exact IH]. unfold YP09.extent_disjoint. lia.
Qed.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma fsw_pj_obj_regionW_ok : forall E m b wlo whi aty akids akeys an acap v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap -> (whi <= wlo \/ 0 <= wlo /\ whi <= 56) ->
  ew E b = Z_to_bv 64 v -> ew E aty = Z_to_bv 64 ty -> ew E akids = Z_to_bv 64 kids ->
  ew E akeys = Z_to_bv 64 keys -> ew E an = Z_to_bv 64 n -> ew E acap = Z_to_bv 64 cap ->
  YP09.region_ok segs E m (pj_obj_regionW b wlo whi aty akids akeys an acap).
Proof.
  intros E m b wlo whi aty akids akeys an acap v ty num str kids keys n cap Hh Hwin Eb Et Ek Ey En Ec.
  destruct Hh as (Hrw & Hty & _ & _ & Hkids & Hkeys & Hn & Hcap). pose proof Hrw as (_ & Hlo & Hhi & _).
  unfold pj_obj_regionW. apply (fsw_pj_part_ok segs E m b v v 0 56 wlo whi _ Hrw);
    [rewrite Eb; apply MState.unsigned_lit; lia | lia | lia | exact Hwin |].
  constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply (fsw_pj_chunk4 segs E m v 0 _ ty); [rewrite Z.add_0_r; exact Hty | rewrite fsw_SOff0; exact Et].
  - apply (fsw_pj_chunk8 segs E m v 24 _ kids); [exact Hkids | rewrite fsw_SOff0; exact Ek].
  - apply (fsw_pj_chunk8 segs E m v 32 _ keys); [exact Hkeys | rewrite fsw_SOff0; exact Ey].
  - apply (fsw_pj_chunk8 segs E m v 40 _ n); [exact Hn | rewrite fsw_SOff0; exact En].
  - apply (fsw_pj_chunk8 segs E m v 48 _ cap); [exact Hcap | rewrite fsw_SOff0; exact Ec].
Qed.
(* read only: no window premise *)
Lemma fsw_pj_obj_regionR_ok : forall E m b aty akids akeys an acap v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew E b = Z_to_bv 64 v -> ew E aty = Z_to_bv 64 ty -> ew E akids = Z_to_bv 64 kids ->
  ew E akeys = Z_to_bv 64 keys -> ew E an = Z_to_bv 64 n -> ew E acap = Z_to_bv 64 cap ->
  YP09.region_ok segs E m (pj_obj_regionR b aty akids akeys an acap).
Proof.
  intros E m b aty akids akeys an acap v ty num str kids keys n cap Hh Eb Et Ek Ey En Ec.
  exact (fsw_pj_obj_regionW_ok E m b 0 0 aty akids akeys an acap v ty num str kids keys n cap Hh
    (or_introl (Z.le_refl 0)) Eb Et Ek Ey En Ec).
Qed.
(* the whole-object form: fsw_pj_obj_regionW_ok at window [0, 56) *)
Lemma fsw_pj_obj_region_ok : forall E m b aty akids akeys an acap v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew E b = Z_to_bv 64 v -> ew E aty = Z_to_bv 64 ty -> ew E akids = Z_to_bv 64 kids ->
  ew E akeys = Z_to_bv 64 keys -> ew E an = Z_to_bv 64 n -> ew E acap = Z_to_bv 64 cap ->
  YP09.region_ok segs E m (pj_obj_region b aty akids akeys an acap).
Proof.
  intros E m b aty akids akeys an acap v ty num str kids keys n cap Hh Eb Et Ek Ey En Ec.
  exact (fsw_pj_obj_regionW_ok E m b 0 56 aty akids akeys an acap v ty num str kids keys n cap Hh
    (or_intror (conj (Z.le_refl 0) (Z.le_refl 56))) Eb Et Ek Ey En Ec).
Qed.
Lemma fsw_pj_obj_facts_ok : forall E m b aty lo hi tlo thi v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew E b = Z_to_bv 64 v -> ew E aty = Z_to_bv 64 ty -> lo <= v <= hi -> tlo <= ty <= thi ->
  atoms_ok E (pj_obj_facts b aty lo hi tlo thi).
Proof.
  intros E m b aty lo hi tlo thi v ty num str kids keys n cap ((H8 & Hlo & Hhi & _) & (Ht & _) & _) Eb Et Hv Hy.
  unfold pj_obj_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Eb, Et.
  rewrite !MState.unsigned_lit by lia. change (2 ^ 3) with 8. rewrite Z.pow_0_r.
  split; [split; [lia | split; [exact H8 | lia]]|]. split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
End q.

(* ---- NEW: the T env of the kit (fsw_entryT_argsX: Ereg regs (fs_extraT ++ xs)) ---- *)
Lemma fpj_nth_firstn : forall (l : list word) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros l. induction l as [|x l IH]; intros n i d Hi; destruct n as [|n]; [lia | reflexivity | lia |].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma fpj_nth_skipn : forall (l : list word) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
  intros l. induction l as [|x l IH]; intros [|j] i d; cbn [skipn Nat.add nth]; try reflexivity.
  - destruct i; reflexivity.
  - exact (IH j i d).
Qed.
(* xatom i is xs's i-th entry *)
Lemma fsw_ew_xatom : forall regs xs i, ew (Ereg regs (fs_extraT ++ xs)) (xatom i) = nth i xs (Z_to_bv 64 0).
Proof.
  intros regs xs i. unfold xatom. replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.
(* the five field atoms from xatom j, when xs holds pj_fields at j *)
Lemma fsw_pj_fields_at : forall regs xs j ty kids keys n cap,
  firstn 5 (skipn j xs) = pj_fields ty kids keys n cap ->
  ew (Ereg regs (fs_extraT ++ xs)) (xatom j) = Z_to_bv 64 ty /\
  ew (Ereg regs (fs_extraT ++ xs)) (xatom (j + 1)) = Z_to_bv 64 kids /\
  ew (Ereg regs (fs_extraT ++ xs)) (xatom (j + 2)) = Z_to_bv 64 keys /\
  ew (Ereg regs (fs_extraT ++ xs)) (xatom (j + 3)) = Z_to_bv 64 n /\
  ew (Ereg regs (fs_extraT ++ xs)) (xatom (j + 4)) = Z_to_bv 64 cap.
Proof.
  intros regs xs j ty kids keys n cap Hw.
  assert (F : forall i, (i < 5)%nat ->
    ew (Ereg regs (fs_extraT ++ xs)) (xatom (j + i)) = nth i (pj_fields ty kids keys n cap) (Z_to_bv 64 0)).
  { intros i Hi. rewrite fsw_ew_xatom, <- fpj_nth_skipn, <- Hw. symmetry. exact (fpj_nth_firstn _ 5 i _ Hi). }
  split; [rewrite <- (Nat.add_0_r j) at 1; exact (F 0%nat ltac:(lia))|].
  split; [exact (F 1%nat ltac:(lia))|]. split; [exact (F 2%nat ltac:(lia))|].
  split; [exact (F 3%nat ltac:(lia)) | exact (F 4%nat ltac:(lia))].
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* rs: the object region of a pj_hdr, its field atoms from xatom j, write window [wlo, whi) *)
Lemma fsw_pj_obj_regionWX_ok : forall regs xs j m b wlo whi v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap -> (whi <= wlo \/ 0 <= wlo /\ whi <= 56) ->
  ew (Ereg regs (fs_extraT ++ xs)) b = Z_to_bv 64 v ->
  firstn 5 (skipn j xs) = pj_fields ty kids keys n cap ->
  YP09.region_ok segs (Ereg regs (fs_extraT ++ xs)) m (pj_obj_regionWX b j wlo whi).
Proof.
  intros regs xs j m b wlo whi v ty num str kids keys n cap Hh Hwin Eb Hw.
  destruct (fsw_pj_fields_at regs xs j ty kids keys n cap Hw) as (Et & Ek & Ey & En & Ec).
  exact (fsw_pj_obj_regionW_ok segs _ m b wlo whi _ _ _ _ _ v ty num str kids keys n cap Hh Hwin Eb Et Ek Ey En Ec).
Qed.
(* ... read only *)
Lemma fsw_pj_obj_regionRX_ok : forall regs xs j m b v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew (Ereg regs (fs_extraT ++ xs)) b = Z_to_bv 64 v ->
  firstn 5 (skipn j xs) = pj_fields ty kids keys n cap ->
  YP09.region_ok segs (Ereg regs (fs_extraT ++ xs)) m (pj_obj_regionRX b j).
Proof.
  intros regs xs j m b v ty num str kids keys n cap Hh Eb Hw.
  exact (fsw_pj_obj_regionWX_ok regs xs j m b 0 0 v ty num str kids keys n cap Hh (or_introl (Z.le_refl 0)) Eb Hw).
Qed.
(* ... the whole object writable: fsw_pj_obj_regionWX_ok at window [0, 56) *)
Lemma fsw_pj_obj_regionX_ok : forall regs xs j m b v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew (Ereg regs (fs_extraT ++ xs)) b = Z_to_bv 64 v ->
  firstn 5 (skipn j xs) = pj_fields ty kids keys n cap ->
  YP09.region_ok segs (Ereg regs (fs_extraT ++ xs)) m (pj_obj_regionX b j).
Proof.
  intros regs xs j m b v ty num str kids keys n cap Hh Eb Hw.
  exact (fsw_pj_obj_regionWX_ok regs xs j m b 0 56 v ty num str kids keys n cap Hh
    (or_intror (conj (Z.le_refl 0) (Z.le_refl 56))) Eb Hw).
Qed.
(* gf: the base and type atom facts, the type atom at xatom j *)
Lemma fsw_pj_obj_factsX_ok : forall regs xs j m b lo hi tlo thi v ty num str kids keys n cap,
  PjStruct.pj_hdr segs m v ty num str kids keys n cap ->
  ew (Ereg regs (fs_extraT ++ xs)) b = Z_to_bv 64 v ->
  firstn 5 (skipn j xs) = pj_fields ty kids keys n cap -> lo <= v <= hi -> tlo <= ty <= thi ->
  atoms_ok (Ereg regs (fs_extraT ++ xs)) (pj_obj_factsX b j lo hi tlo thi).
Proof.
  intros regs xs j m b lo hi tlo thi v ty num str kids keys n cap Hh Eb Hw Hv Hy.
  destruct (fsw_pj_fields_at regs xs j ty kids keys n cap Hw) as (Et & _).
  exact (fsw_pj_obj_facts_ok segs _ m b _ lo hi tlo thi v ty num str kids keys n cap Hh Eb Et Hv Hy).
Qed.
(* the disjointness fsw_entryT_argsX asks of fsT_regions f ++ rs, for rs the parts of ONE object at v (each extent inside
   [v, v + 56), pj_in_obj; the parts pairwise disjoint): the object apart from the frame [spZ regs - f, spZ regs) and
   from the two shadow-base cells of fsT_regions (A/AB1w.v:594 / :605); the frame apart from the cells follows from
   alloc_ceiling + f <= spZ regs (FSW_K.v fsw_sp, f <= STK) *)
Lemma fsw_pj_parts_disjX : forall regs extra f v rs,
  0 <= f -> alloc_ceiling + f <= spZ regs ->
  (v + 56 <= spZ regs - f \/ spZ regs <= v) ->
  (v + 56 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= v) ->
  (v + 56 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= v) ->
  Forall (pj_in_obj (Ereg regs extra) v) rs -> YP09.pairwise_disjoint (Ereg regs extra) rs ->
  YP09.pairwise_disjoint (Ereg regs extra) (fsT_regions_args f rs).
Proof.
  intros regs extra f v rs Hf Hc Hs Hg Hb Hin Hdj.
  pose proof asan_consts as (C1 & _).
  assert (E2 : bv_unsigned (ew (Ereg regs extra) 2) = spZ regs)
    by (rewrite (ew_Ereg_nat regs extra 2 2%bv eq_refl); reflexivity).
  assert (F : forall r, base_val (Ereg regs extra) (YP09.r_base r) + YP09.r_hi r <= v \/
                        v + 56 <= base_val (Ereg regs extra) (YP09.r_base r) + YP09.r_lo r ->
                        YP09.all_disjoint (Ereg regs extra) r rs)
    by (intros r Hr; exact (fpj_all_disjoint_obj _ r rs v Hr Hin)).
  unfold fsT_regions_args, fsT_regions. cbn [app YP09.pairwise_disjoint YP09.all_disjoint].
  split; [split; [|split] | split; [split | split; [|exact Hdj]]].
  all: first [apply F | idtac]; unfold YP09.extent_disjoint, fs_got_region, fs_bcell_region, fstk;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?E2;
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *; lia.
Qed.
(* ... rs the one object region, any write window *)
Lemma fsw_pj_obj_disjWX : forall regs extra f b wlo whi aty akids akeys an acap v,
  ew (Ereg regs extra) b = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= f -> alloc_ceiling + f <= spZ regs ->
  (v + 56 <= spZ regs - f \/ spZ regs <= v) ->
  (v + 56 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= v) ->
  (v + 56 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= v) ->
  YP09.pairwise_disjoint (Ereg regs extra)
    (fsT_regions_args f [pj_obj_regionW b wlo whi aty akids akeys an acap]).
Proof.
  intros regs extra f b wlo whi aty akids akeys an acap v Eb Hv Hf Hc Hs Hg Hb.
  assert (Ub : bv_unsigned (ew (Ereg regs extra) b) = v) by (rewrite Eb; apply MState.unsigned_lit; exact Hv).
  apply (fsw_pj_parts_disjX regs extra f v); [exact Hf | exact Hc | exact Hs | exact Hg | exact Hb | |].
  - constructor; [|constructor]. unfold pj_in_obj, pj_obj_regionW.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ub. lia.
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
Qed.
(* ... the whole-object region: fsw_pj_obj_disjWX at window [0, 56) *)
Lemma fsw_pj_obj_disjX : forall regs extra f b aty akids akeys an acap v,
  ew (Ereg regs extra) b = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= f -> alloc_ceiling + f <= spZ regs ->
  (v + 56 <= spZ regs - f \/ spZ regs <= v) ->
  (v + 56 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= v) ->
  (v + 56 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= v) ->
  YP09.pairwise_disjoint (Ereg regs extra) (fsT_regions_args f [pj_obj_region b aty akids akeys an acap]).
Proof.
  intros regs extra f b aty akids akeys an acap v Eb Hv Hf Hc Hs Hg Hb.
  exact (fsw_pj_obj_disjWX regs extra f b 0 56 aty akids akeys an acap v Eb Hv Hf Hc Hs Hg Hb).
Qed.
End r.
