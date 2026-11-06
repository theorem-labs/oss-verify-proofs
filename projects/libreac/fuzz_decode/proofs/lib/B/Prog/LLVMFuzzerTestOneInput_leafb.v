(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v (tfib_srealizesX),
   lib/A/AB1n.v (tfib_startup_T1, HS_ok) and lib/A/AD2o.v (TFIB_T_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v, a working branch 86b0e893fe8), for libreac/fuzz_decode's
   ASan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeClose.v, with its module paths and module names changed; 1425 of its 1489 lines of code are new or changed and 431 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_leafb: the shared leaf-call bridge of the image-B (asan-ubsan) walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (the segment files LLVMFuzzerTestOneInput_seg*.v of lib/B/Prog).
   It is image A's twin, lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (a working branch
   8ca3e07aa60), lemma for lemma and with the same names, at image B's segments (decodesegsB0 = lib/B/Img0.v rsegs),
   image B's runtime cells (lib/B/AsanCells.v) and image B's leaf kit (lib/B/Prog/LeafCgKit.v).
   A program leaf of this unit is stated in lib/B/Prog/<leaf>_cg.v over the kit lib/B/Prog/LeafCgKit.v: its premises
   are footprint facts about the RAW call memory (Frame.stk, Mem.bytes_at, AsanCells.addressable / asan_cells,
   ExecF.rng over RNG_W W) and its post is LeafCgKit.dleaf_post. A segment walks in cgif's caller-journal form
   (lib/Reusable/YCbq.v ajournal, the VIEW aview of the world's visible bytes). This file turns one into the other,
   for every leaf alike; no lemma here names a leaf.
   (a) dec_leafb_journal: a leaf's dleaf_post at the call becomes the caller's journal at the return, through
       YCbq.v ajournal_after_write with the written set = the leaf's stack window [sp - ESTACK, sp) and its WR.
   (b) Frame.stk / ExecF.rng (RNG_W W): dec_leafb_stk, dec_leafb_stk_journal, dec_leafb_rng, dec_leafb_rng_journal,
       dec_leafb_rng_block, dec_leafb_rng_shadow, dec_leafb_rng_cells.
   (c) the raw byte facts: dec_leafb_mrd (a visible byte's raw read is its view), dec_leafb_bytes_garr8,
       dec_leafb_bytes_le, dec_leafb_rom_bytes, dec_leafb_addressable, dec_leafb_addressable_block,
       dec_leafb_wr_at, dec_leafb_wr_block, the app_mem / off_stk arithmetic.
   (d) dec_leafb_asan_cells: asan_cells from dec_crt_cells B (check_round_trip_cg.v:109) and AR's am_const. Its
       helpers are image A's, which took them from a working branch e6dfa363adb
       proofs/libreac/fuzz_decode/lib/A/Prog/crtA_cells.v:23-237; image B's twin of that file is crtB_cells.v on
       a working branch fb1f0100f0f (crt_* renamed dec_leafb_*; text otherwise the
       record's). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0n YP09 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0f YG0n YG0d YCbq YG0v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Mem Frame ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit AsanKA DecodeBImg.
(* The leaves the walk calls, and their C models (the results the instances below state). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_frame_is_reac_cg reac_frame_clean_len_cg
  reac_frame_counter_cg reac_frame_inspect_cg reac_decode_cg reac_decode_plain_le_cg reac_upstream_channels_cg
  reac_upstream_decode_cg check_braid_cg check_braid_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_frame_inspect_c reac_frame_counter_c
  reac_decode_c reac_decode_plain_le_c reac_upstream_channels_c reac_upstream_decode_c.
Import ListNotations.
Open Scope Z_scope.
(* YM03.v:182-189 (pulled in through PaTable.v) redefines lia / nia globally with context pruning and retries;
   this file uses YM03.v:179-180's originals (a Theorem Labs lane's measured fix). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
(* The shadow arithmetic divides by 8; lia needs the euclidean equations (as ReadName.v:149 does). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module LMem := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Frame.
Module LExecF := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.ExecF.
Module BImg0 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Img0.
Module BCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.AsanCells.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.
Module BKA := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.AsanKA.
Module LIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_is_reac_cg.
Module LCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_clean_len_cg.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_cg.
Module LPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_cg.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_cg.
Module LUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_cg.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_cg.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_c.
Module CCnt := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_counter_c.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_c.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_c.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_c.
Module CBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_c.

(* ------------------------------------------------------------------ *)
(* (d) the runtime cells: crtB_cells.v:23-237, copied (see the header)   *)
(* ------------------------------------------------------------------ *)

Lemma dec_leafb_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma dec_leafb_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma dec_leafb_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma dec_leafb_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite dec_leafb_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply dec_leafb_byte_mod; lia.
Qed.

Lemma dec_leafb_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (LMem.wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold LMem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply dec_leafb_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

Lemma dec_leafb_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le8 (LMem.wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold LMem.le8, word_to_le_bytes.
  apply dec_leafb_le_byte; [exact Hk | apply dec_leafb_wa_mod; lia].
Qed.

Lemma dec_leafb_le4_byte : forall v k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le4 (LMem.wa v)) k) = Some (le_byte v 4 k).
Proof.
  intros v k Hk. unfold LMem.le4.
  apply dec_leafb_le_byte; [exact Hk | apply dec_leafb_wa_mod; lia].
Qed.

Lemma dec_leafb_le1_byte : forall v k, (k < 1)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error [Z_to_bv 8 v] k) = Some (le_byte v 1 k).
Proof.
  intros v k Hk. change [Z_to_bv 8 v] with (Z_to_le_bytes 1 v).
  apply dec_leafb_le_byte; [exact Hk | reflexivity].
Qed.

Lemma dec_leafb_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

Lemma dec_leafb_find_none : forall (l : list Segment) addr n s,
  find_segment l addr n = None -> In s l ->
  Z.of_N (seg_base s) <= addr -> addr + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) -> False.
Proof.
  induction l as [|s0 l IH]; intros addr n s Hf Hin H1 H2; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s0)) addr && Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%Z
    eqn:E; [discriminate|].
  destruct Hin as [<- | Hin].
  - apply andb_false_iff in E as [E | E]; apply Z.leb_gt in E; lia.
  - exact (IH addr n s Hf Hin H1 H2).
Qed.

Lemma dec_leafb_covers_lo : forall a n, dec_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold dec_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma dec_leafb_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments decodesegsB0 hd -> dec_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold dec_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  assert (U : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply (LMem.wa_unsigned (a + i)); lia).
  rewrite U in E2.
  exact (dec_leafb_find_none decodesegsB0 (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma dec_leafb_seg_of : forall a n, In (a, n) dec_asan_cell_ranges -> dec_seg_covers a n = true.
Proof. intros a n Hin. exact (proj1 (forallb_forall _ _) dec_asan_cells_in_seg (a, n) Hin). Qed.

Ltac dec_leafb_seg := clear; apply dec_leafb_seg_of; unfold dec_asan_cell_ranges; cbn [In];
  repeat (first [left; reflexivity | right]).
Ltac dec_leafb_top := clear; apply Z.leb_le; reflexivity.

Section Cells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma dec_leafb_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments decodesegsB0 hd ->
  cell_holds B ly (aview decodesegsB0 hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  dec_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  LMem.bytes_at BImg0.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold LMem.bytes_at.
  split; [exact (dec_leafb_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (dec_leafb_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : LMem.mrd BImg0.rsegs mem (LMem.wa (a + Z.of_nat i)) =
                mbyte decodesegsB0 (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (dec_leafb_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma dec_leafb_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegsB0 hd ->
  Forall (cell_holds B ly (aview decodesegsB0 hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> dec_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  LMem.bytes_at BImg0.rsegs mem a (LMem.le8 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (dec_leafb_cell_bytes ly hd mem a v 8 (LMem.le8 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le8 _) (dec_leafb_le8_byte v)).
Qed.

Lemma dec_leafb_z4 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegsB0 hd ->
  Forall (cell_holds B ly (aview decodesegsB0 hd mem)) (as_const B ly) ->
  In (z4 (ANum a) v) (as_const B ly) -> dec_seg_covers a 4 = true -> a + 4 <= 2 ^ 64 ->
  LMem.bytes_at BImg0.rsegs mem a (LMem.le4 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (dec_leafb_cell_bytes ly hd mem a v 4 (LMem.le4 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le4 _) (dec_leafb_le4_byte v)).
Qed.

Lemma dec_leafb_z1 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegsB0 hd ->
  Forall (cell_holds B ly (aview decodesegsB0 hd mem)) (as_const B ly) ->
  In (z1 (ANum a) v) (as_const B ly) -> dec_seg_covers a 1 = true -> a + 1 <= 2 ^ 64 ->
  LMem.bytes_at BImg0.rsegs mem a [Z_to_bv 8 v].
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (dec_leafb_cell_bytes ly hd mem a v 1 [Z_to_bv 8 v] Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           eq_refl (dec_leafb_le1_byte v)).
Qed.

(* crtB_cells.v:206 dec_cells_asan, at the world's own hidden set (its w_Hoff field). *)
Lemma dec_leafb_asan_cells :
  dec_crt_cells B ->
  forall (ly : alayout) (S : astate) (W : world decodesegsB0) (mem : word -> option byte) (md : Model),
    @AR rc decodesegsB0 B ly S W mem md ->
    BCells.asan_cells mem.
Proof.
  intros HC ly S W mem md HAR.
  pose proof (w_Hoff W) as Hoff.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview decodesegsB0 (w_H W) mem)) (as_const B ly))
    by (eapply am_const; exact HM).
  (* dec_crt_cells is a conjunction of `In <cell> (as_const B ly)` rows whose order and number are the
     statement's, not this file's (the frozen statement appended image B's mode-table rows). Every row is split
     into its own hypothesis and picked by its shape, so an appended row cannot break this proof. *)
  pose proof (HC ly) as HROWS. repeat match type of HROWS with _ /\ _ => destruct HROWS as [? HROWS] end.
  unfold BCells.asan_cells.
  split; [exact (dec_leafb_z8 ly _ mem BCells.CELL_K BCells.ASAN_K Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_CELL_K BCells.CELL_K Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z1 ly _ mem BCells.INITED 1 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z1 ly _ mem BCells.REPLACE 1 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_REPLACE BCells.REPLACE Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z4 ly _ mem BCells.UAR 1 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_UAR BCells.UAR Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z1 ly _ mem BCells.CANPOISON 1 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.HIEND 0x7fffffffffff Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_HIEND BCells.HIEND Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.MIDBEG 0 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_MIDBEG BCells.MIDBEG Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.MIDEND 0 Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.GOT_MIDEND BCells.MIDEND Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.REAL_MEMCPY BCells.MUSL_MEMCPY Hoff HK ltac:(assumption) ltac:(dec_leafb_seg)
                   ltac:(dec_leafb_top))|].
  split; [exact (dec_leafb_z8 ly _ mem BCells.REAL_MEMSET BCells.MUSL_MEMSET Hoff HK ltac:(assumption) ltac:(dec_leafb_seg)
                   ltac:(dec_leafb_top))|].
  exact (dec_leafb_z8 ly _ mem BCells.GOT_REAL_MEMSET BCells.REAL_MEMSET Hoff HK ltac:(assumption) ltac:(dec_leafb_seg) ltac:(dec_leafb_top)).
Qed.
End Cells.

(* ------------------------------------------------------------------ *)
(* (c) raw bytes from the view                                         *)
(* ------------------------------------------------------------------ *)

Local Notation segs := decodesegsB0.

(* A byte the view shows is not hidden: a hidden address lies outside every loaded segment (the world's w_Hoff),
   where the image reads nothing. *)
Lemma dec_leafb_mbyte_vis : forall (W : world segs) mem a b,
  mbyte segs (mrestrict (w_H W) mem) a = Some b -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a b H. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
  unfold mbyte, mrestrict in H. rewrite Hh in H.
  pose proof (w_Hoff W _ Hh) as Hf.
  unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H. rewrite Hf in H. discriminate.
Qed.

Lemma dec_leafb_aview_vis : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b|] eqn:E; [|discriminate].
  exact (dec_leafb_mbyte_vis W mem a b E).
Qed.

(* A visible byte's raw read (Mem.mrd, what the footprint contracts read) is its view byte. *)
Lemma dec_leafb_mrd : forall (W : world segs) mem a,
  w_H W (Z_to_bv 64 a) = false -> LMem.mrd segs mem (LMem.wa a) = mbyte segs (mrestrict (w_H W) mem) a.
Proof. intros W mem a H. unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite H. reflexivity. Qed.

Lemma dec_leafb_mrd_aview : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v ->
  exists b : byte, LMem.mrd segs mem (LMem.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (dec_leafb_aview_vis W mem a v H) as Hv.
  rewrite (dec_leafb_mrd W mem a Hv). unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b|]; [|discriminate].
  cbn in H. injection H as <-. exists b. auto.
Qed.

Lemma dec_leafb_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The bytes of a garr8 array of the view are the raw bytes. *)
Lemma dec_leafb_bytes_garr8 : forall (W : world segs) mem p (bs : list byte),
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) bs) ->
  0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  LMem.bytes_at segs mem p bs.
Proof.
  intros W mem p bs HG H0 Ht. split; [exact H0|]. split; [exact Ht|].
  intros i Hi.
  assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in Hv.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by exact Hi'.
  rewrite map_nth in Hv. rewrite dec_leafb_le_byte1 in Hv.
  rewrite (dec_leafb_mrd W mem (p + Z.of_nat i) (dec_leafb_mbyte_vis W mem _ _ Hv)), Hv.
  symmetry. apply nth_error_nth'. exact Hi.
Qed.

(* A w-byte value of the view, read as the little-endian bytes of any z congruent to it. *)
Lemma dec_leafb_bytes_le : forall (W : world segs) mem a (w : nat) z v,
  val_mem segs (mrestrict (w_H W) mem) a w v ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  LMem.bytes_at segs mem a (Z_to_le_bytes w z).
Proof.
  intros W mem a w z v HV Hm H0 Ht. split; [exact H0|].
  rewrite length_Z_to_le_bytes. split; [exact Ht|]. intros i Hi.
  specialize (HV i Hi).
  rewrite (dec_leafb_mrd W mem (a + Z.of_nat i) (dec_leafb_mbyte_vis W mem _ _ HV)), HV.
  rewrite dec_leafb_nth_le_bytes by exact Hi. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
  rewrite <- Hm. apply dec_leafb_byte_mod; lia.
Qed.

(* Read-only image bytes: under rom_view, the raw bytes of an in-rom range are the image's. *)
Lemma dec_leafb_rom_bytes : forall (W : world segs) mem a (bs : list byte),
  rom_view segs W mem ->
  (forall i, (i < length bs)%nat -> in_rom segs (a + Z.of_nat i)) ->
  (forall i, (i < length bs)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  LMem.bytes_at segs mem a bs.
Proof.
  intros W mem a bs HR Hin Himg H0 Ht. split; [exact H0|]. split; [exact Ht|]. intros i Hi.
  pose proof (HR _ (Hin i Hi)) as Hv. rewrite (Himg i Hi) in Hv.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi) in Hv |- *. cbn [option_map] in Hv.
  destruct (dec_leafb_mrd_aview W mem _ _ Hv) as (b & Hb & Hbv). rewrite Hb. f_equal. apply bv_eq. exact Hbv.
Qed.

Lemma dec_leafb_bv_signed8 : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8 / 2) with 128. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Section App. Context {rc : YM05.RunCeil}.
Lemma dec_leafb_app_of_in_app : forall lo len i, in_app lo len -> 0 <= i < len -> BCells.app_mem (lo + i).
Proof.
  intros lo len i [H0 H] Hi. pose proof (proj1 (@ASAN_CEIL_range rc)) as C. pose proof (proj2 (@ASAN_CEIL_range rc)) as C2.
  unfold BCells.app_mem, BCells.LOWMEM_END, BCells.HIGHMEM_BEG, BCells.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* Every stack byte (between alloc_ceiling and 2^47) is application memory. *)
Lemma dec_leafb_app_stack : forall a, alloc_ceiling <= a < 2 ^ 47 -> BCells.app_mem a.
Proof.
  intros a Ha. pose proof alloc_ceiling_val. unfold BCells.app_mem, BCells.HIGHMEM_BEG, BCells.APPMEM_END. lia.
Qed.
End App.

(* addressable (AsanCells) from range_addressable of the view. *)
Lemma dec_leafb_addressable : forall (W : world segs) mem p n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n ->
  0 <= p -> 0 <= n -> p + n <= BCells.APPMEM_END ->
  (forall i, 0 <= i < n -> BCells.app_mem (p + i)) ->
  BCells.addressable mem p n.
Proof.
  intros W mem p n HRA H0 Hn Ht Happ. split; [exact H0|]. split; [exact Hn|]. split; [exact Ht|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  unfold shadow_of_addr in Hs.
  assert (EA : BCells.shadow_addr (p + i) = SHADOW_OFF + (p + i) / 8)
    by (unfold BCells.shadow_addr, BCells.ASAN_K, SHADOW_OFF; lia).
  rewrite EA. destruct (dec_leafb_mrd_aview W mem _ _ Hs) as (b & Hb & Hbv).
  exists b. split; [exact Hb|]. unfold BCells.shadow_ok, saddr_ok in *.
  rewrite dec_leafb_bv_signed8 by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* (b) Frame.stk and ExecF.rng (RNG_W W)                               *)
(* ------------------------------------------------------------------ *)

Lemma dec_leafb_stk : forall (W : world segs) mem lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  LFrame.stk segs mem lo hi.
Proof.
  intros W mem lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as [_ (b & Hb)]. unfold LMem.wa.
  split; [unfold wview; rewrite Hb; discriminate|]. exists b. unfold LMem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma dec_leafb_rng : forall (W : world segs) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> w_H W (Z_to_bv 64 a) = false) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H0 H1 HV. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj k Hk. unfold LCK.woff.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. apply HV. lia.
Qed.

(* The cells every leaf reads (GOT_CELL_K, CELL_K) lie in loaded segments, where nothing is hidden. *)
Lemma dec_leafb_rng_cells : forall (W : world segs),
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) BCells.GOT_CELL_K 8 /\
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) BCells.CELL_K 8.
Proof.
  intros W. split.
  - apply (dec_leafb_rng W); [unfold BCells.GOT_CELL_K; lia | unfold BCells.GOT_CELL_K; lia |].
    intros a Ha. replace a with (BCells.GOT_CELL_K + (a - BCells.GOT_CELL_K)) by lia.
    apply (dec_leafb_covers_visible (w_H W) BCells.GOT_CELL_K 8); [exact (w_Hoff W) | dec_leafb_seg | lia | dec_leafb_top].
  - apply (dec_leafb_rng W); [unfold BCells.CELL_K; lia | unfold BCells.CELL_K; lia |].
    intros a Ha. replace a with (BCells.CELL_K + (a - BCells.CELL_K)) by lia.
    apply (dec_leafb_covers_visible (w_H W) BCells.CELL_K 8); [exact (w_Hoff W) | dec_leafb_seg | lia | dec_leafb_top].
Qed.

Lemma dec_leafb_rng_vis : forall (W : world segs) mem lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> apresent (w_H W) mem a) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof. intros W mem lo len H0 H1 HP. apply dec_leafb_rng; [exact H0 | exact H1 |]. intros a Ha. exact (proj1 (HP a Ha)). Qed.

(* The shadow bytes of an addressable range are visible, so the leaf's footprint may read them. *)
Lemma dec_leafb_rng_shadow : forall (W : world segs) mem a n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n ->
  0 <= a -> 0 < n -> a + n <= 2 ^ 64 ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (BCells.shadow_addr a)
    (BCells.shadow_addr (a + n - 1) - BCells.shadow_addr a + 1).
Proof.
  intros W mem a n HRA H0 Hn Ht. unfold BCells.shadow_addr, BCells.ASAN_K in *.
  assert (D1 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (D2 : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : 8 * ((a + n - 1) / 8) <= a + n - 1) by (apply Z.mul_div_le; lia).
  assert (D4 : (a + n - 1) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  apply dec_leafb_rng; [lia | lia |]. intros s Hs.
  set (q := s - 2147450880).
  assert (Hq : a / 8 <= q <= (a + n - 1) / 8) by (subst q; lia).
  destruct (Z.eq_dec q (a / 8)) as [Eq | Nq].
  - destruct (HRA a ltac:(lia)) as (v & Hv & _). unfold shadow_of_addr, SHADOW_OFF in Hv.
    replace s with (2147450880 + a / 8) by (subst q; lia). exact (dec_leafb_aview_vis W mem _ v Hv).
  - assert (Ha8 : a < 8 * q) by (pose proof (Z.mod_pos_bound a 8 ltac:(lia)); pose proof (Z.div_mod a 8 ltac:(lia)); lia).
    assert (Hq8 : 8 * q <= a + n - 1) by lia.
    destruct (HRA (8 * q) ltac:(lia)) as (v & Hv & _). unfold shadow_of_addr, SHADOW_OFF in Hv.
    rewrite Z.mul_comm, Z.div_mul in Hv by lia. replace s with (2147450880 + q) by (subst q; lia).
    exact (dec_leafb_aview_vis W mem _ v Hv).
Qed.

Lemma dec_leafb_wr_at : forall (W : world segs) mem a n,
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, 0 <= i < n -> apresent (w_H W) mem (a + i)) ->
  LMem.wr_at segs mem a n.
Proof.
  intros W mem a n H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (HP i Hi) as [_ (b & Hb)]. unfold LMem.wa, wview. rewrite Hb. discriminate.
Qed.

Lemma dec_leafb_pairwise_dup : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) y,
  pairwise R (l1 ++ l2) -> In y l1 -> In y l2 -> R y y.
Proof.
  intros X R l1. induction l1 as [|h t IH]; intros l2 y HP H1 H2; [destruct H1|].
  cbn [app pairwise] in HP. destruct HP as [HF HP]. destruct H1 as [<- | H1].
  - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact H2.
  - exact (IH l2 y HP H1 H2).
Qed.

Section Blocks. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* A block a state added on top of an earlier block list is not in that list (blocks are pairwise disjoint). *)
Lemma dec_leafb_new_block : forall ly S (W : world segs) mem md bl0 rest b n,
  @AR rc segs B ly S W mem md -> ablocks B ly S = bl0 ++ rest -> In (b, n) rest -> ~ In (b, n) bl0.
Proof.
  intros ly S W mem md bl0 rest b n HAR Hbl Hin Hin0.
  assert (Hb : In (b, n) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & _ & _ & _ & Hpw & Hn).
  rewrite Hbl, map_app in Hpw.
  pose proof (dec_leafb_pairwise_dup _ _ _ (b, req_size n) Hpw
    (in_map (fun x => (fst x, req_size (snd x))) _ _ Hin0) (in_map (fun x => (fst x, req_size (snd x))) _ _ Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. revert Hd. unfold req_size. destruct (Z.eqb_spec n 0); intros Hd; lia.
Qed.

(* A byte of such a new block is one the caller's journal lets a callee write (awr_byte's temporary-block case). *)
Lemma dec_leafb_awr_new : forall STK sp0 FP ly S lyc Sc (W : world segs) memc mdc own rest b n a,
  @AR rc segs B lyc Sc W memc mdc -> ablocks B lyc Sc = ablocks B ly S ++ rest -> In (b, n) rest ->
  b <= a < b + req_size n ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a.
Proof.
  intros STK sp0 FP ly S lyc Sc W memc mdc own rest b n a HAR Hbl Hin Ha.
  right. right. left. exists b, n. split; [rewrite Hbl; apply in_or_app; right; exact Hin|].
  split; [exact (dec_leafb_new_block _ _ _ _ _ _ _ b n HAR Hbl Hin) | exact Ha].
Qed.

Lemma dec_leafb_rng_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & Hpres & _).
  pose proof alloc_ceiling_val.
  apply (dec_leafb_rng_vis W mem); [lia | lia |]. intros x Hx. exact (proj1 (Hpres x ltac:(lia))).
Qed.

Lemma dec_leafb_addressable_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> 0 <= n -> a + n <= p + req_size m ->
  BCells.addressable mem a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 Hn H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  pose proof alloc_ceiling_val.
  apply (dec_leafb_addressable W mem).
  - eapply (range_addressable_of_block segs B LAWS); eassumption.
  - lia.
  - exact Hn.
  - unfold BCells.APPMEM_END. lia.
  - intros i Hi. replace (a + i) with (p + (a - p + i)) by lia.
    apply (@dec_leafb_app_of_in_app rc p (req_size m)); [exact Happ | lia].
Qed.

Lemma dec_leafb_rng_shadow_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> 0 < n -> a + n <= p + req_size m ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (BCells.shadow_addr a)
    (BCells.shadow_addr (a + n - 1) - BCells.shadow_addr a + 1).
Proof.
  intros ly S W mem md p m a n HAR Hin H1 Hn H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _).
  pose proof alloc_ceiling_val.
  apply (dec_leafb_rng_shadow W mem); [eapply (range_addressable_of_block segs B LAWS); eassumption | lia | lia | lia].
Qed.

Lemma dec_leafb_wr_block : forall ly S (W : world segs) mem md p m,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
  forall x, p <= x < p + req_size m -> ~ aowned B ly S x /\ ~ LCK.in_img x.
Proof.
  intros ly S W mem md p m HAR Hin x Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  split; [exact (proj2 (Hpres x Hx))|].
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HAR (or_introl (ex_intro _ p (ex_intro _ m (conj Hin Hx)))))).
Qed.

Lemma dec_leafb_wr_at_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  LMem.wr_at segs mem a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & Hpres & _).
  pose proof alloc_ceiling_val.
  apply (dec_leafb_wr_at W mem); [lia | lia |]. intros i Hi. exact (proj1 (Hpres (a + i) ltac:(lia))).
Qed.
End Blocks.

(* ------------------------------------------------------------------ *)
(* (a) a leaf's post at the call -> the caller's journal at the return *)
(* ------------------------------------------------------------------ *)

Section Journal. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
(* The leaf kit's call pre and leaf post (LeafCgKit.v:73, :86), at this unit's allocator model, as
   check_round_trip_cg.v:173 dec_leaf_at instantiates them. *)
Definition dec_leafb_ecall_pre := @LCK.ecall_pre (world segs) (@w_H segs) alayout astate (@AR rc segs B)
  ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
Definition dec_leafb_post := @LCK.dleaf_post fx (world segs) (@w_H segs) alayout astate (@AR rc segs B)
  (aview segs) same_but_materialized.

Lemma dec_leafb_stk_journal : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo hi,
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 -> LFrame.stk segs memc lo hi.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo hi HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof alloc_ceiling_val.
  apply (dec_leafb_stk W memc); [lia | lia |]. intros a Ha. apply Hpres. lia.
Qed.

Lemma dec_leafb_rng_journal : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo len,
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo len HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof alloc_ceiling_val.
  apply (dec_leafb_rng_vis W memc); [lia | lia |]. intros a Ha. apply Hpres. lia.
Qed.

Lemma dec_leafb_journal : forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc
    mdc k (o PC : Z) (RES : option Z) (WR : list (Z * Z)) (X : (word -> option byte) -> Prop),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  (forall a, LCK.in_wr WR a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (dec_leafb_ecall_pre lyc Sc W regsT memT mdc ->
     SRr segs W (@LCK.cfg_at fx PC regsT memT mdc) (dec_leafb_post lyc Sc W regsT memT mdc RES WR X)) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 PC) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst regs2 (getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
       @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall r, RES = Some r -> getr regs2 10 = w64 r) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr WR a ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       X mem2).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o PC RES WR X
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp HWR HLEAF.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstk & _ & HQT).
  assert (HPRE : dec_leafb_ecall_pre lyc Sc W regsT memT mdc).
  { pose proof (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg Hbud
      Hra Hgp Htp) as H.
    exact H. }
  eapply SRr_mono; [exact (HLEAF HPRE) |].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hgr & HX).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split. { unfold LCK.cfg_at, LCK.w64, LCK.raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { eapply (ajournal_after_write segs B LAWS DecodeBImg.decodeb_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k
      mem2 md2 (fun a => (spZ regsT - ESTACK <= a < spZ regsT) \/ LCK.in_wr WR a) Sc own HJ).
    - intros a Ha Hna. apply (Heff a Ha); intros H'; apply Hna; [left | right]; exact H'.
    - exact Hgr.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [left; unfold ESTACK in *; lia | exact (HWR a Ha)].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hgr | exact HX].
Qed.

(* The arithmetic every call site shares: where the callee's stack window lies. *)
Lemma dec_leafb_frame_bounds : forall STK sp0 FP ly S W0 mem md own lyc Sc (W : world segs) memc mdc k
    (regsT : bvmap 5 word) (o : Z),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsT = sp0 + o -> o <= 0 -> ESTACK - o <= STK ->
  alloc_ceiling + ESTACK <= spZ regsT /\ spZ regsT <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 - STK <= spZ regsT - ESTACK.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsT o HJ Hsp Hneg Hbud.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  unfold ESTACK in *. lia.
Qed.
End Journal.

(* ------------------------------------------------------------------ *)
(* The per-leaf instances: one lemma per leaf the walk calls           *)
(* ------------------------------------------------------------------ *)

Section Leaves. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* What every instance's post says: the caller's journal at the return, the callee-saved registers, the result in
   a0, and the bytes outside the call's stack window (and its written ranges) kept. *)
Definition dec_leafb_ret (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world segs) mem md own lyc Sc
    (W : world segs) (memT : word -> option byte) (k : Z) (regsT : bvmap 5 word)
    (res : Z) (WR : list (Z * Z)) (X : (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    getr regs2 10 = w64 res /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr WR a ->
       aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
    X mem2.

(* reac_frame_inspect (lib/B/Prog/reac_frame_inspect_cg.v): reads the copy's header and trailer bytes; writes
   nothing but its own frame. The frame's `len = 1492` guard is the leaf's own: every data premise is under it. *)
Lemma dec_leafb_inspect :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw len : Z) (bs : list byte),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 raw -> getr regsT 11 = w64 len -> 0 <= len < 2 ^ 64 ->
  (len = 1492 -> In (raw, len) (ablocks B lyc Sc) /\ length bs = 1492%nat /\
     garr8 segs (mrestrict (w_H W) memT) raw (map (fun b : byte => bv_unsigned b) bs)) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CInsp.REAC_FRAME_INSPECT) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (CInsp.inspect_result len bs) [] (fun _ => True)).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw len bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 Hlen HB.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  (* the stack pointer in the leaf statement's own spelling, so that lia sees one atom *)
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  assert (Ha1 : bv_unsigned (getr regsT 11) = len)
    by (rewrite H11; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
  assert (Ha0 : bv_unsigned (getr regsT 10) = raw mod 2 ^ 64)
    by (rewrite H10; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 64) with (2 ^ 64); reflexivity).
  assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len) by exact Ha1.
  assert (Ha0L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = raw mod 2 ^ 64) by exact Ha0.
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CInsp.REAC_FRAME_INSPECT (Some (CInsp.inspect_result len bs)) [] (fun _ => True)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & _);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2 | exact I] ].
  - intros a Ha. inversion Ha.
  - intros HPRE. rewrite <- Ha1L.
    refine (HLEAF fx lyc Sc W regsT memT mdc bs (sp0 - STK) HPRE _ _ _ _ _).
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CInsp.REAC_FRAME_INSPECT_FRAME. lia.
    + intros H1492.
      assert (Hl : len = 1492) by (rewrite <- Ha1L; exact H1492).
      destruct (HB Hl) as (Hin & Hbl & HG). rewrite Hl in Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw 1492 HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
      pose proof (req_size_pos 1492 ltac:(lia)) as [Hq1 Hq2].
      assert (Hraw : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = raw) by (rewrite Ha0L; apply Z.mod_small; lia).
      rewrite Hraw.
      split; [exact Hbl|].
      split; [apply (dec_leafb_bytes_garr8 W memT raw bs HG); [lia | rewrite Hbl; pose proof alloc_ceiling_val; lia]|].
      split; [lia|].
      split; [unfold BKA.off_stk, CInsp.REAC_FRAME_INSPECT_FRAME; left; lia|].
      split; [apply dec_leafb_app_stack; unfold CInsp.REAC_FRAME_INSPECT_FRAME; lia|].
      split; [apply dec_leafb_app_stack; lia|].
      split; [exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR)|].
      split; [unfold BKA.off_stk, CInsp.REAC_FRAME_INSPECT_FRAME, BCells.GOT_CELL_K; left; lia|].
      split; [unfold BKA.off_stk, CInsp.REAC_FRAME_INSPECT_FRAME, BCells.CELL_K; left; lia|].
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw 1492 raw 1492 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CInsp.REAC_FRAME_INSPECT_FRAME; lia
         | unfold CInsp.REAC_FRAME_INSPECT_FRAME; lia].
    + intros H1492.
      assert (Hl : len = 1492) by (rewrite <- Ha1L; exact H1492).
      destruct (HB Hl) as (Hin & Hbl & HG). rewrite Hl in Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw 1492 HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & _).
      pose proof (req_size_pos 1492 ltac:(lia)) as [Hq1 Hq2].
      assert (Hraw : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = raw) by (rewrite Ha0L; apply Z.mod_small; lia).
      rewrite Hraw.
      split; [exact (proj1 (dec_leafb_rng_cells W))|].
      split; [exact (proj2 (dec_leafb_rng_cells W))|].
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw 1492 (raw + 12) 4 HAR Hin ltac:(lia) ltac:(lia))|].
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw 1492 (raw + 1490) 2 HAR Hin ltac:(lia) ltac:(lia))|].
      split.
      * pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw 1492 (raw + 12) 4 HAR Hin
          ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
        unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
        replace (raw + 12 + 4 - 1) with (raw + 15) in HS by lia.
        replace ((raw + 15) / 8 + 2147450880 - ((raw + 12) / 8 + 2147450880) + 1)
          with ((raw + 15) / 8 - (raw + 12) / 8 + 1) in HS by lia.
        exact HS.
      * pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw 1492 (raw + 1490) 2 HAR Hin
          ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
        unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
        replace (raw + 1490 + 2 - 1) with (raw + 1491) in HS by lia.
        replace ((raw + 1491) / 8 + 2147450880 - ((raw + 1490) / 8 + 2147450880) + 1)
          with ((raw + 1491) / 8 - (raw + 1490) / 8 + 1) in HS by lia.
        exact HS.
Qed.

(* reac_frame_counter (lib/B/Prog/reac_frame_counter_cg.v): reads the two counter bytes at a0 + 14; writes
   nothing but its own frame. *)
Lemma dec_leafb_counter :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw blen : Z) (bs : list byte),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 raw ->
  In (raw, blen) (ablocks B lyc Sc) -> 16 <= blen -> length bs = Z.to_nat blen ->
  garr8 segs (mrestrict (w_H W) memT) raw (map (fun b : byte => bv_unsigned b) bs) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CCnt.REAC_FRAME_COUNTER) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (CCnt.counter_result bs) [] (fun _ => True)).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw blen bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 Hin Hblen Hbs HG.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ raw blen HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hmr).
  pose proof (req_size_pos blen ltac:(lia)) as [Hq1 Hq2].
  assert (Ha0L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)) = raw).
  { assert (Hx : bv_unsigned (getr regsT 10) = raw)
      by (rewrite H10; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
    exact Hx. }
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CCnt.REAC_FRAME_COUNTER (Some (CCnt.counter_result bs)) [] (fun _ => True)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & _);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2 | exact I] ].
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (HLEAF fx lyc Sc W regsT memT mdc bs (sp0 - STK) HPRE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + rewrite Hbs. lia.
    + rewrite Ha0L. lia.
    + rewrite Ha0L. apply (dec_leafb_bytes_garr8 W memT raw bs HG); [lia | rewrite Hbs; lia].
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CCnt.REAC_FRAME_COUNTER_FRAME. lia.
    + rewrite Ha0L. unfold BKA.off_stk, CCnt.REAC_FRAME_COUNTER_FRAME. left. lia.
    + apply dec_leafb_app_stack; unfold CCnt.REAC_FRAME_COUNTER_FRAME; lia.
    + apply dec_leafb_app_stack; lia.
    + exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR).
    + unfold BKA.off_stk, CCnt.REAC_FRAME_COUNTER_FRAME, BCells.GOT_CELL_K. left. lia.
    + unfold BKA.off_stk, CCnt.REAC_FRAME_COUNTER_FRAME, BCells.CELL_K. left. lia.
    + rewrite Ha0L.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw blen (raw + 14) 2 HAR Hin
               ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CCnt.REAC_FRAME_COUNTER_FRAME; lia | unfold CCnt.REAC_FRAME_COUNTER_FRAME; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + rewrite Ha0L.
      exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw blen (raw + 14) 2 HAR Hin ltac:(lia) ltac:(lia)).
    + rewrite Ha0L.
      pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw blen (raw + 14) 2 HAR Hin
        ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace (raw + 14 + 2 - 1) with (raw + 15) in HS by lia.
      replace ((raw + 15) / 8 + 2147450880 - ((raw + 14) / 8 + 2147450880) + 1)
        with ((raw + 15) / 8 - (raw + 14) / 8 + 1) in HS by lia.
      exact HS.
Qed.

(* The post of a leaf that returns nothing (check_braid): dec_leafb_ret without the a0 clause. *)
Definition dec_leafb_ret_nores (STK sp0 : Z) (FP : list (Z * Z)) ly S (W0 : world segs) mem md own lyc Sc
    (W : world segs) (memT : word -> option byte) (k : Z) (regsT : bvmap 5 word)
    (WR : list (Z * Z)) (X : (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (YK11.mkst regs2 (getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
    @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr WR a ->
       aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
    X mem2.

(* The braid relation of the walk's view is the leaf's raw-memory one: both read the same bytes, and a byte the
   view shows is never hidden. *)
Lemma dec_leafb_braid_map : forall (W : world segs) (memT : word -> option byte) audio pcm nch ns,
  dec_crt_braid (aview segs (w_H W) memT) audio pcm nch ns ->
  CBraid.braid_map memT audio pcm nch ns.
Proof.
  intros W memT audio pcm nch ns HBR ch s j Hch Hs Hj.
  destruct (HBR ch s j Hch Hs Hj) as (b & Hp & Ha).
  destruct (dec_leafb_mrd_aview W memT _ _ Hp) as (b1 & Hb1 & Hv1).
  destruct (dec_leafb_mrd_aview W memT _ _ Ha) as (b2 & Hb2 & Hv2).
  exists b1. split; [exact Hb1|]. replace b1 with b2; [exact Hb2|]. apply bv_eq. rewrite Hv1, Hv2. reflexivity.
Qed.

(* check_braid (lib/B/Prog/check_braid_cg.v): reads the two buffers and returns nothing; writes only its frame. *)
Lemma dec_leafb_check_braid :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o audio pcm nch ns bA nA bP nP : Z),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 audio -> getr regsT 11 = w64 pcm ->
  getr regsT 12 = w64 nch -> getr regsT 13 = w64 ns ->
  1 <= nch <= 127 -> 1 <= ns <= 127 ->
  In (bA, nA) (ablocks B lyc Sc) -> bA <= audio -> audio + 3 * nch * ns + 3 * (nch mod 2) <= bA + req_size nA ->
  In (bP, nP) (ablocks B lyc Sc) -> bP <= pcm -> pcm + 3 * nch * ns <= bP + req_size nP ->
  dec_crt_braid (aview segs (w_H W) memT) audio pcm nch ns ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CBraid.CHECK_BRAID) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret_nores STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT [] (fun _ => True)).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o audio pcm nch ns bA nA bP nP
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 H12 H13 Hnch Hns HinA HbA1 HbA2 HinP HbP1 HbP2 HBR.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR HinA) as (_ & HA4096 & HAceil & HAapp & _ & _ & HAmr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bP nP HAR HinP) as (_ & HP4096 & HPceil & HPapp & _ & _ & HPmr).
  pose proof (req_size_pos nA ltac:(lia)) as [HqA1 HqA2].
  pose proof (req_size_pos nP ltac:(lia)) as [HqP1 HqP2].
  assert (Hmod : 0 <= nch mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  assert (HaudL : YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 audio) by exact H10.
  assert (HpcmL : YK11.getr regsT (Z_to_bv 5 11) = Z_to_bv 64 pcm) by exact H11.
  assert (HnchL : YK11.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 nch) by exact H12.
  assert (HnsL : YK11.getr regsT (Z_to_bv 5 13) = Z_to_bv 64 ns) by exact H13.
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CBraid.CHECK_BRAID None [] (fun _ => True)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & _ & Heff2 & Hgr2 & _);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact Heff2|]; split; [exact Hgr2 | exact I] ].
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (HLEAF fx lyc Sc W regsT memT mdc audio pcm nch ns (sp0 - STK) HPRE HaudL HpcmL HnchL HnsL
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (dec_leafb_braid_map W memT audio pcm nch ns HBR).
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CBraid.CHECK_BRAID_FRAME. lia.
    + unfold CBraid.CHECK_BRAID_FRAME. left. lia.
    + unfold CBraid.CHECK_BRAID_FRAME. left. lia.
    + exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR).
    + apply dec_leafb_app_stack; unfold CBraid.CHECK_BRAID_FRAME; lia.
    + apply dec_leafb_app_stack; lia.
    + unfold BKA.off_stk, CBraid.CHECK_BRAID_FRAME, BCells.GOT_CELL_K, BCells.MIDEND. left. lia.
    + exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc bA nA audio (3 * nch * ns + 3 * (nch mod 2))
               HAR HinA ltac:(lia) ltac:(nia) ltac:(lia)).
    + exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc bP nP pcm (3 * nch * ns)
               HAR HinP ltac:(lia) ltac:(nia) ltac:(lia)).
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CBraid.CHECK_BRAID_FRAME; lia | unfold CBraid.CHECK_BRAID_FRAME; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc bA nA audio (3 * nch * ns + 3 * (nch mod 2))
               HAR HinA ltac:(lia) ltac:(lia)).
    + exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc bP nP pcm (3 * nch * ns) HAR HinP ltac:(lia) ltac:(lia)).
    + pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bA nA audio
        (3 * nch * ns + 3 * (nch mod 2)) HAR HinA ltac:(lia) ltac:(nia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace ((audio + (3 * nch * ns + 3 * (nch mod 2)) - 1) / 8 + 2147450880 -
                 (audio / 8 + 2147450880) + 1)
        with ((audio + (3 * nch * ns + 3 * (nch mod 2)) - 1) / 8 - audio / 8 + 1) in HS by lia.
      exact HS.
    + pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bP nP pcm (3 * nch * ns)
        HAR HinP ltac:(lia) ltac:(nia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace ((pcm + 3 * nch * ns - 1) / 8 + 2147450880 - (pcm / 8 + 2147450880) + 1)
        with ((pcm + 3 * nch * ns - 1) / 8 - pcm / 8 + 1) in HS by lia.
      exact HS.
Qed.

(* Two raw-byte helpers the write-set leaves need: appending byte runs, and the way back from the leaf's
   bytes_at to the walk's garr8 (every byte of the written block is present, so none is hidden). *)
Lemma dec_leafb_bytes_app : forall (memT : word -> option byte) a (l1 l2 : list byte),
  LMem.bytes_at segs memT a l1 -> LMem.bytes_at segs memT (a + Z.of_nat (length l1)) l2 ->
  LMem.bytes_at segs memT a (l1 ++ l2).
Proof.
  intros memT a l1 l2 (H01 & Ht1 & H1) (H02 & Ht2 & H2).
  unfold LMem.bytes_at. rewrite length_app.
  split; [exact H01|]. split; [lia|].
  intros i Hi.
  destruct (Nat.ltb_spec i (length l1)) as [Hlt | Hge].
  - rewrite nth_error_app1 by exact Hlt. exact (H1 i Hlt).
  - rewrite nth_error_app2 by exact Hge.
    replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
    apply H2. lia.
Qed.

Lemma dec_leafb_garr8_of_bytes : forall (W : world segs) (memT : word -> option byte) p (bs : list byte),
  LMem.bytes_at segs memT p bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> apresent (w_H W) memT (p + i)) ->
  garr8 segs (mrestrict (w_H W) memT) p (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros W memT p bs (H0 & Ht & HB) HP j Hj.
  rewrite length_map in Hj.
  assert (Hv : w_H W (Z_to_bv 64 (p + Z.of_nat j)) = false) by (apply (HP (Z.of_nat j)); lia).
  pose proof (HB j Hj) as Hb. rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj) in Hb.
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) bs) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; lia).
  rewrite (map_nth (fun b : byte => bv_unsigned b) bs (Z_to_bv 8 0) j).
  pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as HR.
  change (bv_modulus 8) with 256 in HR.
  split; [|exact HR].
  intros kk Hkk. assert (kk = 0%nat) as -> by lia.
  rewrite Nat2Z.inj_0, Z.add_0_r.
  rewrite <- (dec_leafb_mrd W memT (p + Z.of_nat j) Hv), Hb. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
  change (bv_modulus 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* reac_decode_plain_le (lib/B/Prog/reac_decode_plain_le_cg.v): reads the copy and the mode's two fields and,
   when the geometry is good, writes the 3 * nch * ns output bytes of the plain decoder. The caller says where
   the mode's two fields are (a live block of the call state, or the image's mode table: either way as the
   visibility, the shadow and the two values the walk's view shows). *)
Lemma dec_leafb_plain :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw len mode out nch ns olen : Z) (bs : list byte),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 raw -> getr regsT 11 = w64 len ->
  getr regsT 12 = w64 mode -> getr regsT 13 = w64 out ->
  0 <= len < 2 ^ 64 -> -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  In (raw, len) (ablocks B lyc Sc) -> (len = 1492 -> length bs = 1492%nat) ->
  garr8 segs (mrestrict (w_H W) memT) raw (map (fun b : byte => bv_unsigned b) bs) ->
  In (out, olen) (ablocks B lyc Sc) -> out <> raw ->
  (* both guarded by plain_ok: the leaf writes nothing without it, and the harness's olen is 1 when the
     input-chosen geometry is not positive (a Theorem Labs lane's crt1 lane, 2026-10-29) *)
  (CPlain.plain_ok len bs nch ns = true -> 3 * nch * ns <= olen) ->
  (CPlain.plain_ok len bs nch ns = true ->
     forall a, out <= a < out + 3 * nch * ns ->
       awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  in_app mode 12 -> mode mod 4 = 0 ->
  (* visibility, not presence: a table mode's bytes are image bytes the overlay need not hold *)
  (forall a, mode + 4 <= a < mode + 12 -> w_H W (Z_to_bv 64 a) = false) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF (mode + 4) 8 ->
  val_mem segs (mrestrict (w_H W) memT) (mode + 4) 4%nat (nch mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memT) (mode + 8) 4%nat (ns mod 2 ^ 32) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CPlain.REAC_DECODE_PLAIN_LE) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (if CPlain.plain_ok len bs nch ns then ns else -1)
       (if CPlain.plain_ok len bs nch ns then [(out, out + 3 * nch * ns)] else [])
       (fun m2 => CPlain.plain_ok len bs nch ns = true ->
          garr8 segs (mrestrict (w_H W) m2) out
            (map (fun b : byte => bv_unsigned b) (CPlain.plain_out bs nch ns)))).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw len mode out nch ns olen bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 H12 H13 Hlen Hnch Hns Hinr Hbs HG Hino Hne HolenG HawrG
    Hmapp Hm4 Hmpres Hmra Hmv1 Hmv2.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hinr) as (_ & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrmr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (_ & Ho4096 & Hoceil & Hoapp & Hopres & _ & Homr).
  pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
  pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
  pose proof (sep_blocks segs B LAWS lyc Sc W memT mdc out olen raw len HAR Hino Hinr
    ltac:(intros Hq; injection Hq as Hq1 _; exact (Hne Hq1))) as Hdisj.
  unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
  assert (Hmlo : 4096 <= mode) by (destruct Hmapp as [Hx _]; lia).
  assert (Hmhi : mode + 12 <= alloc_ceiling)
    by (destruct Hmapp as [_ [Hx | [Hx Hy]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
  assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len).
  { assert (Hx : bv_unsigned (getr regsT 11) = len)
      by (rewrite H11; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
    exact Hx. }
  assert (Ha0L : YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 raw) by exact H10.
  assert (Ha2L : YK11.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 mode) by exact H12.
  assert (Ha3L : YK11.getr regsT (Z_to_bv 5 13) = Z_to_bv 64 out) by exact H13.
  (* plain_ok says the geometry is positive and the copy is the 1492-byte frame *)
  assert (HokF : forall (l : Z), CPlain.plain_ok l bs nch ns = true -> l = 1492 /\ 0 < nch /\ 0 < ns).
  { intros l Hok. unfold CPlain.plain_ok in Hok.
    apply andb_true_iff in Hok as [Hok Hprod]. apply andb_true_iff in Hok as [Hok Hns0].
    apply andb_true_iff in Hok as [Hwf Hnch0].
    unfold CInsp.inspect_wf in Hwf. apply andb_true_iff in Hwf as [Hwf _].
    apply andb_true_iff in Hwf as [Hwf _]. apply andb_true_iff in Hwf as [Hwf _].
    apply andb_true_iff in Hwf as [Hl _]. apply Z.eqb_eq in Hl.
    apply Z.ltb_lt in Hnch0. apply Z.ltb_lt in Hns0. auto. }
  assert (Hmode8 : LMem.bytes_at segs memT (mode + 4) (LMem.le4 (Z_to_bv 64 nch) ++ LMem.le4 (Z_to_bv 64 ns))).
  { apply dec_leafb_bytes_app.
    - unfold LMem.le4. apply (dec_leafb_bytes_le W memT (mode + 4) 4%nat _ (nch mod 2 ^ 32) Hmv1);
        [ rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); change (8 * Z.of_nat 4) with 32;
          rewrite (Z.mod_mod nch (2 ^ 32)) by lia;
          apply (dec_leafb_mod_pow2_mod nch 32 64); lia
        | lia | change (Z.of_nat 4) with 4; lia ].
    - unfold LMem.le4. rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
      replace (mode + 4 + 4) with (mode + 8) by lia.
      apply (dec_leafb_bytes_le W memT (mode + 8) 4%nat _ (ns mod 2 ^ 32) Hmv2);
        [ rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); change (8 * Z.of_nat 4) with 32;
          rewrite (Z.mod_mod ns (2 ^ 32)) by lia;
          apply (dec_leafb_mod_pow2_mod ns 32 64); lia
        | lia | change (Z.of_nat 4) with 4; lia ]. }
  assert (HoutLen : length (CPlain.plain_out bs nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CPlain.plain_out; rewrite !length_map, length_seq; reflexivity).
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CPlain.REAC_DECODE_PLAIN_LE (Some (if CPlain.plain_ok len bs nch ns then ns else -1))
                (if CPlain.plain_ok len bs nch ns then [(out, out + 3 * nch * ns)] else [])
                (fun m2 => CPlain.plain_ok len bs nch ns = true ->
                   LMem.bytes_at segs m2 out (CPlain.plain_out bs nch ns))
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & HX2);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2|];
      intros Hok; destruct (HokF len Hok) as (Hl & Hn0 & Hs0); pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen;
      apply (dec_leafb_garr8_of_bytes W mem2 out _ (HX2 Hok));
      intros i Hi; rewrite HoutLen in Hi; apply Hgr2; exact (proj1 (Hopres (out + i) ltac:(nia))) ].
  - (* the written range is one the caller's journal lets the callee write *)
    intros a Ha. destruct (CPlain.plain_ok len bs nch ns) eqn:Hok; [|inversion Ha].
    apply (HawrG ltac:(first [exact Hok | reflexivity])). inversion Ha as [r l Hr Hl | r l Hr Hl]; subst; cbn [fst snd] in *; [lia | inversion Hr].
  - intros HPRE. rewrite <- Ha1L.
    refine (HLEAF fx lyc Sc W regsT memT mdc bs raw mode out nch ns (sp0 - STK) HPRE
              Ha0L Ha2L Ha3L _ _ _ _ _ _ Hmode8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + lia.
    + lia.
    + lia.
    + intros Hl. rewrite Ha1L in Hl. split; [exact (Hbs Hl)|].
      apply (dec_leafb_bytes_garr8 W memT raw bs HG); [lia | rewrite (Hbs Hl); lia].
    + lia.
    + lia.
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + intros Hl. rewrite Ha1L in Hl.
      unfold BKA.off_stk, CPlain.REAC_DECODE_PLAIN_LE_D. left. lia.
    + unfold BKA.off_stk, CPlain.REAC_DECODE_PLAIN_LE_D. left. lia.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      split; [exact (dec_leafb_wr_at_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
                       HAR Hino ltac:(lia) ltac:(nia))|].
      split; [nia|].
      split; [subst len; nia|].
      unfold BKA.off_stk, CPlain.REAC_DECODE_PLAIN_LE_D. left. nia.
    + apply dec_leafb_app_stack; unfold CPlain.REAC_DECODE_PLAIN_LE_D; lia.
    + apply dec_leafb_app_stack; lia.
    + exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR).
    + unfold BKA.off_stk, CPlain.REAC_DECODE_PLAIN_LE_D, BCells.GOT_CELL_K, BCells.MIDEND. left. lia.
    + intros Hl. rewrite Ha1L in Hl.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr
               ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _. apply (dec_leafb_addressable W memT (mode + 4) 8 Hmra); [lia | lia | |].
      * unfold BCells.APPMEM_END. unfold kHighMemEnd in *. lia.
      * intros i Hi. replace (mode + 4 + i) with (mode + (4 + i)) by lia.
        apply (@dec_leafb_app_of_in_app rc mode 12); [exact Hmapp | lia].
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
               HAR Hino ltac:(lia) ltac:(nia) ltac:(nia)).
    + intros Hl. lia.
    + intros _. split; lia.
    + intros Hok. lia.
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CPlain.REAC_DECODE_PLAIN_LE_D; lia | unfold CPlain.REAC_DECODE_PLAIN_LE_D; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hl. rewrite Ha1L in Hl.
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr ltac:(lia) ltac:(lia))|].
      pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr
        ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace (raw + 1492 - 1) with (raw + 1491) in HS by lia.
      replace ((raw + 1491) / 8 + 2147450880 - (raw / 8 + 2147450880) + 1)
        with ((raw + 1491) / 8 - raw / 8 + 1) in HS by lia.
      exact HS.
    + intros _.
      split; [apply (dec_leafb_rng W); [lia | lia | intros a Ha; apply Hmpres; lia]|].
      pose proof (dec_leafb_rng_shadow W memT (mode + 4) 8 Hmra ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace (mode + 4 + 8 - 1) with (mode + 11) in HS by lia.
      replace ((mode + 11) / 8 + 2147450880 - ((mode + 4) / 8 + 2147450880) + 1)
        with ((mode + 11) / 8 - (mode + 4) / 8 + 1) in HS by lia.
      exact HS.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
                       HAR Hino ltac:(lia) ltac:(nia))|].
      pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
        HAR Hino ltac:(lia) ltac:(nia) ltac:(nia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace ((out + 3 * nch * ns - 1) / 8 + 2147450880 - (out / 8 + 2147450880) + 1)
        with ((out + 3 * nch * ns - 1) / 8 - out / 8 + 1) in HS by lia.
      exact HS.
    + intros x Hx. rewrite Ha1L in Hx.
      destruct (CPlain.plain_ok len bs nch ns) eqn:Hok; [|inversion Hx].
      destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      assert (Hxr : out <= x < out + 3 * nch * ns)
        by (inversion Hx as [r l Hr Hl2 | r l Hr Hl2]; subst; cbn [fst snd] in *; [lia | inversion Hr]).
      exact (dec_leafb_wr_block B LAWS lyc Sc W memT mdc out olen HAR Hino x ltac:(nia)).
Qed.


(* The div-by-36 word both upstream leaves read: one of dec_crt_cells' rows (the frozen statement's
   `In (z8 (ANum (decodeb_obj 9)) 0xe38e38e38e38e38f)`), so it holds at every AR state with no transport of a
   read-only view. *)
Lemma dec_leafb_div36_seg : dec_seg_covers CChan.UPSTREAM_DIV36_AT 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_leafb_div36 : dec_crt_cells B ->
  forall (ly : alayout) (S : astate) (W : world segs) (memT : word -> option byte) (md : Model),
    @AR rc segs B ly S W memT md ->
    LMem.bytes_at segs memT CChan.UPSTREAM_DIV36_AT (LMem.le8 (Z_to_bv 64 CChan.UPSTREAM_DIV36)).
Proof.
  intros HC ly S W memT md HAR.
  pose proof (w_Hoff W) as Hoff.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview segs (w_H W) memT)) (as_const B ly))
    by (eapply am_const; exact HM).
  pose proof (HC ly) as HROWS. repeat match type of HROWS with _ /\ _ => destruct HROWS as [? HROWS] end.
  assert (HE : LMem.wa CChan.UPSTREAM_DIV36 = Z_to_bv 64 CChan.UPSTREAM_DIV36) by reflexivity.
  rewrite <- HE.
  exact (dec_leafb_z8 B ly _ memT CChan.UPSTREAM_DIV36_AT CChan.UPSTREAM_DIV36 Hoff HK
           ltac:(assumption) dec_leafb_div36_seg ltac:(clear; apply Z.leb_le; reflexivity)).
Qed.

Lemma dec_leafb_rng_div36 : forall (W : world segs),
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) CChan.UPSTREAM_DIV36_AT 8.
Proof.
  intros W. apply (dec_leafb_rng W);
    [unfold CChan.UPSTREAM_DIV36_AT; lia | unfold CChan.UPSTREAM_DIV36_AT; lia |].
  intros a Ha. replace a with (CChan.UPSTREAM_DIV36_AT + (a - CChan.UPSTREAM_DIV36_AT)) by lia.
  apply (dec_leafb_covers_visible (w_H W) CChan.UPSTREAM_DIV36_AT 8);
    [exact (w_Hoff W) | exact dec_leafb_div36_seg | lia | clear; apply Z.leb_le; reflexivity].
Qed.

(* reac_upstream_channels (lib/B/Prog/reac_upstream_channels_cg.v): reads only the div-by-36 word, writes
   nothing at all (its X is m2 = memT), and returns the channel count of the length in a0. *)
Lemma dec_leafb_upstream_channels :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CChan.REAC_UPSTREAM_CHANNELS) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (CChan.upstream_result (bv_unsigned (getr regsT 10))) [] (fun m2 => m2 = memT)).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp.
  pose proof (proj1 HJ) as HAR.
  assert (Hres : CChan.upstream_result (bv_unsigned (getr regsT 10)) =
                 CChan.upstream_result (bv_unsigned (YK11.getr regsT (Z_to_bv 5 10)))) by reflexivity.
  rewrite Hres.
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CChan.REAC_UPSTREAM_CHANNELS
                (Some (CChan.upstream_result (bv_unsigned (YK11.getr regsT (Z_to_bv 5 10))))) []
                (fun m2 => m2 = memT)
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & HX2);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2 | exact HX2] ].
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (HLEAF fx lyc Sc W regsT memT mdc HPRE _ _).
    + exact (dec_leafb_div36 HC lyc Sc W memT mdc HAR).
    + exact (dec_leafb_rng_div36 W).
Qed.

(* reac_upstream_decode (lib/B/Prog/reac_upstream_decode_cg.v), one lemma for the three call sites: the data
   premises are guarded by `raw <> 0` and `out <> 0`, which is how the two refusing calls (a0 = 0, a2 = 0) and
   the real one all fit. *)
Lemma dec_leafb_upstream_decode :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw len out olen : Z) (bs : list byte),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 raw -> getr regsT 11 = w64 len -> getr regsT 12 = w64 out ->
  0 <= len < 2 ^ 32 ->
  (raw <> 0 -> In (raw, len) (ablocks B lyc Sc) /\ length bs = Z.to_nat len /\
     garr8 segs (mrestrict (w_H W) memT) raw (map (fun b : byte => bv_unsigned b) bs)) ->
  (out <> 0 -> In (out, olen) (ablocks B lyc Sc) /\ 36 * CUp.up_nch len <= olen /\ out <> raw /\
     (forall a, out <= a < out + 36 * CUp.up_nch len ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CUp.REAC_UPSTREAM_DECODE) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (if CUp.up_ok raw out len bs then 12 else -1)
       (if CUp.up_ok raw out len bs then [(out, out + 36 * CUp.up_nch len)] else [])
       (fun m2 => CUp.up_ok raw out len bs = true ->
          garr8 segs (mrestrict (w_H W) m2) out
            (map (fun b : byte => bv_unsigned b) (CDec.braid_out bs (CUp.up_nch len) 12)))).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw len out olen bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 H12 Hlen HRAW HOUT.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len).
  { assert (Hx : bv_unsigned (getr regsT 11) = len)
      by (rewrite H11; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
    exact Hx. }
  assert (Ha0L : YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 raw) by exact H10.
  assert (Ha2L : YK11.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 out) by exact H12.
  (* up_ok asks for both pointers and the length, so the guarded premises are available under it *)
  assert (HokF : CUp.up_ok raw out len bs = true -> raw <> 0 /\ out <> 0 /\ 0 <= CUp.up_nch len).
  { intros Hok. unfold CUp.up_ok in Hok.
    apply andb_true_iff in Hok as [Hok _]. apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [Hok _]. apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [Hok Hnch]. apply andb_true_iff in Hok as [Hraw0 Hout0].
    apply negb_true_iff in Hraw0. apply Z.eqb_neq in Hraw0.
    apply negb_true_iff in Hout0. apply Z.eqb_neq in Hout0.
    apply Z.leb_le in Hnch. auto. }
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CUp.REAC_UPSTREAM_DECODE (Some (if CUp.up_ok raw out len bs then 12 else -1))
                (if CUp.up_ok raw out len bs then [(out, out + 36 * CUp.up_nch len)] else [])
                (fun m2 => CUp.up_ok raw out len bs = true ->
                   LMem.bytes_at segs m2 out (CDec.braid_out bs (CUp.up_nch len) 12))
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & HX2);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2|];
      intros Hok; destruct (HokF Hok) as (Hr0 & Ho0 & Hn0);
      destruct (HOUT Ho0) as (Hino & Holen & Hne & Hawr);
      destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen (proj1 HJ) Hino) as (_ & _ & _ & _ & Hopres & _ & _);
      apply (dec_leafb_garr8_of_bytes W mem2 out _ (HX2 Hok));
      intros i Hi;
      assert (Hbl : length (CDec.braid_out bs (CUp.up_nch len) 12) = Z.to_nat (3 * CUp.up_nch len * 12))
        by (unfold CDec.braid_out; rewrite !length_map, length_seq; reflexivity);
      rewrite Hbl in Hi; apply Hgr2;
      exact (proj1 (Hopres (out + i) ltac:(pose proof (req_size_pos olen ltac:(lia)); nia))) ].
  - intros a Ha. destruct (CUp.up_ok raw out len bs) eqn:Hok; [|inversion Ha].
    destruct (HokF ltac:(first [exact Hok | reflexivity])) as (Hr0 & Ho0 & Hn0).
    destruct (HOUT Ho0) as (_ & _ & _ & Hawr).
    apply Hawr. inversion Ha as [r l Hr Hl | r l Hr Hl]; subst; cbn [fst snd] in *; [lia | inversion Hr].
  - intros HPRE. rewrite <- Ha1L.
    refine (HLEAF fx lyc Sc W regsT memT mdc bs raw out (sp0 - STK) HPRE Ha0L Ha2L
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + (* 0 <= raw < 2 ^ 64 *)
      destruct (Z.eq_dec raw 0) as [->|Hr0]; [lia|].
      destruct (HRAW Hr0) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (_ & H4096 & Hceil & _).
      pose proof (req_size_pos len ltac:(lia)). lia.
    + destruct (Z.eq_dec out 0) as [->|Ho0]; [lia|].
      destruct (HOUT Ho0) as (Hin & _ & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos olen ltac:(lia)). lia.
    + rewrite Ha1L. lia.
    + exact (dec_leafb_div36 HC lyc Sc W memT mdc HAR).
    + intros Hr0 Ho0 Hn0. rewrite Ha1L.
      destruct (HRAW Hr0) as (Hin & Hbl & HG).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
      split; [exact Hbl|].
      apply (dec_leafb_bytes_garr8 W memT raw bs HG); [lia | rewrite Hbl; lia].
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF Hok) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & Hne & _). destruct (HRAW Hr0) as (Hinr & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (_ & Ho4096 & Hoceil & _ & _ & _ & Homr).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hinr) as (_ & Hr4096 & Hrceil & _ & _ & _ & Hrmr).
      pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
      pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
      pose proof (sep_blocks segs B LAWS lyc Sc W memT mdc out olen raw len HAR Hino Hinr
        ltac:(intros Hq; injection Hq as Hq1 _; exact (Hne Hq1))) as Hdisj.
      unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
      rewrite Ha1L.
      split; [exact (dec_leafb_wr_at_block B LAWS lyc Sc W memT mdc out olen out (36 * CUp.up_nch len)
                       HAR Hino ltac:(lia) ltac:(lia))|].
      split; [lia|]. lia.
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CUp.REAC_UPSTREAM_DECODE_D. lia.
    + intros Hr0 Ho0 Hn0. rewrite Ha1L. destruct (HRAW Hr0) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
      unfold BKA.off_stk, CUp.REAC_UPSTREAM_DECODE_D. left. lia.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF Hok) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & _ & _). rewrite Ha1L.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (_ & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos olen ltac:(lia)) as [Hq1 Hq2].
      unfold BKA.off_stk, CUp.REAC_UPSTREAM_DECODE_D. left. lia.
    + unfold BKA.off_stk, CUp.REAC_UPSTREAM_DECODE_D, CUp.DIV36_MAGIC_AT. left. lia.
    + apply dec_leafb_app_stack; unfold CUp.REAC_UPSTREAM_DECODE_D; lia.
    + apply dec_leafb_app_stack; lia.
    + exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR).
    + unfold BKA.off_stk, CUp.REAC_UPSTREAM_DECODE_D, BCells.GOT_CELL_K, BCells.MIDEND. left. lia.
    + intros Hr0 Ho0 Hn0. rewrite Ha1L. destruct (HRAW Hr0) as (Hin & _ & _).
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw len raw len HAR Hin
               ltac:(lia) ltac:(lia) ltac:(pose proof (req_size_pos len ltac:(lia)); lia)).
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF Hok) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & _ & _). rewrite Ha1L.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc out olen out (36 * CUp.up_nch len)
               HAR Hino ltac:(lia) ltac:(lia) ltac:(pose proof (req_size_pos olen ltac:(lia)); lia)).
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CUp.REAC_UPSTREAM_DECODE_D; lia | unfold CUp.REAC_UPSTREAM_DECODE_D; lia].
    + exact (dec_leafb_rng_div36 W).
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hr0 Ho0 Hn0. rewrite Ha1L. destruct (HRAW Hr0) as (Hin & _ & _).
      exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw len raw len HAR Hin
               ltac:(lia) ltac:(pose proof (req_size_pos len ltac:(lia)); lia)).
    + intros Hr0 Ho0 Hn0. rewrite Ha1L. destruct (HRAW Hr0) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hin) as (Hal16 & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos len ltac:(lia)) as [Hq1 Hq2].
      destruct (Z.eq_dec len 0) as [->|Hl0].
      * (* an empty copy: the leaf's shadow range is empty, raw being 16-aligned *)
        apply (dec_leafb_rng W); [unfold BCells.ASAN_K; lia | unfold BCells.ASAN_K; lia |].
        intros a Ha. exfalso. unfold BCells.ASAN_K in Ha. lia.
      * pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw len raw len HAR Hin
          ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
        unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
        replace ((raw + len - 1) / 8 + 2147450880 - (raw / 8 + 2147450880) + 1)
          with ((raw + len - 1) / 8 - raw / 8 + 1) in HS by lia.
        exact HS.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF Hok) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & _ & _). rewrite Ha1L.
      exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc out olen out (36 * CUp.up_nch len)
               HAR Hino ltac:(lia) ltac:(pose proof (req_size_pos olen ltac:(lia)); lia)).
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF Hok) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & _ & _). rewrite Ha1L.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (Hal16 & H4096 & Hceil & _ & _ & _ & Hmr).
      pose proof (req_size_pos olen ltac:(lia)) as [Hq1 Hq2].
      destruct (Z.eq_dec (CUp.up_nch len) 0) as [Hz|Hz].
      * rewrite Hz. apply (dec_leafb_rng W); [unfold BCells.ASAN_K; lia | unfold BCells.ASAN_K; lia |].
        intros a Ha. exfalso. unfold BCells.ASAN_K in Ha. lia.
      * pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc out olen out (36 * CUp.up_nch len)
          HAR Hino ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
        unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
        replace ((out + 36 * CUp.up_nch len - 1) / 8 + 2147450880 - (out / 8 + 2147450880) + 1)
          with ((out + 36 * CUp.up_nch len - 1) / 8 - out / 8 + 1) in HS by lia.
        exact HS.
    + intros x Hx. rewrite Ha1L in Hx.
      destruct (CUp.up_ok raw out len bs) eqn:Hok; [|inversion Hx].
      destruct (HokF ltac:(first [exact Hok | reflexivity])) as (Hr0 & Ho0 & Hn0).
      destruct (HOUT Ho0) as (Hino & Holen & _ & _).
      assert (Hxr : out <= x < out + 36 * CUp.up_nch len)
        by (inversion Hx as [r l Hr Hl2 | r l Hr Hl2]; subst; cbn [fst snd] in *; [lia | inversion Hr]).
      exact (dec_leafb_wr_block B LAWS lyc Sc W memT mdc out olen HAR Hino x
               ltac:(pose proof (req_size_pos olen ltac:(lia)); lia)).
Qed.


(* reac_decode (lib/B/Prog/reac_decode_cg.v): reads the copy and the mode's two fields and, when the geometry is
   good (even channel count), writes the 3 * nch * ns braided output bytes. Twin of dec_leafb_plain. The caller says where
   the mode's two fields are (a live block of the call state, or the image's mode table: either way as the
   visibility, the shadow and the two values the walk's view shows). *)
Lemma dec_leafb_decode :
  dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx') ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         (o raw len mode out nch ns olen : Z) (bs : list byte),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 10 = w64 raw -> getr regsT 11 = w64 len ->
  getr regsT 12 = w64 mode -> getr regsT 13 = w64 out ->
  0 <= len < 2 ^ 64 -> -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  In (raw, len) (ablocks B lyc Sc) -> (len = 1492 -> length bs = 1492%nat) ->
  garr8 segs (mrestrict (w_H W) memT) raw (map (fun b : byte => bv_unsigned b) bs) ->
  In (out, olen) (ablocks B lyc Sc) -> out <> raw ->
  (* both guarded by decode_ok, as in dec_leafb_plain *)
  (CDec.decode_ok len bs nch ns = true -> 3 * nch * ns <= olen) ->
  (CDec.decode_ok len bs nch ns = true ->
     forall a, out <= a < out + 3 * nch * ns ->
       awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  in_app mode 12 -> mode mod 4 = 0 ->
  (* visibility, not presence: a table mode's bytes are image bytes the overlay need not hold *)
  (forall a, mode + 4 <= a < mode + 12 -> w_H W (Z_to_bv 64 a) = false) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF (mode + 4) 8 ->
  val_mem segs (mrestrict (w_H W) memT) (mode + 4) 4%nat (nch mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) memT) (mode + 8) 4%nat (ns mod 2 ^ 32) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 CDec.REAC_DECODE) memT (YK11.seg_rom segs)) mdc)
    (dec_leafb_ret STK sp0 FP ly S W0 mem md own lyc Sc W memT k regsT
       (if CDec.decode_ok len bs nch ns then ns else -1)
       (if CDec.decode_ok len bs nch ns then [(out, out + 3 * nch * ns)] else [])
       (fun m2 => CDec.decode_ok len bs nch ns = true ->
          garr8 segs (mrestrict (w_H W) m2) out
            (map (fun b : byte => bv_unsigned b) (CDec.braid_out bs nch ns)))).
Proof.
  intros HC HLEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw len mode out nch ns olen bs
    HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 H12 H13 Hlen Hnch Hns Hinr Hbs HG Hino Hne HolenG HawrG
    Hmapp Hm4 Hmpres Hmra Hmv1 Hmv2.
  pose proof (dec_leafb_frame_bounds B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o
    HJ Hsp Hneg Hbud) as (Hsp1 & Hsp2 & Hsp3 & Hsp4).
  pose proof (proj1 HJ) as HAR.
  assert (HspL : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
  assert (Hsp1L : alloc_ceiling + ESTACK <= bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) by exact Hsp1.
  assert (Hsp2L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) <= sp0) by exact Hsp2.
  pose proof alloc_ceiling_val as HCEIL.
  unfold ESTACK in Hsp1L, Hsp4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ raw len HAR Hinr) as (_ & Hr4096 & Hrceil & Hrapp & Hrpres & _ & Hrmr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hino) as (_ & Ho4096 & Hoceil & Hoapp & Hopres & _ & Homr).
  pose proof (req_size_pos len ltac:(lia)) as [Hqr1 Hqr2].
  pose proof (req_size_pos olen ltac:(lia)) as [Hqo1 Hqo2].
  pose proof (sep_blocks segs B LAWS lyc Sc W memT mdc out olen raw len HAR Hino Hinr
    ltac:(intros Hq; injection Hq as Hq1 _; exact (Hne Hq1))) as Hdisj.
  unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
  assert (Hmlo : 4096 <= mode) by (destruct Hmapp as [Hx _]; lia).
  assert (Hmhi : mode + 12 <= alloc_ceiling)
    by (destruct Hmapp as [_ [Hx | [Hx Hy]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
  assert (Ha1L : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = len).
  { assert (Hx : bv_unsigned (getr regsT 11) = len)
      by (rewrite H11; unfold w64; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); apply Z.mod_small; lia).
    exact Hx. }
  assert (Ha0L : YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 raw) by exact H10.
  assert (Ha2L : YK11.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 mode) by exact H12.
  assert (Ha3L : YK11.getr regsT (Z_to_bv 5 13) = Z_to_bv 64 out) by exact H13.
  (* decode_ok says the geometry is positive and the copy is the 1492-byte frame *)
  assert (HokF : forall (l : Z), CDec.decode_ok l bs nch ns = true -> l = 1492 /\ 0 < nch /\ 0 < ns).
  { intros l Hok. unfold CDec.decode_ok in Hok.
    apply andb_true_iff in Hok as [Hok Hprod]. apply andb_true_iff in Hok as [Hok Hns0].
    apply andb_true_iff in Hok as [Hok Hev]. apply andb_true_iff in Hok as [Hwf Hnch0].
    unfold CInsp.inspect_wf in Hwf. apply andb_true_iff in Hwf as [Hwf _].
    apply andb_true_iff in Hwf as [Hwf _]. apply andb_true_iff in Hwf as [Hwf _].
    apply andb_true_iff in Hwf as [Hl _]. apply Z.eqb_eq in Hl.
    apply Z.ltb_lt in Hnch0. apply Z.ltb_lt in Hns0. auto. }
  assert (Hmode8 : LMem.bytes_at segs memT (mode + 4) (LMem.le4 (Z_to_bv 64 nch) ++ LMem.le4 (Z_to_bv 64 ns))).
  { apply dec_leafb_bytes_app.
    - unfold LMem.le4. apply (dec_leafb_bytes_le W memT (mode + 4) 4%nat _ (nch mod 2 ^ 32) Hmv1);
        [ rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); change (8 * Z.of_nat 4) with 32;
          rewrite (Z.mod_mod nch (2 ^ 32)) by lia;
          apply (dec_leafb_mod_pow2_mod nch 32 64); lia
        | lia | change (Z.of_nat 4) with 4; lia ].
    - unfold LMem.le4. rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
      replace (mode + 4 + 4) with (mode + 8) by lia.
      apply (dec_leafb_bytes_le W memT (mode + 8) 4%nat _ (ns mod 2 ^ 32) Hmv2);
        [ rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
          change (2 ^ Z.of_N 64) with (2 ^ 64); change (8 * Z.of_nat 4) with 32;
          rewrite (Z.mod_mod ns (2 ^ 32)) by lia;
          apply (dec_leafb_mod_pow2_mod ns 32 64); lia
        | lia | change (Z.of_nat 4) with 4; lia ]. }
  assert (HoutLen : length (CDec.braid_out bs nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CDec.braid_out; rewrite !length_map, length_seq; reflexivity).
  eapply SRr_mono;
    [ eapply (dec_leafb_journal B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o
                CDec.REAC_DECODE (Some (if CDec.decode_ok len bs nch ns then ns else -1))
                (if CDec.decode_ok len bs nch ns then [(out, out + 3 * nch * ns)] else [])
                (fun m2 => CDec.decode_ok len bs nch ns = true ->
                   LMem.bytes_at segs m2 out (CDec.braid_out bs nch ns))
                HJ Hsp Hal Hneg Hbud Hra Hgp Htp)
    | cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HJ2 & Hp2 & Hres2 & Heff2 & Hgr2 & HX2);
      split; [reflexivity|]; exists regs2, mem2, md2;
      split; [exact Hc2|]; split; [exact HJ2|]; split; [exact Hp2|];
      split; [exact (Hres2 _ eq_refl)|]; split; [exact Heff2|]; split; [exact Hgr2|];
      intros Hok; destruct (HokF len Hok) as (Hl & Hn0 & Hs0); pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen;
      apply (dec_leafb_garr8_of_bytes W mem2 out _ (HX2 Hok));
      intros i Hi; rewrite HoutLen in Hi; apply Hgr2; exact (proj1 (Hopres (out + i) ltac:(nia))) ].
  - (* the written range is one the caller's journal lets the callee write *)
    intros a Ha. destruct (CDec.decode_ok len bs nch ns) eqn:Hok; [|inversion Ha].
    apply (HawrG ltac:(first [exact Hok | reflexivity])). inversion Ha as [r l Hr Hl | r l Hr Hl]; subst; cbn [fst snd] in *; [lia | inversion Hr].
  - intros HPRE. rewrite <- Ha1L.
    refine (HLEAF fx lyc Sc W regsT memT mdc bs raw mode out nch ns (sp0 - STK) HPRE
              Ha0L Ha2L Ha3L _ _ _ _ _ _ Hmode8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + lia.
    + lia.
    + lia.
    + intros Hl. rewrite Ha1L in Hl. split; [exact (Hbs Hl)|].
      apply (dec_leafb_bytes_garr8 W memT raw bs HG); [lia | rewrite (Hbs Hl); lia].
    + lia.
    + lia.
    + exact (dec_leafb_stk_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k (sp0 - STK)
               (spZ regsT) HJ ltac:(lia) ltac:(lia)).
    + unfold CDec.REAC_DECODE_D. lia.
    + intros Hl. rewrite Ha1L in Hl.
      unfold BKA.off_stk, CDec.REAC_DECODE_D. left. lia.
    + unfold BKA.off_stk, CDec.REAC_DECODE_D. left. lia.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      split; [exact (dec_leafb_wr_at_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
                       HAR Hino ltac:(lia) ltac:(nia))|].
      split; [nia|].
      split; [subst len; nia|].
      unfold BKA.off_stk, CDec.REAC_DECODE_D. left. nia.
    + apply dec_leafb_app_stack; unfold CDec.REAC_DECODE_D; lia.
    + apply dec_leafb_app_stack; lia.
    + exact (dec_leafb_asan_cells B HC lyc Sc W memT mdc HAR).
    + unfold BKA.off_stk, CDec.REAC_DECODE_D, BCells.GOT_CELL_K, BCells.MIDEND. left. lia.
    + intros Hl. rewrite Ha1L in Hl.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr
               ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros _. apply (dec_leafb_addressable W memT (mode + 4) 8 Hmra); [lia | lia | |].
      * unfold BCells.APPMEM_END. unfold kHighMemEnd in *. lia.
      * intros i Hi. replace (mode + 4 + i) with (mode + (4 + i)) by lia.
        apply (@dec_leafb_app_of_in_app rc mode 12); [exact Hmapp | lia].
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      exact (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
               HAR Hino ltac:(lia) ltac:(nia) ltac:(nia)).
    + intros Hl. lia.
    + intros _. split; lia.
    + intros Hok. lia.
    + apply (dec_leafb_rng_journal B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k);
        [exact HJ | unfold CDec.REAC_DECODE_D; lia | unfold CDec.REAC_DECODE_D; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hl. rewrite Ha1L in Hl.
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr ltac:(lia) ltac:(lia))|].
      pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc raw len raw 1492 HAR Hinr
        ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace (raw + 1492 - 1) with (raw + 1491) in HS by lia.
      replace ((raw + 1491) / 8 + 2147450880 - (raw / 8 + 2147450880) + 1)
        with ((raw + 1491) / 8 - raw / 8 + 1) in HS by lia.
      exact HS.
    + intros _.
      split; [apply (dec_leafb_rng W); [lia | lia | intros a Ha; apply Hmpres; lia]|].
      pose proof (dec_leafb_rng_shadow W memT (mode + 4) 8 Hmra ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace (mode + 4 + 8 - 1) with (mode + 11) in HS by lia.
      replace ((mode + 11) / 8 + 2147450880 - ((mode + 4) / 8 + 2147450880) + 1)
        with ((mode + 11) / 8 - (mode + 4) / 8 + 1) in HS by lia.
      exact HS.
    + intros Hok. rewrite Ha1L in Hok. destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      split; [exact (dec_leafb_rng_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
                       HAR Hino ltac:(lia) ltac:(nia))|].
      pose proof (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc out olen out (3 * nch * ns)
        HAR Hino ltac:(lia) ltac:(nia) ltac:(nia)) as HS.
      unfold BCells.shadow_addr, BCells.ASAN_K in HS |- *.
      replace ((out + 3 * nch * ns - 1) / 8 + 2147450880 - (out / 8 + 2147450880) + 1)
        with ((out + 3 * nch * ns - 1) / 8 - out / 8 + 1) in HS by lia.
      exact HS.
    + intros x Hx. rewrite Ha1L in Hx.
      destruct (CDec.decode_ok len bs nch ns) eqn:Hok; [|inversion Hx].
      destruct (HokF len Hok) as (Hl & Hn0 & Hs0). pose proof (HolenG ltac:(first [exact Hok | reflexivity])) as Holen.
      assert (Hxr : out <= x < out + 3 * nch * ns)
        by (inversion Hx as [r l Hr Hl2 | r l Hr Hl2]; subst; cbn [fst snd] in *; [lia | inversion Hr]).
      exact (dec_leafb_wr_block B LAWS lyc Sc W memT mdc out olen HAR Hino x ltac:(nia)).
Qed.
End Leaves.
