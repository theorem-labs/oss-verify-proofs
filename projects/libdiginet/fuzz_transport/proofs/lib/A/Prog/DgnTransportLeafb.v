(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1q.v (tfib_srealizesX),
   lib/A/AB1n.v (tfib_startup_T1, HS_ok) and lib/A/AD2o.v (TFIB_T_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v, a working branch 86b0e893fe8), for libreac/fuzz_decode's
   ASan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeClose.v, with its module paths and module names changed; 1425 of its 1489 lines of code are new or changed and 431 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v, with its module paths and module names changed; 172 of its 533 lines of code are new or changed and 1128 lines of the source are left out. *)
(* DgnDecodeLeafb: the shared leaf-call bridge of the image-A walks of libdiginet/fuzz_decode.
   A program leaf of this unit is stated in lib/A/Prog/<leaf>_cg.v over the kit lib/A/Prog/LeafCgKit.v: its premises
   are footprint facts about the RAW call memory (Frame.stk, Mem.bytes_at, AsanCells.addressable / asan_cells,
   ExecF.rng over RNG_W W) and its post is LeafCgKit.dleaf_post. A walk runs in cgif's caller-journal form
   (lib/Reusable/YCbq.v ajournal, the VIEW aview of the world's visible bytes). This file turns one into the other,
   for every leaf alike; no lemma here names a leaf.
   (a) decode_leafb_journal: a leaf's dleaf_post at the call becomes the caller's journal at the return, through
       YCbq.v ajournal_after_write with the written set = the leaf's stack window [sp - ESTACK, sp) and its WR.
   (b) Frame.stk / ExecF.rng (RNG_W W): decode_leafb_stk, decode_leafb_stk_journal, decode_leafb_rng,
       decode_leafb_rng_journal, decode_leafb_rng_block, decode_leafb_rng_shadow, decode_leafb_rng_cells.
   (c) the raw byte facts: decode_leafb_mrd (a visible byte's raw read is its view), decode_leafb_bytes_garr8,
       decode_leafb_bytes_le, decode_leafb_rom_bytes, decode_leafb_addressable, decode_leafb_addressable_block,
       decode_leafb_wr_at, decode_leafb_wr_block, the app_mem / off_stk arithmetic.
   (d) decode_leafb_asan_cells: asan_cells from decode_cells B (DgnDecodeCg.v) and AR's am_const. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05 YK04 YA0n YP09 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0f YG0n YG0d YCbq YG0v YI04 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit AsanKA DgnTransportImg.
Import ListNotations.
Open Scope Z_scope.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Module LExecF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Module AImg0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Local Notation transportsegs0 := DgnTransportImg.transportsegs0.

(* ------------------------------------------------------------------ *)
(* (d) the runtime cells (see the header)                              *)
(* ------------------------------------------------------------------ *)

Lemma decode_leafb_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma decode_leafb_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma decode_leafb_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma decode_leafb_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite decode_leafb_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply decode_leafb_byte_mod; lia.
Qed.

Lemma decode_leafb_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (LMem.wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold LMem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply decode_leafb_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

Lemma decode_leafb_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le8 (LMem.wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold LMem.le8, word_to_le_bytes.
  apply decode_leafb_le_byte; [exact Hk | apply decode_leafb_wa_mod; lia].
Qed.

Lemma decode_leafb_le4_byte : forall v k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le4 (LMem.wa v)) k) = Some (le_byte v 4 k).
Proof.
  intros v k Hk. unfold LMem.le4.
  apply decode_leafb_le_byte; [exact Hk | apply decode_leafb_wa_mod; lia].
Qed.

Lemma decode_leafb_le1_byte : forall v k, (k < 1)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error [Z_to_bv 8 v] k) = Some (le_byte v 1 k).
Proof.
  intros v k Hk. change [Z_to_bv 8 v] with (Z_to_le_bytes 1 v).
  apply decode_leafb_le_byte; [exact Hk | reflexivity].
Qed.

Lemma decode_leafb_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

Lemma decode_leafb_find_none : forall (l : list Segment) addr n s,
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

Lemma decode_leafb_covers_lo : forall a n, decode_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma decode_leafb_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments transportsegs0 hd -> decode_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
  hd (Z_to_bv 64 (a + i)) = false.
Proof.
  intros hd a n i Hoff Hc Hi Ht.
  unfold decode_seg_covers in Hc. apply existsb_exists in Hc as (s & Hs & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (N2Z.is_nonneg (seg_base s)) as H0.
  destruct (hd (Z_to_bv 64 (a + i))) eqn:E; [exfalso | reflexivity].
  pose proof (Hoff _ E) as E2.
  assert (U : bv_unsigned (Z_to_bv 64 (a + i)) = a + i) by (apply (LMem.wa_unsigned (a + i)); lia).
  rewrite U in E2.
  exact (decode_leafb_find_none transportsegs0 (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma decode_leafb_seg_of : forall a n, In (a, n) decode_asan_cell_ranges -> decode_seg_covers a n = true.
Proof. intros a n Hin. exact (proj1 (forallb_forall _ _) decode_asan_cells_in_seg (a, n) Hin). Qed.

Ltac decode_leafb_seg := clear; apply decode_leafb_seg_of; unfold decode_asan_cell_ranges; cbn [In];
  repeat (first [left; reflexivity | right]).
Ltac decode_leafb_top := clear; apply Z.leb_le; reflexivity.
(* One row of decode_cells, found by its statement (no positional destruct: rows may be added). *)
Ltac decode_leafb_row HC ly := let H := fresh "Hrow" in pose proof (HC ly) as H;
  repeat match type of H with _ /\ _ => let A := fresh "Hrow" in destruct H as [A H] end; assumption.

Section Cells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma decode_leafb_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments transportsegs0 hd ->
  cell_holds B ly (aview transportsegs0 hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  decode_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  LMem.bytes_at AImg0.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold LMem.bytes_at.
  split; [exact (decode_leafb_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (decode_leafb_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : LMem.mrd AImg0.rsegs mem (LMem.wa (a + Z.of_nat i)) =
                mbyte transportsegs0 (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (decode_leafb_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma decode_leafb_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments transportsegs0 hd ->
  Forall (cell_holds B ly (aview transportsegs0 hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> decode_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le8 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_leafb_cell_bytes ly hd mem a v 8 (LMem.le8 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le8 _) (decode_leafb_le8_byte v)).
Qed.

Lemma decode_leafb_z4 : forall ly (hd : word -> bool) mem a v,
  H_off_segments transportsegs0 hd ->
  Forall (cell_holds B ly (aview transportsegs0 hd mem)) (as_const B ly) ->
  In (z4 (ANum a) v) (as_const B ly) -> decode_seg_covers a 4 = true -> a + 4 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le4 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_leafb_cell_bytes ly hd mem a v 4 (LMem.le4 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le4 _) (decode_leafb_le4_byte v)).
Qed.

Lemma decode_leafb_z1 : forall ly (hd : word -> bool) mem a v,
  H_off_segments transportsegs0 hd ->
  Forall (cell_holds B ly (aview transportsegs0 hd mem)) (as_const B ly) ->
  In (z1 (ANum a) v) (as_const B ly) -> decode_seg_covers a 1 = true -> a + 1 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a [Z_to_bv 8 v].
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (decode_leafb_cell_bytes ly hd mem a v 1 [Z_to_bv 8 v] Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           eq_refl (decode_leafb_le1_byte v)).
Qed.

(* asan_cells at the world's own hidden set (its w_Hoff field), from rows 1-17 of decode_cells. *)
Lemma decode_leafb_asan_cells :
  transport_cells B ->
  forall (ly : alayout) (S : astate) (W : world transportsegs0) (mem : word -> option byte) (md : Model),
    @AR rc transportsegs0 B ly S W mem md ->
    ACells.asan_cells mem.
Proof.
  intros HC ly S W mem md HAR.
  pose proof (w_Hoff W) as Hoff.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview transportsegs0 (w_H W) mem)) (as_const B ly))
    by (eapply am_const; exact HM).
  unfold ACells.asan_cells.
  split; [exact (decode_leafb_z8 ly _ mem ACells.CELL_K ACells.ASAN_K Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_CELL_K ACells.CELL_K Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z1 ly _ mem ACells.INITED 1 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z1 ly _ mem ACells.REPLACE 1 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_REPLACE ACells.REPLACE Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z4 ly _ mem ACells.UAR 1 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_UAR ACells.UAR Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z1 ly _ mem ACells.CANPOISON 1 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.HIEND 0x7fffffffffff Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_HIEND ACells.HIEND Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.MIDBEG 0 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_MIDBEG ACells.MIDBEG Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.MIDEND 0 Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.GOT_MIDEND ACells.MIDEND Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.REAL_MEMCPY ACells.MUSL_MEMCPY Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg)
                   ltac:(decode_leafb_top))|].
  split; [exact (decode_leafb_z8 ly _ mem ACells.REAL_MEMSET ACells.MUSL_MEMSET Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg)
                   ltac:(decode_leafb_top))|].
  exact (decode_leafb_z8 ly _ mem ACells.GOT_REAL_MEMSET ACells.REAL_MEMSET Hoff HK ltac:(decode_leafb_row HC ly) ltac:(decode_leafb_seg) ltac:(decode_leafb_top)).
Qed.
End Cells.

(* ------------------------------------------------------------------ *)
(* (c) raw bytes from the view                                         *)
(* ------------------------------------------------------------------ *)

Local Notation segs := transportsegs0.

(* A byte the view shows is not hidden: a hidden address lies outside every loaded segment (the world's w_Hoff),
   where the image reads nothing. *)
Lemma decode_leafb_mbyte_vis : forall (W : world segs) mem a b,
  mbyte segs (mrestrict (w_H W) mem) a = Some b -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a b H. destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
  unfold mbyte, mrestrict in H. rewrite Hh in H.
  pose proof (w_Hoff W _ Hh) as Hf.
  unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H. rewrite Hf in H. discriminate.
Qed.

Lemma decode_leafb_aview_vis : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b|] eqn:E; [|discriminate].
  exact (decode_leafb_mbyte_vis W mem a b E).
Qed.

(* A visible byte's raw read (Mem.mrd, what the footprint contracts read) is its view byte. *)
Lemma decode_leafb_mrd : forall (W : world segs) mem a,
  w_H W (Z_to_bv 64 a) = false -> LMem.mrd segs mem (LMem.wa a) = mbyte segs (mrestrict (w_H W) mem) a.
Proof. intros W mem a H. unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite H. reflexivity. Qed.

Lemma decode_leafb_mrd_aview : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v ->
  exists b : byte, LMem.mrd segs mem (LMem.wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (decode_leafb_aview_vis W mem a v H) as Hv.
  rewrite (decode_leafb_mrd W mem a Hv). unfold aview in H.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b|]; [|discriminate].
  cbn in H. injection H as <-. exists b. auto.
Qed.

Lemma decode_leafb_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The bytes of a garr8 array of the view are the raw bytes. *)
Lemma decode_leafb_bytes_garr8 : forall (W : world segs) mem p (bs : list byte),
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
  rewrite map_nth in Hv. rewrite decode_leafb_le_byte1 in Hv.
  rewrite (decode_leafb_mrd W mem (p + Z.of_nat i) (decode_leafb_mbyte_vis W mem _ _ Hv)), Hv.
  symmetry. apply nth_error_nth'. exact Hi.
Qed.

(* A w-byte value of the view, read as the little-endian bytes of any z congruent to it. *)
Lemma decode_leafb_bytes_le : forall (W : world segs) mem a (w : nat) z v,
  val_mem segs (mrestrict (w_H W) mem) a w v ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  LMem.bytes_at segs mem a (Z_to_le_bytes w z).
Proof.
  intros W mem a w z v HV Hm H0 Ht. split; [exact H0|].
  rewrite length_Z_to_le_bytes. split; [exact Ht|]. intros i Hi.
  specialize (HV i Hi).
  rewrite (decode_leafb_mrd W mem (a + Z.of_nat i) (decode_leafb_mbyte_vis W mem _ _ HV)), HV.
  rewrite decode_leafb_nth_le_bytes by exact Hi. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
  rewrite <- Hm. apply decode_leafb_byte_mod; lia.
Qed.

(* Read-only image bytes: under rom_view, the raw bytes of an in-rom range are the image's. *)
Lemma decode_leafb_rom_bytes : forall (W : world segs) mem a (bs : list byte),
  rom_view segs W mem ->
  (forall i, (i < length bs)%nat -> in_rom segs (a + Z.of_nat i)) ->
  (forall i, (i < length bs)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  LMem.bytes_at segs mem a bs.
Proof.
  intros W mem a bs HR Hin Himg H0 Ht. split; [exact H0|]. split; [exact Ht|]. intros i Hi.
  pose proof (HR _ (Hin i Hi)) as Hv. rewrite (Himg i Hi) in Hv.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi) in Hv |- *. cbn [option_map] in Hv.
  destruct (decode_leafb_mrd_aview W mem _ _ Hv) as (b & Hb & Hbv). rewrite Hb. f_equal. apply bv_eq. exact Hbv.
Qed.

Lemma decode_leafb_bv_signed8 : forall b : byte, 0 <= bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed, bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8 / 2) with 128. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

Section App. Context {rc : YM05.RunCeil}.
Lemma decode_leafb_app_of_in_app : forall lo len i, in_app lo len -> 0 <= i < len -> ACells.app_mem (lo + i).
Proof.
  intros lo len i [H0 H] Hi. pose proof (proj1 (@ASAN_CEIL_range rc)) as C. pose proof (proj2 (@ASAN_CEIL_range rc)) as C2.
  unfold ACells.app_mem, ACells.LOWMEM_END, ACells.HIGHMEM_BEG, ACells.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* Every stack byte (between alloc_ceiling and 2^47) is application memory. *)
Lemma decode_leafb_app_stack : forall a, alloc_ceiling <= a < 2 ^ 47 -> ACells.app_mem a.
Proof.
  intros a Ha. pose proof alloc_ceiling_val. unfold ACells.app_mem, ACells.HIGHMEM_BEG, ACells.APPMEM_END. lia.
Qed.
End App.

(* addressable (AsanCells) from range_addressable of the view. *)
Lemma decode_leafb_addressable : forall (W : world segs) mem p n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n ->
  0 <= p -> 0 <= n -> p + n <= ACells.APPMEM_END ->
  (forall i, 0 <= i < n -> ACells.app_mem (p + i)) ->
  ACells.addressable mem p n.
Proof.
  intros W mem p n HRA H0 Hn Ht Happ. split; [exact H0|]. split; [exact Hn|]. split; [exact Ht|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  unfold shadow_of_addr in Hs.
  assert (EA : ACells.shadow_addr (p + i) = SHADOW_OFF + (p + i) / 8)
    by (unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF; lia).
  rewrite EA. destruct (decode_leafb_mrd_aview W mem _ _ Hs) as (b & Hb & Hbv).
  exists b. split; [exact Hb|]. unfold ACells.shadow_ok, saddr_ok in *.
  rewrite decode_leafb_bv_signed8 by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* (b) Frame.stk and ExecF.rng (RNG_W W)                               *)
(* ------------------------------------------------------------------ *)

Lemma decode_leafb_stk : forall (W : world segs) mem lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
  LFrame.stk segs mem lo hi.
Proof.
  intros W mem lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a Ha) as [_ (b & Hb)]. unfold LMem.wa.
  split; [unfold wview; rewrite Hb; discriminate|]. exists b. unfold LMem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma decode_leafb_rng : forall (W : world segs) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> w_H W (Z_to_bv 64 a) = false) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros W lo len H0 H1 HV. split; [exact H0|]. split; [exact H1|].
  intros b j Hb Hj k Hk. unfold LCK.woff.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. apply HV. lia.
Qed.

(* The cells every leaf reads (GOT_CELL_K, CELL_K) lie in loaded segments, where nothing is hidden. *)
Lemma decode_leafb_rng_cells : forall (W : world segs),
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) ACells.GOT_CELL_K 8 /\
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) ACells.CELL_K 8.
Proof.
  intros W. split.
  - apply (decode_leafb_rng W); [unfold ACells.GOT_CELL_K; lia | unfold ACells.GOT_CELL_K; lia |].
    intros a Ha. replace a with (ACells.GOT_CELL_K + (a - ACells.GOT_CELL_K)) by lia.
    apply (decode_leafb_covers_visible (w_H W) ACells.GOT_CELL_K 8); [exact (w_Hoff W) | decode_leafb_seg | lia | decode_leafb_top].
  - apply (decode_leafb_rng W); [unfold ACells.CELL_K; lia | unfold ACells.CELL_K; lia |].
    intros a Ha. replace a with (ACells.CELL_K + (a - ACells.CELL_K)) by lia.
    apply (decode_leafb_covers_visible (w_H W) ACells.CELL_K 8); [exact (w_Hoff W) | decode_leafb_seg | lia | decode_leafb_top].
Qed.

Lemma decode_leafb_rng_vis : forall (W : world segs) mem lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> apresent (w_H W) mem a) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof. intros W mem lo len H0 H1 HP. apply decode_leafb_rng; [exact H0 | exact H1 |]. intros a Ha. exact (proj1 (HP a Ha)). Qed.

(* The shadow bytes of an addressable range are visible, so the leaf's footprint may read them. *)
Lemma decode_leafb_rng_shadow : forall (W : world segs) mem a n,
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n ->
  0 <= a -> 0 < n -> a + n <= 2 ^ 64 ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (ACells.shadow_addr a)
    (ACells.shadow_addr (a + n - 1) - ACells.shadow_addr a + 1).
Proof.
  intros W mem a n HRA H0 Hn Ht. unfold ACells.shadow_addr, ACells.ASAN_K in *.
  assert (D1 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (D2 : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D3 : 8 * ((a + n - 1) / 8) <= a + n - 1) by (apply Z.mul_div_le; lia).
  assert (D4 : (a + n - 1) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  apply decode_leafb_rng; [lia | lia |]. intros s Hs.
  set (q := s - 2147450880).
  assert (Hq : a / 8 <= q <= (a + n - 1) / 8) by (subst q; lia).
  destruct (Z.eq_dec q (a / 8)) as [Eq | Nq].
  - destruct (HRA a ltac:(lia)) as (v & Hv & _). unfold shadow_of_addr, SHADOW_OFF in Hv.
    replace s with (2147450880 + a / 8) by (subst q; lia). exact (decode_leafb_aview_vis W mem _ v Hv).
  - assert (Ha8 : a < 8 * q) by (pose proof (Z.mod_pos_bound a 8 ltac:(lia)); pose proof (Z.div_mod a 8 ltac:(lia)); lia).
    assert (Hq8 : 8 * q <= a + n - 1) by lia.
    destruct (HRA (8 * q) ltac:(lia)) as (v & Hv & _). unfold shadow_of_addr, SHADOW_OFF in Hv.
    rewrite Z.mul_comm, Z.div_mul in Hv by lia. replace s with (2147450880 + q) by (subst q; lia).
    exact (decode_leafb_aview_vis W mem _ v Hv).
Qed.

Lemma decode_leafb_wr_at : forall (W : world segs) mem a n,
  0 <= a -> a + n <= 2 ^ 64 -> (forall i, 0 <= i < n -> apresent (w_H W) mem (a + i)) ->
  LMem.wr_at segs mem a n.
Proof.
  intros W mem a n H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (HP i Hi) as [_ (b & Hb)]. unfold LMem.wa, wview. rewrite Hb. discriminate.
Qed.

Lemma decode_leafb_pairwise_dup : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) y,
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
Lemma decode_leafb_new_block : forall ly S (W : world segs) mem md bl0 rest b n,
  @AR rc segs B ly S W mem md -> ablocks B ly S = bl0 ++ rest -> In (b, n) rest -> ~ In (b, n) bl0.
Proof.
  intros ly S W mem md bl0 rest b n HAR Hbl Hin Hin0.
  assert (Hb : In (b, n) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & _ & _ & _ & Hpw & Hn).
  rewrite Hbl, map_app in Hpw.
  pose proof (decode_leafb_pairwise_dup _ _ _ (b, req_size n) Hpw
    (in_map (fun x => (fst x, req_size (snd x))) _ _ Hin0) (in_map (fun x => (fst x, req_size (snd x))) _ _ Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. revert Hd. unfold req_size. destruct (Z.eqb_spec n 0); intros Hd; lia.
Qed.

(* A byte of such a new block is one the caller's journal lets a callee write (awr_byte's temporary-block case). *)
Lemma decode_leafb_awr_new : forall STK sp0 FP ly S lyc Sc (W : world segs) memc mdc own rest b n a,
  @AR rc segs B lyc Sc W memc mdc -> ablocks B lyc Sc = ablocks B ly S ++ rest -> In (b, n) rest ->
  b <= a < b + req_size n ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a.
Proof.
  intros STK sp0 FP ly S lyc Sc W memc mdc own rest b n a HAR Hbl Hin Ha.
  right. right. left. exists b, n. split; [rewrite Hbl; apply in_or_app; right; exact Hin|].
  split; [exact (decode_leafb_new_block _ _ _ _ _ _ _ b n HAR Hbl Hin) | exact Ha].
Qed.

Lemma decode_leafb_rng_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & Hpres & _).
  pose proof alloc_ceiling_val.
  apply (decode_leafb_rng_vis W mem); [lia | lia |]. intros x Hx. exact (proj1 (Hpres x ltac:(lia))).
Qed.

Lemma decode_leafb_addressable_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> 0 <= n -> a + n <= p + req_size m ->
  ACells.addressable mem a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 Hn H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  pose proof alloc_ceiling_val.
  apply (decode_leafb_addressable W mem).
  - eapply (range_addressable_of_block segs B LAWS); eassumption.
  - lia.
  - exact Hn.
  - unfold ACells.APPMEM_END. lia.
  - intros i Hi. replace (a + i) with (p + (a - p + i)) by lia.
    apply (@decode_leafb_app_of_in_app rc p (req_size m)); [exact Happ | lia].
Qed.

Lemma decode_leafb_rng_shadow_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> 0 < n -> a + n <= p + req_size m ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (ACells.shadow_addr a)
    (ACells.shadow_addr (a + n - 1) - ACells.shadow_addr a + 1).
Proof.
  intros ly S W mem md p m a n HAR Hin H1 Hn H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _).
  pose proof alloc_ceiling_val.
  apply (decode_leafb_rng_shadow W mem); [eapply (range_addressable_of_block segs B LAWS); eassumption | lia | lia | lia].
Qed.

Lemma decode_leafb_wr_block : forall ly S (W : world segs) mem md p m,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
  forall x, p <= x < p + req_size m -> ~ aowned B ly S x /\ ~ LCK.in_img x.
Proof.
  intros ly S W mem md p m HAR Hin x Hx.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  split; [exact (proj2 (Hpres x Hx))|].
  exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HAR (or_introl (ex_intro _ p (ex_intro _ m (conj Hin Hx)))))).
Qed.

Lemma decode_leafb_wr_at_block : forall ly S (W : world segs) mem md p m a n,
  @AR rc segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
  LMem.wr_at segs mem a n.
Proof.
  intros ly S W mem md p m a n HAR Hin H1 H2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & H4096 & Hc & _ & Hpres & _).
  pose proof alloc_ceiling_val.
  apply (decode_leafb_wr_at W mem); [lia | lia |]. intros i Hi. exact (proj1 (Hpres (a + i) ltac:(lia))).
Qed.
End Blocks.

(* ------------------------------------------------------------------ *)
(* (a) a leaf's post at the call -> the caller's journal at the return *)
(* ------------------------------------------------------------------ *)

Section Journal. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
(* The leaf kit's call pre and leaf post (LeafCgKit.v:73, :86), at this unit's allocator model, as
   DgnDecodeCg.v decode_leaf_at instantiates them. *)
Definition decode_leafb_ecall_pre := @LCK.ecall_pre (world segs) (@w_H segs) alayout astate (@AR rc segs B)
  ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B).
Definition decode_leafb_post := @LCK.dleaf_post fx (world segs) (@w_H segs) alayout astate (@AR rc segs B)
  (aview segs) same_but_materialized.

Lemma decode_leafb_stk_journal : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo hi,
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> hi <= sp0 -> LFrame.stk segs memc lo hi.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo hi HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof alloc_ceiling_val.
  apply (decode_leafb_stk W memc); [lia | lia |]. intros a Ha. apply Hpres. lia.
Qed.

Lemma decode_leafb_rng_journal : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo len,
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= lo -> lo + len <= sp0 ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
  intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k lo len HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _). pose proof alloc_ceiling_val.
  apply (decode_leafb_rng_vis W memc); [lia | lia |]. intros a Ha. apply Hpres. lia.
Qed.

Lemma decode_leafb_journal : forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc
    mdc k (o PC : Z) (RES : option Z) (WR : list (Z * Z)) (X : (word -> option byte) -> Prop),
  @ajournal rc SK segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  (forall a, LCK.in_wr WR a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (decode_leafb_ecall_pre lyc Sc W regsT memT mdc ->
     SRr segs W (@LCK.cfg_at fx PC regsT memT mdc) (decode_leafb_post lyc Sc W regsT memT mdc RES WR X)) ->
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
  assert (HPRE : decode_leafb_ecall_pre lyc Sc W regsT memT mdc).
  { pose proof (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp Hal Hneg Hbud
      Hra Hgp Htp) as H.
    exact H. }
  eapply SRr_mono; [exact (HLEAF HPRE) |].
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hgr & HX).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split. { unfold LCK.cfg_at, LCK.w64, LCK.raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { eapply (ajournal_after_write segs B LAWS DgnTransportImg.transport_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k
      mem2 md2 (fun a => (spZ regsT - ESTACK <= a < spZ regsT) \/ LCK.in_wr WR a) Sc own HJ).
    - intros a Ha Hna. apply (Heff a Ha); intros H'; apply Hna; [left | right]; exact H'.
    - exact Hgr.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [left; unfold ESTACK in *; lia | exact (HWR a Ha)].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hgr | exact HX].
Qed.
End Journal.
