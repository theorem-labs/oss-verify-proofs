(* crtA_cells: the runtime cells of lib/A/AsanCells.v from cgif's allocator invariant, for the cgif-form walk of
   check_round_trip (lib/A/Prog/check_round_trip_cg.v).
   dec_crt_cells (check_round_trip_cg.v:109-127) puts the 17 cells of asan_cells (AsanCells.v:55-65) in the constant
   cells of the asyms record B. AR (lib/Reusable/YG0n.v:490) gives ARm, whose am_const (YG0n.v:211) says every
   constant cell holds under the reader aview (YG0n.v:18). Every cell lies in one loaded segment of decodesegs0
   (dec_asan_cells_in_seg, check_round_trip_cg.v:74), where the world hides no byte (H_off_segments,
   lib/Reusable/YK04.v:38), so there aview reads the byte that mrd (lib/Lib/Mem.v:52) reads. The byte values of
   cell_holds (le_byte, lib/Reusable/YG0f.v:260-266) are the bytes of le8 / le4 / [Z_to_bv 8 _] (Mem.v:389-390). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0n YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Img0 AsanCells.
Import ListNotations.
Open Scope Z_scope.
Module LMem := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Mem.
Module AImg0 := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Img0.

(* ---- the bytes: le_byte against le8 / le4 / [Z_to_bv 8 _] ---- *)

Lemma crt_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma crt_mod_pow2_mod : forall v n m, 0 <= n <= m -> (v mod 2 ^ m) mod 2 ^ n = v mod 2 ^ n.
Proof.
  intros v n m Hnm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i n) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* Byte k of z is byte k of z mod 2^n when the byte lies below bit n. *)
Lemma crt_byte_mod : forall z n k, 0 <= k -> k + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) k mod 256 = Z.shiftr z k mod 256.
Proof.
  intros z n k Hk Hn. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb_spec0 i 8) as [Hl | Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma crt_le_byte : forall (w k : nat) z v, (k < w)%nat ->
  z mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (Z_to_le_bytes w z) k) = Some (le_byte v w k).
Proof.
  intros w k z v Hk Hm. rewrite crt_nth_le_bytes by exact Hk. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold le_byte. rewrite <- Hm. symmetry. apply crt_byte_mod; lia.
Qed.

Lemma crt_wa_mod : forall v (w : nat), (w <= 8)%nat ->
  bv_unsigned (LMem.wa v) mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
  intros v w Hw. unfold LMem.wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply crt_mod_pow2_mod. change (Z.of_N 64) with 64. lia.
Qed.

(* Width 8: the bytes of le8 (wa v), as asan_cells writes the word cells. *)
Lemma crt_le8_byte : forall v k, (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le8 (LMem.wa v)) k) = Some (le_byte v 8 k).
Proof.
  intros v k Hk. unfold LMem.le8, word_to_le_bytes.
  apply crt_le_byte; [exact Hk | apply crt_wa_mod; lia].
Qed.

(* Width 4: the bytes of le4 (wa v) (the UAR cell). *)
Lemma crt_le4_byte : forall v k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le4 (LMem.wa v)) k) = Some (le_byte v 4 k).
Proof.
  intros v k Hk. unfold LMem.le4.
  apply crt_le_byte; [exact Hk | apply crt_wa_mod; lia].
Qed.

(* Width 1: the byte [Z_to_bv 8 v] (the INITED / REPLACE / CANPOISON cells). *)
Lemma crt_le1_byte : forall v k, (k < 1)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error [Z_to_bv 8 v] k) = Some (le_byte v 1 k).
Proof.
  intros v k Hk. change [Z_to_bv 8 v] with (Z_to_le_bytes 1 v).
  apply crt_le_byte; [exact Hk | reflexivity].
Qed.

Lemma crt_opt_byte_eq : forall (x y : option byte) z,
  option_map (fun b : byte => bv_unsigned b) x = Some z ->
  option_map (fun b : byte => bv_unsigned b) y = Some z -> x = y.
Proof.
  intros [x|] [y|] z Hx Hy; cbn in Hx, Hy; try discriminate.
  injection Hx as Hx. injection Hy as Hy. f_equal. apply bv_eq. congruence.
Qed.

(* ---- the addresses: a cell inside a loaded segment is not hidden ---- *)

Lemma crt_find_none : forall (l : list Segment) addr n s,
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

Lemma crt_covers_lo : forall a n, dec_seg_covers a n = true -> 0 <= a.
Proof.
  intros a n Hc. unfold dec_seg_covers in Hc. apply existsb_exists in Hc as (s & _ & Hb). cbv beta in Hb.
  apply andb_true_iff in Hb as [H1 _]. apply Z.leb_le in H1.
  pose proof (N2Z.is_nonneg (seg_base s)). lia.
Qed.

Lemma crt_covers_visible : forall (hd : word -> bool) a n i,
  H_off_segments decodesegs0 hd -> dec_seg_covers a n = true -> 0 <= i < n -> a + n <= 2 ^ 64 ->
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
  exact (crt_find_none decodesegs0 (a + i) 1 s E2 Hs ltac:(lia) ltac:(lia)).
Qed.

Lemma crt_seg_of : forall a n, In (a, n) dec_asan_cell_ranges -> dec_seg_covers a n = true.
Proof. intros a n Hin. exact (proj1 (forallb_forall _ _) dec_asan_cells_in_seg (a, n) Hin). Qed.

Ltac crt_seg := clear; apply crt_seg_of; unfold dec_asan_cell_ranges; cbn [In];
  repeat (first [left; reflexivity | right]).
Ltac crt_top := clear; apply Z.leb_le; reflexivity.

Section CrtCells.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* One constant cell at a numeral address, in a loaded segment: its bytes are bytes_at under mrd. *)
Lemma crt_cell_bytes : forall ly (hd : word -> bool) mem a v (w : nat) (bs : list byte),
  H_off_segments decodesegs0 hd ->
  cell_holds B ly (aview decodesegs0 hd mem) (ACell (ANum a) w (AV (ANum v))) ->
  dec_seg_covers a (Z.of_nat w) = true -> a + Z.of_nat w <= 2 ^ 64 ->
  length bs = w ->
  (forall k, (k < w)%nat -> option_map (fun b : byte => bv_unsigned b) (nth_error bs k) = Some (le_byte v w k)) ->
  LMem.bytes_at AImg0.rsegs mem a bs.
Proof.
  intros ly hd mem a v w bs Hoff Hc Hcov Htop Hlen Henc.
  unfold cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  unfold LMem.bytes_at.
  split; [exact (crt_covers_lo a (Z.of_nat w) Hcov)|].
  split; [rewrite Hlen; exact Htop|].
  intros i Hi. rewrite Hlen in Hi.
  assert (Hv : hd (Z_to_bv 64 (a + Z.of_nat i)) = false)
    by (apply (crt_covers_visible hd a (Z.of_nat w) (Z.of_nat i) Hoff Hcov); lia).
  assert (Erd : LMem.mrd AImg0.rsegs mem (LMem.wa (a + Z.of_nat i)) =
                mbyte decodesegs0 (mrestrict hd mem) (a + Z.of_nat i)).
  { unfold LMem.mrd, LMem.wa, mbyte, mrestrict. rewrite Hv. reflexivity. }
  rewrite Erd. apply (crt_opt_byte_eq _ _ (le_byte v w i)); [exact (Hc i Hi) | exact (Henc i Hi)].
Qed.

Lemma crt_z8 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegs0 hd ->
  Forall (cell_holds B ly (aview decodesegs0 hd mem)) (as_const B ly) ->
  In (z8 (ANum a) v) (as_const B ly) -> dec_seg_covers a 8 = true -> a + 8 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le8 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (crt_cell_bytes ly hd mem a v 8 (LMem.le8 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le8 _) (crt_le8_byte v)).
Qed.

Lemma crt_z4 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegs0 hd ->
  Forall (cell_holds B ly (aview decodesegs0 hd mem)) (as_const B ly) ->
  In (z4 (ANum a) v) (as_const B ly) -> dec_seg_covers a 4 = true -> a + 4 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a (LMem.le4 (LMem.wa v)).
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (crt_cell_bytes ly hd mem a v 4 (LMem.le4 (LMem.wa v)) Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           (LMem.length_le4 _) (crt_le4_byte v)).
Qed.

Lemma crt_z1 : forall ly (hd : word -> bool) mem a v,
  H_off_segments decodesegs0 hd ->
  Forall (cell_holds B ly (aview decodesegs0 hd mem)) (as_const B ly) ->
  In (z1 (ANum a) v) (as_const B ly) -> dec_seg_covers a 1 = true -> a + 1 <= 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs mem a [Z_to_bv 8 v].
Proof.
  intros ly hd mem a v Hoff HK Hin Hc Ht.
  exact (crt_cell_bytes ly hd mem a v 1 [Z_to_bv 8 v] Hoff (proj1 (Forall_forall _ _) HK _ Hin) Hc Ht
           eq_refl (crt_le1_byte v)).
Qed.

Lemma dec_cells_asan :
  dec_crt_cells B ->
  forall (ly : alayout) (S : astate) (W : world decodesegs0) (mem : word -> option byte) (md : Model),
    H_off_segments decodesegs0 (w_H W) ->
    @AR rc decodesegs0 B ly S W mem md ->
    AsanCells.asan_cells mem.
Proof.
  intros HC ly S W mem md Hoff HAR.
  destruct HAR as [HM _].
  assert (HK : Forall (cell_holds B ly (aview decodesegs0 (w_H W) mem)) (as_const B ly))
    by (eapply am_const; exact HM).
  (* The first seventeen rows of dec_crt_cells are the runtime cells AsanCells.asan_cells reads; the rows after
     them (the .got pointer words, the table words and their shadow granules, the divide-by-36 word: statement
     774ffa170e8) are for other program walks, and this lemma does not need them. *)
  destruct (HC ly) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & _).
  unfold AsanCells.asan_cells.
  split; [exact (crt_z8 ly _ mem AsanCells.CELL_K AsanCells.ASAN_K Hoff HK C1 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_CELL_K AsanCells.CELL_K Hoff HK C2 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z1 ly _ mem AsanCells.INITED 1 Hoff HK C3 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z1 ly _ mem AsanCells.REPLACE 1 Hoff HK C4 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_REPLACE AsanCells.REPLACE Hoff HK C5 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z4 ly _ mem AsanCells.UAR 1 Hoff HK C6 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_UAR AsanCells.UAR Hoff HK C7 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z1 ly _ mem AsanCells.CANPOISON 1 Hoff HK C8 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.HIEND 0x7fffffffffff Hoff HK C9 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_HIEND AsanCells.HIEND Hoff HK C10 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.MIDBEG 0 Hoff HK C11 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_MIDBEG AsanCells.MIDBEG Hoff HK C12 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.MIDEND 0 Hoff HK C13 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.GOT_MIDEND AsanCells.MIDEND Hoff HK C14 ltac:(crt_seg) ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.REAL_MEMCPY AsanCells.MUSL_MEMCPY Hoff HK C15 ltac:(crt_seg)
                   ltac:(crt_top))|].
  split; [exact (crt_z8 ly _ mem AsanCells.REAL_MEMSET AsanCells.MUSL_MEMSET Hoff HK C16 ltac:(crt_seg)
                   ltac:(crt_top))|].
  exact (crt_z8 ly _ mem AsanCells.GOT_REAL_MEMSET AsanCells.REAL_MEMSET Hoff HK C17 ltac:(crt_seg) ltac:(crt_top)).
Qed.
End CrtCells.
