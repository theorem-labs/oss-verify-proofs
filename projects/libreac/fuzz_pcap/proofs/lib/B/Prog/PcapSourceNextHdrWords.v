(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: the byte and model
   arithmetic of the record-header phase, for lib/B/Prog/PcapSourceNextHdrB.v (a Theorem Labs lane), which Requires this
   file and keeps the walk. Nothing here reads the image: the statements name only the fread's view of the header
   (nx_hk / nx_hdr, lib/B/Prog/PcapSourceNextHdrBDefs.v), rd_u32's value (rd_u32_val, lib/B/Prog/RdU32.v), the byte
   array predicate garr8 (lib/Reusable/YI00.v) and Pau's model (lib/Prog/pcap_source_struct_next.v, PSN, through
   lib/A/Prog/PcapSourceNextSpec.v's nxF and nx_chain_inv).

   |C| below is HdrBDefs' Z.of_nat (length C).
   (a) hw_of_bytes: the four header bytes at byte offset j (0, 4, 8, 12), read as rd_u32 reads them with the stream's
       `swapped` field sw (0 or 1, the Z the code passes in a1), are the model's header word PSN.hw (sw =? 1) at j
       (the boolean nx_hdra_inv's chain clause uses). incl_range / orig_range: incl and orig are 32-bit.
   (b) hdr_bytes: the four bytes of word j (0 <= j < 4) of the header sit at A + 4 * j; j is a WORD index, as at the
       four rd_u32 calls (hb_call: a0 = ph + 4 * j, 0 <= j < 4). Its byte hypotheses are (a)'s at byte offset 4 * j,
       term for term, so the two compose without rewriting.
   (c) hdr_len: a full header (16 bytes left from q) is read whole. It needs 0 <= q: with q < 0 the fread view starts
       at byte 0 (Z.to_nat q = 0), and C = [0;0;0;0;0;0], q = -10 has 16 <= |C| - q but length (nx_hdr C q) = 6.
   (d) kind_*: the six kinds of PSN.kind at a full header (KEmpty, KFit, KCutFit, KBig0, KBig, KCutBig), each from
       PSN.kind's own tests, in its order: incl = 0, incl <= cap, cap = 0, q + 16 + incl <= flen (flen = |C|).
   (e) chain_empty_at: nx_chain_empty with its kind premise read off the header (incl = 0 at a full header).

   TAKEN FROM: (a) lib/A/Prog/PcapSourceNextHdrB.v nx_fb_hb / nx_hw_hb (a working branch 43308d15d0d,
   a Theorem Labs lane), restated over lib/B's nx_hdr and rd_u32_val; incl_range / orig_range: HdrBDefs' nx_hw_range (a Theorem Labs lane);
   (b) Reusable/YI01.v garr8_sub; (c) the same lib/A file's nx_hk_16 / nx_hdr_len16; (d) lib/B/Prog/
   PcapSourceNextHdrBDefs.v nx_kind_cases (a Theorem Labs lane) and lib/A/Prog/PcapSourceNextSpec.v nx_kind_empty; (e)
   PcapSourceNextSpec.v nx_chain_empty (a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextHdrBDefs.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* (c) A full header is read whole                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hdr_len : forall C q, 0 <= q -> 16 <= Z.of_nat (length C) - q ->
  nx_hk C q = 16 /\ length (nx_hdr C q) = 16%nat.
Proof.
  intros C q Hq H.
  assert (Hk : nx_hk C q = 16) by (unfold nx_hk, NX_PH_LEN; lia).
  split; [exact Hk|].
  unfold nx_hdr. rewrite Hk, length_firstn, length_skipn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (a) Four header bytes, read as rd_u32 reads them, are the model's header word                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* Every entry of a byte list is a byte (the default 0 past its end too). *)
Lemma hw_nth_byte : forall (l : list Z) (n : nat), bytes_ok l -> 0 <= nth n l 0 < 256.
Proof.
  intros l n H. destruct (Nat.lt_ge_cases n (length l)) as [Hl | Hl].
  - unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. exact Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

(* The model's byte q + i of the file is header byte i (0 <= i < 16) of a full header. *)
Lemma hw_fb_hdr : forall C q i, 0 <= q -> 16 <= Z.of_nat (length C) - q -> 0 <= i < 16 -> bytes_ok C ->
  PSN.fb (nxF C) (q + i) = nth (Z.to_nat i) (nx_hdr C q) 0.
Proof.
  intros C q i Hq H Hi Hok.
  assert (Hk : nx_hk C q = 16) by (unfold nx_hk, NX_PH_LEN; lia).
  unfold PSN.fb, nxF, bytesZ, nx_hdr. rewrite Hk.
  rewrite nth_firstn.
  replace (Z.to_nat i <? Z.to_nat 16)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn.
  change (Z_to_bv 8 0) with ((fun z : Z => Z_to_bv 8 z) 0). rewrite map_nth.
  replace (Z.to_nat (q + i)) with (Z.to_nat q + Z.to_nat i)%nat by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. apply hw_nth_byte. exact Hok.
Qed.

Lemma hw_of_bytes : forall (sw : Z) C q j b0 b1 b2 b3, (sw = 0 \/ sw = 1) -> 0 <= q ->
  16 <= Z.of_nat (length C) - q -> 0 <= j <= 12 -> j mod 4 = 0 ->
  nth (Z.to_nat (j + 0)) (nx_hdr C q) 0 = b0 -> nth (Z.to_nat (j + 1)) (nx_hdr C q) 0 = b1 ->
  nth (Z.to_nat (j + 2)) (nx_hdr C q) 0 = b2 -> nth (Z.to_nat (j + 3)) (nx_hdr C q) 0 = b3 ->
  bytes_ok C ->
  rd_u32_val sw b0 b1 b2 b3 = PSN.hw (sw =? 1) (nxF C) q j.
Proof.
  intros sw C q j b0 b1 b2 b3 Hsw Hq H Hj _ E0 E1 E2 E3 Hok. revert Hsw.
  assert (F0 : PSN.fb (nxF C) (q + j) = b0).
  { rewrite <- E0. replace (q + j) with (q + (j + 0)) by lia. apply hw_fb_hdr; [lia | lia | lia | exact Hok]. }
  assert (F1 : PSN.fb (nxF C) (q + j + 1) = b1).
  { rewrite <- E1. replace (q + j + 1) with (q + (j + 1)) by lia. apply hw_fb_hdr; [lia | lia | lia | exact Hok]. }
  assert (F2 : PSN.fb (nxF C) (q + j + 2) = b2).
  { rewrite <- E2. replace (q + j + 2) with (q + (j + 2)) by lia. apply hw_fb_hdr; [lia | lia | lia | exact Hok]. }
  assert (F3 : PSN.fb (nxF C) (q + j + 3) = b3).
  { rewrite <- E3. replace (q + j + 3) with (q + (j + 3)) by lia. apply hw_fb_hdr; [lia | lia | lia | exact Hok]. }
  unfold PSN.hw. rewrite F0, F1, F2, F3.
  intros [-> | ->]; unfold rd_u32_val, u32le, PSN.w32le; reflexivity.
Qed.

(* The model's header words are 32-bit: incl (bytes 8..11) and orig (bytes 12..15). *)
Lemma incl_range : forall sw F q, 0 <= PSN.incl sw F q < 2 ^ 32.
Proof. intros sw F q. unfold PSN.incl. apply nx_hw_range. Qed.

Lemma orig_range : forall sw F q, 0 <= PSN.orig sw F q < 2 ^ 32.
Proof. intros sw F q. unfold PSN.orig. apply nx_hw_range.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (b) Word j of the header in memory                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hdr_take4 : forall (l : list Z) (n : nat), (n + 4 <= length l)%nat ->
  firstn 4 (skipn n l) = [nth n l 0; nth (n + 1) l 0; nth (n + 2) l 0; nth (n + 3) l 0].
Proof.
  intros l n H. apply (nth_ext _ _ 0 0).
  - rewrite length_firstn, length_skipn. cbn [length]. lia.
  - intros i Hi. rewrite length_firstn, length_skipn in Hi.
    rewrite nth_firstn, nth_skipn.
    replace (i <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    destruct i as [|[|[|[|i]]]]; cbn [nth].
    + rewrite Nat.add_0_r. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exfalso. lia.
Qed.

Lemma hdr_bytes : forall segs m A C q j b0 b1 b2 b3,
  garr8 segs m A (nx_hdr C q) -> length (nx_hdr C q) = 16%nat -> 0 <= j < 4 ->
  nth (Z.to_nat (4 * j + 0)) (nx_hdr C q) 0 = b0 -> nth (Z.to_nat (4 * j + 1)) (nx_hdr C q) 0 = b1 ->
  nth (Z.to_nat (4 * j + 2)) (nx_hdr C q) 0 = b2 -> nth (Z.to_nat (4 * j + 3)) (nx_hdr C q) 0 = b3 ->
  garr8 segs m (A + 4 * j) [b0; b1; b2; b3].
Proof.
  intros segs m A C q j b0 b1 b2 b3 HG HL Hj E0 E1 E2 E3.
  pose proof (garr8_sub segs m A (nx_hdr C q) (Z.to_nat (4 * j)) 4 HG) as HS.
  assert (EL : firstn 4 (skipn (Z.to_nat (4 * j)) (nx_hdr C q)) = [b0; b1; b2; b3]).
  { rewrite hdr_take4 by lia. subst b0 b1 b2 b3.
    replace (Z.to_nat (4 * j + 0)) with (Z.to_nat (4 * j)) by lia.
    replace (Z.to_nat (4 * j + 1)) with (Z.to_nat (4 * j) + 1)%nat by lia.
    replace (Z.to_nat (4 * j + 2)) with (Z.to_nat (4 * j) + 2)%nat by lia.
    replace (Z.to_nat (4 * j + 3)) with (Z.to_nat (4 * j) + 3)%nat by lia.
    reflexivity. }
  rewrite EL, Z2Nat.id in HS by lia. exact HS.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (d) The kind of a full header, from PSN.kind's tests                                             *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma kind_flen : forall C, PSN.flen (nxF C) = Z.of_nat (length C).
Proof. intros C. unfold PSN.flen. rewrite nxF_length. reflexivity. Qed.

Lemma kind_empty_iff : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  (PSN.kind sw (nxF C) cap q = PSN.KEmpty <-> PSN.incl sw (nxF C) q = 0).
Proof.
  intros sw C cap q H. split.
  - intros Hk. exact (proj1 (nx_kind_empty sw (nxF C) cap q Hk)).
  - intros I. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
    destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

Lemma kind_fit : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  PSN.incl sw (nxF C) q <> 0 -> PSN.incl sw (nxF C) q <= cap ->
  q + 16 + PSN.incl sw (nxF C) q <= Z.of_nat (length C) ->
  PSN.kind sw (nxF C) cap q = PSN.KFit.
Proof.
  intros sw C cap q H I1 I2 I3. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
  destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

Lemma kind_cutfit : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  PSN.incl sw (nxF C) q <> 0 -> PSN.incl sw (nxF C) q <= cap ->
  Z.of_nat (length C) < q + 16 + PSN.incl sw (nxF C) q ->
  PSN.kind sw (nxF C) cap q = PSN.KCutFit.
Proof.
  intros sw C cap q H I1 I2 I3. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
  destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

Lemma kind_big0 : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  PSN.incl sw (nxF C) q <> 0 -> cap < PSN.incl sw (nxF C) q -> cap = 0 ->
  PSN.kind sw (nxF C) cap q = PSN.KBig0.
Proof.
  intros sw C cap q H I1 I2 I3. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
  destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

Lemma kind_big : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  PSN.incl sw (nxF C) q <> 0 -> cap < PSN.incl sw (nxF C) q -> cap <> 0 ->
  q + 16 + PSN.incl sw (nxF C) q <= Z.of_nat (length C) ->
  PSN.kind sw (nxF C) cap q = PSN.KBig.
Proof.
  intros sw C cap q H I1 I2 I3 I4. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
  destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

Lemma kind_cutbig : forall sw C cap q, 16 <= Z.of_nat (length C) - q ->
  PSN.incl sw (nxF C) q <> 0 -> cap < PSN.incl sw (nxF C) q -> cap <> 0 ->
  Z.of_nat (length C) < q + 16 + PSN.incl sw (nxF C) q ->
  PSN.kind sw (nxF C) cap q = PSN.KCutBig.
Proof.
  intros sw C cap q H I1 I2 I3 I4. generalize (nx_kind_cases sw (nxF C) cap q). rewrite kind_flen.
  destruct (PSN.kind sw (nxF C) cap q); intros K; cbv beta iota in K; first [reflexivity | exfalso; lia].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (e) The chain clause after an empty record                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* nx_chain_empty (PcapSourceNextSpec.v) takes PSN.kind = KEmpty and q <= length (nxF C); this reads the first off
   the header (kind_empty_iff) and the second off nxF_length. *)
Lemma chain_empty_at : forall sw C cap p q lh,
  nx_chain_inv sw (nxF C) cap p q lh -> q <= Z.of_nat (length C) ->
  PSN.incl sw (nxF C) q = 0 -> 16 <= Z.of_nat (length C) - q ->
  nx_chain_inv sw (nxF C) cap p (q + 16) lh.
Proof.
  intros sw C cap p q lh HI Hq Hi H.
  apply nx_chain_empty; [exact HI | rewrite nxF_length; exact Hq |].
  exact (proj2 (kind_empty_iff sw C cap q H) Hi).
Qed.
