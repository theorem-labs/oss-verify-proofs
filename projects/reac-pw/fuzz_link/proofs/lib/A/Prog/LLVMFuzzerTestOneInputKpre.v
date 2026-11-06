(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 867 of its 936 lines of code are new or changed and 335 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): kernel's Pre at
   the four kernel call sites of the 48-operation loop (0x82ec0 op_unmark, 0x832a4 op_mark, 0x83584 op_read,
   0x837e4 op_write; listing (internal path)
   (internal record, sha256 e84d6f0c6974)), built from what the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v
   carries. Shared by the three arm walks (owner: the read arms' walk; the other two Require it).

   `lf_kernel_apre` gives lib/A/Prog/kernel_c.v `kernel_apre` at a call with a0 = s1 + 0x118 (the cursor, LS_P) and
   sp = s1, from: lf_base, the call's journal (the shape lf_from hands a phase), arodata_okP at the call memory,
   lf_data at the call memory, the payload's bytes at the call memory, and the two cursor words.
   Where each conjunct comes from:
   - g_nl's bytes and shape: lf_data; its shadow: LinkWalkZsh.v zsh_gnl_ard (AR's zero-shadow rows).
   - the cursor: its two words (the arm reads them back), writable and present because they lie in the journal's
     window [sp0 - LLVMF_STK, sp0) (s1 + 0x118 .. s1 + 0x128 is in the real frame), shadow zero because they lie in
     the real-stack row of AR's zero_shadow_ranges (`kp_stack_ra`).
   - the payload [c_p + q, c_p + c_n): a heap block of the call's start state (tfib_lib_pre_x) that is still a block
     of the call state (`lf_input_block`: the journal lets a start block go only if all its bytes are in FP =
     amf_harness_fp T, and the payload is apart from the sink token and from every kept block); its shadow and band
     from YCbq.v range_addressable_of_block / shadow_hull_vis_of_block / amem_range_of_block; its place (off the
     image, below alloc_ceiling) from LinkPaLib.v blk_off_imgP and AR's block law. An empty payload is A_EMPTY.
   - nl_errno.e, msg_build.codes, the texts table and its eleven strings, .str.1, .str.8, odd[1..4]: read-only image
     bytes (a non-writable segment or the relro window [PCAP_RLO, PCAP_RHI)), outside the runtime's statics and errno,
     so arodata_okP gives them; their shadow from the image's zero rows (Tfib_zero_shadow) and constant shadow cells
     (Tfib_const_shadow), pinned by AR's const and zero-shadow laws. All checked by one computation at tfibsegs
     (`kp_img_checks`), reached through HSEGS : pa_segs = tfibsegs and PcapSyms B.
   - long_alias: lf_la_at (its 300 bytes, the NUL at 300, the 3 slack bytes); the NUL is writable (link_ajkit.v
     LA_LONG_ALIAS_writable); its shadow by the same computation.
   - the interface names: lf_ifp places every name pointer (g_names + 8 k, or odd[1..4]), and lf_tab's names are at
     most 11 bytes, so each name is apart from kernel's writes. A pointer is fixed only modulo 2 ^ 64 by au64_at, so a
     value off by a multiple of 2 ^ 64 is also covered.
   The stack bound: sp = s1 >= sp0 - 432 and the journal's window is 32768 bytes, so kernel's window
   [s1 - KERNEL_AK, s1) is inside it and above alloc_ceiling.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. Read-only image bytes, by computation
   ========================================================================== *)

(* a byte arodata_okP pins: in a non-writable segment or the relro window, not a runtime static, not errno *)
Definition kp_ro_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (a : Z) : bool :=
  (existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a)
                     && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
   || ((PCAP_RLO <=? a) && (a <? PCAP_RHI)))
  && negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) own)
  && negb ((err <=? a) && (a <? err + 4)).
Definition kp_rom_b (segs : list Segment) (a v : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Definition kp_some_b (segs : list Segment) (a : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.
(* the bytes l at a, each pinned *)
Definition kp_bytes_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (a : Z) (l : list Z) : bool :=
  forallb (fun i => kp_ro_b segs own err (a + Z.of_nat i) && kp_rom_b segs (a + Z.of_nat i) (nth i l 0))
    (seq 0 (length l)).
(* n bytes from a that the image holds (readable at every memory) *)
Definition kp_somes_b (segs : list Segment) (a : Z) (n : nat) : bool :=
  forallb (fun i => kp_some_b segs (a + Z.of_nat i)) (seq 0 n).
(* the 8 bytes of a word, as val_mem reads them *)
Definition kp_le8 (v : Z) : list Z := map (fun k => YO0f.le_byte v 8 k) (seq 0 8).

(* ==========================================================================
   2. The image's shadow, by computation over Tfib_zero_shadow and Tfib_const_shadow
   ========================================================================== *)

Definition kp_sval (s : Z) : option Z :=
  match find (row_hit s) Tfib_zero_shadow with
  | Some _ => Some 0
  | None =>
      match find (cell_ok s) Tfib_const_shadow with
      | Some (ACell _ w (AV (ANum v))) => Some (YG0f.le_byte v w 0)
      | _ => None
      end
  end.
Definition kp_saddr_b (x : Z) : bool :=
  match kp_sval (shadow_of_addr SHADOW_OFF x) with
  | Some s => (s =? 0) || ((x mod 8 <? s) && (s <? 8))
  | None => false
  end.
Definition kp_ra_b (p n : Z) : bool := forallb (fun i => kp_saddr_b (p + Z.of_nat i)) (seq 0 (Z.to_nat n)).
Definition kp_hull_b (p n : Z) : bool :=
  forallb (fun i => match kp_sval (shadow_addr p / 8 * 8 + Z.of_nat i) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (shadow_addr (p + n - 1) / 8 * 8 + 8 - shadow_addr p / 8 * 8))).

(* a C string in the read-only image that kernel hands to attr_text: its bytes and NUL pinned, no NUL inside, the
   slack to the next 8-byte boundary readable, its shadow addressable and visible, below g_nl *)
Definition kp_kstr_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (p : Z) (l : list Z) : bool :=
  (0 <? p) && (p + Z.of_nat (length l) + 8 <=? LA_G_NL)
  && forallb (fun z => (0 <? z) && (z <? 256)) l
  && kp_bytes_b segs own err p (l ++ [0])
  && kp_somes_b segs (p + Z.of_nat (length l) + 1) (Z.to_nat ((- (p + Z.of_nat (length l) + 1)) mod 8))
  && kp_ra_b p (Z.of_nat (length l) + 1)
  && kp_hull_b p (Z.of_nat (length l) + 1).

(* the texts table (texts[0..10], .data.rel.ro 0xa17c0) and the odd table (odd[0..5], 0xa1760): each pointer with
   the string it points at, read from the pin's PT_LOADs *)
Definition KP_TEXTS : list (Z * list Z) :=
  [(0x20fc0, []);
   (0x21100, [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100]);
   (0x21120, [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100]);
   (0x21140, [104; 111; 115; 116; 45; 97; 108; 105; 97; 115]);
   (0x21160, [114; 101; 97; 99; 45; 112; 119; 58]);
   (0x21180, [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 50]);
   (0x211a0, [114; 101; 97; 99; 45; 112; 119]);
   (0x211c0, [118; 108; 97; 110]);
   (0x211e0, [118; 101; 116; 104]);
   (0x21200, [118; 108; 97; 110; 120]);
   (0x21220, [118; 108; 97])].
Definition KP_ODD : list (Z * list Z) :=
  [(0x20fc0, []);
   (0x20fe0, [101; 110; 112; 49; 51; 49; 115; 48; 46; 51; 51]);
   (0x21000, [101; 116; 104; 48]);
   (0x21020, [119; 108; 97; 110; 48]);
   (0x21040, [118; 101; 116; 104; 45; 98; 111; 120]);
   (0x21060, [103; 111; 110; 101; 48])].
(* msg_build.codes, int32[4] at 0x210e0: -EPERM, -ENODEV, -EOPNOTSUPP, 5 *)
Definition KP_CODES : list Z := [255; 255; 255; 255; 237; 255; 255; 255; 161; 255; 255; 255; 5; 0; 0; 0].
(* nl_errno.e, int32[6] at 0x21080: word i as val_mem reads it *)
Definition kp_le4 (v : Z) : list Z := map (fun k => YO0f.le_byte v 4 k) (seq 0 4).

(* every image fact the kernel Pre needs, as one boolean *)
Definition kp_img_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  forallb (fun i => kp_bytes_b segs own err (LA_NL_ERRNO_E + 4 * Z.of_nat i) (kp_le4 (nth i nl_errno_tab 0)))
    (seq 0 6)
  && kp_ra_b LA_NL_ERRNO_E 24
  && kp_bytes_b segs own err LA_MSG_CODES KP_CODES
  && kp_ra_b LA_MSG_CODES 16
  && kp_ra_b LA_TEXTS (8 * TEXTS_N)
  && forallb (fun i => let e := nth i KP_TEXTS (0, []) in
       kp_bytes_b segs own err (LA_TEXTS + 8 * Z.of_nat i) (kp_le8 (fst e))
       && kp_kstr_b segs own err (fst e) (snd e)) (seq 0 11)
  && kp_kstr_b segs own err LA_STR_EMPTY []
  && kp_kstr_b segs own err LA_STR_X [120]
  && forallb (fun i => let e := nth i KP_ODD (0, []) in
       kp_bytes_b segs own err (LA_ODD + 8 * Z.of_nat i) (kp_le8 (fst e))
       && kp_kstr_b segs own err (fst e) (snd e)) (seq 1 4)
  && kp_ra_b LA_LONG_ALIAS LONG_ALIAS_SIZE
  && kp_hull_b LA_LONG_ALIAS LONG_ALIAS_SIZE.

Lemma kp_img_checks : kp_img_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

(* the read set's image ranges (kernel_ard): every byte in the image, not a runtime static, not errno (akb's
   image clause) *)
Definition kp_akb_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
  && negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) own)
  && negb ((err <=? a) && (a <? err + 4)).
Definition kp_akbs_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (a : Z) (n : nat) : bool :=
  forallb (fun i => kp_akb_b segs own err (a + Z.of_nat i)) (seq 0 n).
Definition kp_ard_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  kp_akbs_b segs own err LA_NL_ERRNO_E 24
  && kp_akbs_b segs own err LA_MSG_CODES 16
  && kp_akbs_b segs own err LA_TEXTS 88
  && forallb (fun i => let e := nth i KP_TEXTS (0, []) in kp_akbs_b segs own err (fst e) (S (length (snd e))))
       (seq 0 11)
  && kp_akbs_b segs own err LA_STR_EMPTY 1
  && kp_akbs_b segs own err LA_STR_X 2
  && forallb (fun i => let e := nth i KP_ODD (0, []) in kp_akbs_b segs own err (fst e) (S (length (snd e))))
       (seq 1 4).

Lemma kp_ard_checks : kp_ard_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

(* the first 60 names of lf_tab (g_names' "nl<k>") are at most 4 bytes *)
Lemma lf_tab_gnames_short : forallb (fun e => Nat.leb (length (fst e)) 4) (firstn 60 lf_tab) = true.
Proof. vm_compute. reflexivity. Qed.

(* the odd table odd[0..5] and the texts table texts[0..10] with their strings, as lf_odd_at / lf_texts_at read
   them: the words and the strings read-only image bytes outside the runtime's statics and errno *)
Definition kp_rostr_b (segs : list Segment) (own : list (Z * Z)) (err : Z) (p : Z) (l : list Z) : bool :=
  (0 <? p) && (p + Z.of_nat (length l) + 8 <=? LA_G_NL)
  && forallb (fun z => (0 <? z) && (z <? 256)) l
  && kp_bytes_b segs own err p (l ++ [0]).
Definition kp_tabs_b (segs : list Segment) (own : list (Z * Z)) (err : Z) : bool :=
  forallb (fun i => let e := nth i KP_ODD (0, []) in
     kp_bytes_b segs own err (LA_ODD + 8 * Z.of_nat i) (kp_le8 (fst e)) && kp_rostr_b segs own err (fst e) (snd e))
    (seq 0 6)
  && forallb (fun i => let e := nth i KP_TEXTS (0, []) in
     kp_bytes_b segs own err (LA_TEXTS + 8 * Z.of_nat i) (kp_le8 (fst e)) && kp_rostr_b segs own err (fst e) (snd e))
    (seq 0 11).

Lemma kp_tabs_checks : kp_tabs_b tfibsegs Tfib_owned_static TFIB_ERRNO = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kp_odd_nth : forall i, nth i lf_odd_strs [] = map (Z_to_bv 8) (snd (nth i KP_ODD (0, []))).
Proof. intros i. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.

(* odd[1..4] lie below g_nl, with room for their strings *)
Lemma kp_odd_low : forallb (fun j => (0 <=? fst (nth j KP_ODD (0, []))) && (fst (nth j KP_ODD (0, [])) + 12 <=? LA_G_NL))
  (seq 1 4) = true.
Proof. vm_compute. reflexivity. Qed.

(* lf_tab's names are at most 11 bytes *)
Lemma lf_tab_names_short : forallb (fun e => Nat.leb (length (fst e)) 11) lf_tab = true.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3. From the booleans to the views
   ========================================================================== *)

Lemma kp_forallb_seq : forall (f : nat -> bool) n, forallb f (seq 0 n) = true -> forall i, (i < n)%nat -> f i = true.
Proof.
  intros f n H i Hi. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

Lemma kp_mbyte_of_aview : forall segs H (mem : word -> option byte) a b,
  aview segs H mem a = Some (bv_unsigned b) -> mbyte segs (mrestrict H mem) a = Some b.
Proof.
  intros segs H mem a b Ha. unfold aview in Ha.
  destruct (mbyte segs (mrestrict H mem) a) as [b'|] eqn:E; [|discriminate].
  cbn [option_map] in Ha. injection Ha as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

Lemma kp_bytes_mbyte : forall segs own err B H (mem : word -> option byte) a l,
  as_owned_static B = own -> as_errno B = err ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs own err a l = true ->
  forall i, (i < length l)%nat -> mbyte segs (mrestrict H mem) (a + Z.of_nat i) = Some (Z_to_bv 8 (nth i l 0)).
Proof.
  intros segs own err B H mem a l Ho He HR Hb i Hi.
  pose proof (kp_forallb_seq _ _ Hb i Hi) as Hx. cbv beta in Hx.
  apply andb_prop in Hx as [Hro Hrom]. unfold kp_ro_b in Hro.
  apply andb_prop in Hro as [Hro Herr]. apply andb_prop in Hro as [Hseg Hown].
  set (x := a + Z.of_nat i) in *.
  unfold kp_rom_b in Hrom. destruct (seg_rom segs (Z_to_bv 64 x)) as [b|] eqn:Er; [|discriminate].
  apply Z.eqb_eq in Hrom.
  assert (Hv : aview segs H mem x = Some (bv_unsigned b)).
  { rewrite (HR x).
    - rewrite Er. reflexivity.
    - apply orb_prop in Hseg as [Hs | Hs].
      + left. apply existsb_exists in Hs as (s & Hin & Hs).
        apply andb_prop in Hs as [Hs Hhi]. apply andb_prop in Hs as [Hw Hlo].
        apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
        exists s. split; [exact Hin|]. split; [exact Hw | lia].
      + right. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
      rewrite Ho in Hr. apply negb_true_iff in Hown.
      assert (Hx : existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) own = true)
        by (apply existsb_exists; exists r; split; [exact Hr|];
            apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Hx in Hown. discriminate.
    - intros Hx. apply negb_true_iff in Herr. rewrite He in Hx.
      assert (Ht : ((err <=? x) && (x <? err + 4))%bool = true)
        by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Ht in Herr. discriminate. }
  rewrite (kp_mbyte_of_aview segs H mem x b Hv). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hrom.
  unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma kp_somes_mbyte : forall segs (m : word -> option byte) a n,
  kp_somes_b segs a n = true -> forall i, (i < n)%nat -> exists b, mbyte segs m (a + Z.of_nat i) = Some b.
Proof.
  intros segs m a n H i Hi. pose proof (kp_forallb_seq _ _ H i Hi) as Hx. cbv beta in Hx.
  unfold kp_some_b in Hx. unfold mbyte.
  destruct (m (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [exists b; reflexivity|].
  destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [exists b; reflexivity | discriminate].
Qed.

(* the n bytes l at a, as abytes *)
Lemma kp_abytes : forall segs own err B H (mem : word -> option byte) a l,
  as_owned_static B = own -> as_errno B = err ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs own err a l = true -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  abytes segs (mrestrict H mem) a (map (Z_to_bv 8) l).
Proof.
  intros segs own err B H mem a l Ho He HR Hb Ha Hal. split; [exact Ha|].
  rewrite length_map. split; [exact Hal|]. intros i Hi.
  rewrite (kp_bytes_mbyte segs own err B H mem a l Ho He HR Hb i Hi).
  rewrite nth_error_map. rewrite (nth_error_nth' l 0 Hi). reflexivity.
Qed.

(* a word as val_mem reads it *)
Lemma kp_val_mem8 : forall segs own err B H (mem : word -> option byte) a v,
  as_owned_static B = own -> as_errno B = err ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs own err a (kp_le8 v) = true ->
  val_mem segs (mrestrict H mem) a 8 v.
Proof.
  intros segs own err B H mem a v Ho He HR Hb k Hk.
  assert (Hl : length (kp_le8 v) = 8%nat) by (unfold kp_le8; rewrite length_map, length_seq; reflexivity).
  rewrite (kp_bytes_mbyte segs own err B H mem a (kp_le8 v) Ho He HR Hb k ltac:(lia)).
  unfold kp_le8. rewrite (nth_indep _ 0 (YO0f.le_byte v 8 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma kp_val_mem4 : forall segs own err B H (mem : word -> option byte) a v,
  as_owned_static B = own -> as_errno B = err ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs own err a (kp_le4 v) = true ->
  val_mem segs (mrestrict H mem) a 4 v.
Proof.
  intros segs own err B H mem a v Ho He HR Hb k Hk.
  rewrite (kp_bytes_mbyte segs own err B H mem a _ Ho He HR Hb k ltac:(unfold kp_le4; rewrite length_map, length_seq; lia)).
  unfold kp_le4. rewrite (nth_indep _ 0 (YO0f.le_byte v 4 0)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma kp_cell_ok_inv : forall s c, cell_ok s c = true ->
  exists w v, c = ACell (ANum s) w (AV (ANum v)) /\ (0 < w)%nat.
Proof.
  intros s [ca w cv]. unfold cell_ok. destruct ca; try discriminate.
  destruct cv as [e|]; try discriminate. destruct e; try discriminate.
  intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.ltb_lt in H2. subst.
  do 2 eexists. split; [reflexivity | exact H2].
Qed.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma kp_sval_ok : forall ly S rd s v, ARm B ly S rd -> kp_sval s = Some v -> rd s = Some v.
Proof.
  intros ly S rd s v M. unfold kp_sval.
  destruct (find (row_hit s) Tfib_zero_shadow) as [[lo n]|] eqn:Hf.
  - intros Hv. cbv iota beta in Hv. injection Hv as <-.
    destruct (find_some _ _ Hf) as [Hin Hb]. unfold row_hit in Hb. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    pose proof (zsh_row_zero B TB ly S rd lo n M Hin) as Z1. unfold zero_shadow, shadow_of_addr in Z1.
    replace s with (SHADOW_OFF + lo / 8 + (s - (SHADOW_OFF + lo / 8))) by lia.
    apply Z1. lia.
  - destruct (find (cell_ok s) Tfib_const_shadow) as [c|] eqn:Hc; [|discriminate].
    destruct (find_some _ _ Hc) as [Hin Hok].
    destruct (kp_cell_ok_inv s c Hok) as (w & v' & -> & Hw).
    intros Hv. cbv iota beta in Hv. injection Hv as <-.
    assert (HinT : In (ACell (ANum s) w (AV (ANum v'))) (as_const B ly)).
    { rewrite (ts_const B TB ly). unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    pose proof (proj1 (Forall_forall _ _) (am_const B ly S rd M) _ HinT) as C.
    unfold cell_holds in C. cbn [c_at c_w c_val aeval] in C.
    specialize (C 0%nat Hw). rewrite Z.add_0_r in C. exact C.
Qed.

Lemma kp_ra : forall ly S rd p n, ARm B ly S rd -> kp_ra_b p n = true -> range_addressable rd SHADOW_OFF p n.
Proof.
  intros ly S rd p n M Hb x Hx.
  pose proof (kp_forallb_seq _ _ Hb (Z.to_nat (x - p)) ltac:(lia)) as Hx'. cbv beta in Hx'.
  replace (p + Z.of_nat (Z.to_nat (x - p))) with x in Hx' by lia.
  unfold kp_saddr_b in Hx'. destruct (kp_sval (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:Hs; [|discriminate].
  exists s. split; [exact (kp_sval_ok ly S rd _ s M Hs)|].
  unfold saddr_ok. apply orb_prop in Hx' as [H0 | H1]; [left; apply Z.eqb_eq; exact H0|].
  right. apply andb_prop in H1 as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma kp_hull : forall ly S rd p n, ARm B ly S rd -> kp_hull_b p n = true -> shadow_hull_vis rd p n.
Proof.
  intros ly S rd p n M Hb s Hs.
  pose proof (kp_forallb_seq _ _ Hb (Z.to_nat (s - shadow_addr p / 8 * 8)) ltac:(lia)) as Hx. cbv beta in Hx.
  replace (shadow_addr p / 8 * 8 + Z.of_nat (Z.to_nat (s - shadow_addr p / 8 * 8))) with s in Hx by lia.
  destruct (kp_sval s) as [v|] eqn:Hv; [|discriminate].
  rewrite (kp_sval_ok ly S rd s v M Hv). discriminate.
Qed.

(* the real-stack row's shadow is zero at every AR state (YG0n.v zero_shadow_ranges, first row) *)
Lemma kp_stack_ra : forall ly S rd p n, ARm B ly S rd -> ly_stk_lo ly <= p -> p + n <= ly_stk_hi ly ->
  range_addressable rd SHADOW_OFF p n.
Proof.
  intros ly S rd p n M Hlo Hhi x Hx.
  pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ M) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold zero_shadow, shadow_of_addr in HZ.
  pose proof (am_layout B ly S _ M) as LO. destruct (lo_top _ LO) as (_ & _ & _ & _ & Pl & Ph & _).
  unfold page_aligned in Pl, Ph.
  exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo ly / 8 + (x / 8 - ly_stk_lo ly / 8)) by lia.
  apply HZ. lia.
Qed.
End sh.

(* ==========================================================================
   4. Small facts
   ========================================================================== *)

Lemma kp_rdword_range : forall (rd : reader) a v,
  (forall x, match rd x with Some b => 0 <= b < 256 | None => True end) ->
  rdword rd a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros rd a v Hr Hw. unfold rdword in Hw.
  pose proof (Hr a) as R0. pose proof (Hr (a + 1)) as R1. pose proof (Hr (a + 2)) as R2.
  pose proof (Hr (a + 3)) as R3. pose proof (Hr (a + 4)) as R4. pose proof (Hr (a + 5)) as R5.
  pose proof (Hr (a + 6)) as R6. pose proof (Hr (a + 7)) as R7.
  destruct (rd a), (rd (a + 1)), (rd (a + 2)), (rd (a + 3)), (rd (a + 4)), (rd (a + 5)), (rd (a + 6)),
    (rd (a + 7)); try discriminate.
  injection Hw as <-. lia.
Qed.

Lemma kp_aview_range : forall segs H (mem : word -> option byte) x,
  match aview segs H mem x with Some b => 0 <= b < 256 | None => True end.
Proof.
  intros segs H mem x. unfold aview. destruct (mbyte segs (mrestrict H mem) x) as [b|]; [|exact I].
  cbn [option_map]. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* a byte value fixes the Z_to_bv 8 byte *)
Lemma kp_zb_inj : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z_to_bv 8 x = Z_to_bv 8 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  unfold bv_wrap in E. change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* a word's eight bytes fix it modulo 2 ^ 64 *)
Lemma kp_vm8_mod : forall segs (m : word -> option byte) a v1 v2,
  val_mem segs m a 8 v1 -> val_mem segs m a 8 v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros segs m a v1 v2 H1 H2.
  set (l := map (fun k => Z_to_bv 8 (YG0f.le_byte v1 8 k)) (seq 0 8)).
  assert (Hl : length l = 8%nat) by (unfold l; rewrite length_map, length_seq; reflexivity).
  assert (Lb : forall v k, 0 <= YG0f.le_byte v 8 k < 256)
    by (intros v k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
  assert (Lm : forall v k, YG0f.le_byte (v mod 2 ^ 64) 8 k = YG0f.le_byte v 8 k)
    by (intros v k; unfold YG0f.le_byte; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite Z.mod_mod by lia;
        reflexivity).
  assert (Hn : forall k, (k < 8)%nat -> nth_error l k = Some (Z_to_bv 8 (YG0f.le_byte v1 8 k))).
  { intros k Hk. unfold l. rewrite (lw_nth_error_map_seq _ 8 0 k Hk). reflexivity. }
  assert (E12 : forall k, (k < 8)%nat -> YG0f.le_byte v1 8 k = YG0f.le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as A1. pose proof (H2 k Hk) as A2. rewrite A1 in A2.
    assert (A3 : Z_to_bv 8 (YO0f.le_byte v1 8 k) = Z_to_bv 8 (YO0f.le_byte v2 8 k)) by congruence.
    apply kp_zb_inj; [apply Lb | apply Lb |].
    unfold YG0f.le_byte. unfold YO0f.le_byte in A3. exact A3. }
  assert (B1 : bytes_le_to_Z l = v1 mod 2 ^ 64).
  { apply (lw_bytes_of_vals 8 l (v1 mod 2 ^ 64) Hl).
    - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
    - intros k Hk. rewrite (Hn k Hk). f_equal. f_equal.
      unfold YG0f.le_byte, YO0f.le_byte; try unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
      rewrite Z.mod_mod by lia. reflexivity. }
  assert (B2 : bytes_le_to_Z l = v2 mod 2 ^ 64).
  { apply (lw_bytes_of_vals 8 l (v2 mod 2 ^ 64) Hl).
    - change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
    - intros k Hk. rewrite (Hn k Hk). f_equal. f_equal. rewrite (E12 k Hk).
      unfold YG0f.le_byte, YO0f.le_byte; try unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
      rewrite Z.mod_mod by lia. reflexivity. }
  congruence.
Qed.

(* two C strings at one address are one string *)
Lemma kp_acstr_unique : forall segs m p s s', acstr_at segs m p s -> acstr_at segs m p s' -> s = s'.
Proof.
  intros segs m p s s' ((_ & _ & H1) & N1) ((_ & _ & H2) & N2).
  assert (Hlen : length s = length s').
  { destruct (Nat.lt_trichotomy (length s) (length s')) as [Hl | [Hl | Hl]]; [exfalso | exact Hl | exfalso].
    - pose proof (H1 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as A.
      pose proof (H2 (length s) ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
      rewrite A in Bq. rewrite nth_error_app2 in Bq by lia. rewrite Nat.sub_diag in Bq. cbn [nth_error] in Bq.
      rewrite nth_error_app1 in Bq by lia. symmetry in Bq. apply nth_error_In in Bq. exact (N2 Bq).
    - pose proof (H1 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as A.
      pose proof (H2 (length s') ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
      rewrite Bq in A. rewrite nth_error_app2 in A by lia. rewrite Nat.sub_diag in A. cbn [nth_error] in A.
      rewrite nth_error_app1 in A by lia. symmetry in A. apply nth_error_In in A. exact (N1 A). }
  apply lw_list_ext; [exact Hlen|]. intros i Hi.
  pose proof (H1 i ltac:(rewrite length_app; cbn [length]; lia)) as A.
  pose proof (H2 i ltac:(rewrite length_app; cbn [length]; lia)) as Bq.
  rewrite A in Bq. rewrite nth_error_app1 in Bq by lia. rewrite nth_error_app1 in Bq by lia. exact Bq.
Qed.

(* a C string the booleans describe, as acstr_at *)
Lemma kp_acstr : forall segs own err B H (mem : word -> option byte) p l,
  as_owned_static B = own -> as_errno B = err ->
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_bytes_b segs own err p (l ++ [0]) = true -> forallb (fun z => (0 <? z) && (z <? 256)) l = true ->
  0 <= p -> p + Z.of_nat (length l) + 1 <= 2 ^ 64 ->
  acstr_at segs (mrestrict H mem) p (map (Z_to_bv 8) l).
Proof.
  intros segs own err B H mem p l Ho He HR Hb Hz H0 H1. split.
  - replace (map (Z_to_bv 8) l ++ [zb 0]) with (map (Z_to_bv 8) (l ++ [0])) by (rewrite map_app; reflexivity).
    apply (kp_abytes segs own err B H mem p (l ++ [0]) Ho He HR Hb H0).
    rewrite length_app. cbn [length]. lia.
  - intros Hin. apply in_map_iff in Hin as (z & Hz0 & Hzl).
    rewrite forallb_forall in Hz. specialize (Hz z Hzl). apply andb_prop in Hz as [Za Zb].
    apply Z.ltb_lt in Za. apply Z.ltb_lt in Zb.
    apply kp_zb_inj in Hz0; lia.
Qed.

(* every byte a kp_bytes_b check reads is read-only *)
Lemma kp_bytes_inroP : forall segs own err a l, kp_bytes_b segs own err a l = true ->
  forall i, (i < length l)%nat -> in_roP segs PCAP_RLO PCAP_RHI (a + Z.of_nat i).
Proof.
  intros segs own err a l Hb i Hi.
  pose proof (kp_forallb_seq _ _ Hb i Hi) as Hx. cbv beta in Hx.
  apply andb_prop in Hx as [Hro _]. unfold kp_ro_b in Hro.
  apply andb_prop in Hro as [Hro _]. apply andb_prop in Hro as [Hseg _].
  apply orb_prop in Hseg as [Hs | Hs].
  - left. apply existsb_exists in Hs as (s & Hin & Hs).
    apply andb_prop in Hs as [Hs Hhi]. apply andb_prop in Hs as [Hw Hlo].
    apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    exists s. split; [exact Hin|]. split; [exact Hw | lia].
  - right. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma kp_rostr : forall segs B H (mem : word -> option byte) p l,
  arodata_okP segs PCAP_RLO PCAP_RHI B (aview segs H mem) ->
  kp_rostr_b segs (as_owned_static B) (as_errno B) p l = true ->
  acstr_at segs (mrestrict H mem) p (map (Z_to_bv 8) l) /\ p <> 0 /\
  (forall j, 0 <= j <= Z.of_nat (length (map (Z_to_bv 8) l)) -> in_roP segs PCAP_RLO PCAP_RHI (p + j)).
Proof.
  intros segs B H mem p l HRO Hk. unfold kp_rostr_b in Hk.
  apply andb_prop in Hk as [Hk Hby]. apply andb_prop in Hk as [Hk Hnz]. apply andb_prop in Hk as [Hp0 Hpl].
  apply Z.ltb_lt in Hp0. apply Z.leb_le in Hpl.
  split; [apply (kp_acstr segs _ _ B H mem p l eq_refl eq_refl HRO Hby Hnz); unfold LA_G_NL in *; lia|].
  split; [lia|].
  intros j Hj. rewrite length_map in Hj.
  replace (p + j) with (p + Z.of_nat (Z.to_nat j)) by lia.
  apply (kp_bytes_inroP segs _ _ p (l ++ [0]) Hby). rewrite length_app. cbn [length]. lia.
Qed.

(* ==========================================================================
   5. The phase context
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

(* the image instance: its allocator laws, its symbols, its segments *)
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma kp_img_here : kp_img_b SEGS (as_owned_static B) (as_errno B) = true.
Proof. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). exact kp_img_checks. Qed.

(* What the call's journal says of the real frame: the entry sp's alignment, the window above the allocator's
   ceiling, inside the current stack row, and present. *)
Lemma lf_frame_facts : forall cx fp ly S W mem mdl k,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  spZ (c_regs cx) mod 16 = 0 /\
  alloc_ceiling <= spZ (c_regs cx) - LLVMF_STK /\
  ly_stk_lo ly + LLVMF_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W) mem a) /\
  AR SEGS B ly S W mem mdl.
Proof.
  intros cx fp ly S W mem mdl k HB HJ.
  destruct HB as (HPRE & _). destruct HPRE as (Hafn & _).
  destruct Hafn as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (H16 & _).
  pose proof HJ as Hrow. eapply ajournal_gx_row in Hrow. destruct Hrow as (Hc & H47 & Hlo & Hhi).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  try rewrite !Z.add_0_r in Hpres. try rewrite !Z.add_0_r in Hhi.
  unfold LLVMF_STK in *.
  refine (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ HAR)))))); [lia | lia | lia | lia |].
  intros a Ha. apply Hpres. lia.
Qed.

(* the payload is still a block at every state of the call *)
Lemma lf_input_block : forall cx fp ly S W mem mdl k,
  BASEF cx -> JRN cx fp ly S W mem mdl k -> 0 < c_n cx ->
  In (c_p cx, c_n cx) (ablocks B ly S).
Proof.
  intros cx fp ly S W mem mdl k HB HJ Hn.
  destruct HB as (HPRE & _).
  destruct HPRE as (Hafn & _ & _ & _ & Hpn & _ & _ & _ & _ & _ & _ & _ & Hincl & HnT & _).
  destruct Hafn as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin0)]; [lia|].
  assert (Hd : forall x y : Z * Z, {x = y} + {x <> y})
    by (intros [x1 x2] [y1 y2]; destruct (Z.eq_dec x1 y1), (Z.eq_dec x2 y2);
        [left; congruence | right; congruence | right; congruence | right; congruence]).
  destruct (in_dec Hd (c_p cx, c_n cx) (ablocks B ly S)) as [Hin | Hout];
    [exact Hin | exfalso].
  pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (_ & Hp4096 & _).
  assert (Hr : 0 <= 0 < req_size (c_n cx)) by (unfold req_size; destruct (c_n cx =? 0) eqn:E; [lia|]; lia).
  pose proof (HG (c_p cx) (c_n cx) 0 Hin0 Hout Hr) as (r & Hrin & Hr1 & Hr2).
  rewrite Z.add_0_r in Hr1, Hr2. unfold amf_harness_fp in Hrin. destruct Hrin as [<- | Hrin].
  - unfold YI16.sink_token in Hr1, Hr2. cbn [fst snd] in Hr1, Hr2. lia.
  - apply in_map_iff in Hrin as ([b m] & <- & Hbm). cbn [fst snd] in Hr1, Hr2.
    assert (Hne : (b, m) <> (c_p cx, c_n cx)) by (intros E; rewrite E in Hbm; exact (HnT Hn Hbm)).
    pose proof (sep_blocks _ _ LAWS _ _ _ _ _ b m (c_p cx) (c_n cx) HAR0 (Hincl _ Hbm) Hin0 Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D.
    assert (Rm : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
    assert (Rn : 1 <= req_size (c_n cx)) by (unfold req_size; destruct (c_n cx =? 0) eqn:E; [lia|]; lia).
    lia.
Qed.

(* kernel_apart of an image range below g_nl *)
Lemma kp_apart_low : forall regs p n, 0 <= p -> p + n <= LA_G_NL ->
  alloc_ceiling <= spZ regs - KERNEL_AK -> spZ regs <= aarg regs 0 -> kernel_apart regs p n.
Proof.
  intros regs p n H0 H1 H2 H3. pose proof asan_consts as ((C1a & C1b) & _).
  rewrite KERNEL_AK_val in H2. unfold LA_G_NL in H1.
  unfold kernel_apart, apart_frame, apart_gnl, apart, LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE.
  rewrite KERNEL_AK_val. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* kernel_apart of a name: its pointer is one of the 64 places lf_ifp gives, modulo 2 ^ 64 *)
Lemma kp_apart_name : forall regs p q n, p mod 2 ^ 64 = q -> 0 <= n <= 12 ->
  ((0 <= q /\ q + 12 <= LA_G_NL) \/ (LA_G_NL + NK_SIZE <= q /\ q + 12 <= LA_LONG_ALIAS)) ->
  alloc_ceiling <= spZ regs - KERNEL_AK -> spZ regs <= aarg regs 0 -> aarg regs 0 + 16 <= 2 ^ 47 ->
  kernel_apart regs p n.
Proof.
  intros regs p q n Hq Hn Hplace H2 H3 H4. pose proof asan_consts as ((C1a & C1b) & _).
  rewrite KERNEL_AK_val in H2.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D. rewrite Hq in D.
  set (t := p / 2 ^ 64) in *.
  unfold LA_G_NL, NK_SIZE, LA_LONG_ALIAS in Hplace.
  unfold kernel_apart, apart_frame, apart_gnl, apart, LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE, NK_SIZE.
  rewrite KERNEL_AK_val.
  destruct (Z.lt_trichotomy t 0) as [Ht | [Ht | Ht]].
  - assert (Hp : p + n <= 0) by nia.
    split; [lia|]. split; [lia|]. split; lia.
  - rewrite Ht, Z.mul_0_r, Z.add_0_l in D. subst p.
    split; [lia|]. split; [lia|]. split; lia.
  - assert (Hp : 2 ^ 64 <= p) by nia.
    split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ==========================================================================
   6. The kernel Pre at a kernel call site
   ========================================================================== *)

Lemma lf_kernel_apre : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs (regs : bvmap 5 word) P N,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  abytes SEGS (rdW W mem) (c_p cx) (c_pl cx) ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_P) = Some P ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_N) = Some N ->
  (exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) ->
  aarg regs 0 = lf_sp1 cx + LS_P -> spZ regs = lf_sp1 cx ->
  kernel_apre SEGS regs (rdW W mem).
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs regs P N HB HJ HRO HD Hpl HP HN (q & Hq & -> & ->) Ha0 Hsp.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts cx fp ly S W mem mdl k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof HAR as (M & _).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (_ & _ & _ & _ & Hpn & Hlen & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (Hs1 : sp0 - 416 - 16 <= lf_sp1 cx <= sp0 - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range sp0 ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16) as (R & _).
    unfold LF_MFRAME in R. exact R. }
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  unfold LS_P, LS_N, LLVMF_STK in *.
  assert (HspK : alloc_ceiling <= spZ regs - KERNEL_AK) by lia.
  assert (Hsa0 : spZ regs <= aarg regs 0) by lia.
  assert (Ha47 : aarg regs 0 + 16 <= 2 ^ 47) by lia.
  pose proof kp_img_here as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  rename KI into KErr.
  match goal with H : kp_hull_b LA_LONG_ALIAS _ = true |- _ => rename H into KLah end.
  match goal with H : kp_ra_b LA_LONG_ALIAS _ = true |- _ => rename H into KLar end.
  match goal with H : forallb _ (seq 1 4) = true |- _ => rename H into KOdd end.
  match goal with H : kp_kstr_b _ _ _ LA_STR_X _ = true |- _ => rename H into KStrX end.
  match goal with H : kp_kstr_b _ _ _ LA_STR_EMPTY _ = true |- _ => rename H into KStrE end.
  match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
  match goal with H : kp_ra_b LA_TEXTS _ = true |- _ => rename H into KTxr end.
  match goal with H : kp_ra_b LA_MSG_CODES _ = true |- _ => rename H into KCr end.
  match goal with H : kp_bytes_b _ _ _ LA_MSG_CODES _ = true |- _ => rename H into KC end.
  match goal with H : kp_ra_b LA_NL_ERRNO_E _ = true |- _ => rename H into KEr end.
  pose proof (eq_refl (as_owned_static B)) as Ho. pose proof (eq_refl (as_errno B)) as He.
  (* kernel_str of a read-only string the booleans describe *)
  assert (KSTR : forall p l, kp_kstr_b SEGS (as_owned_static B) (as_errno B) p l = true ->
                   kernel_str SEGS regs (rdW W mem) p).
  { intros p l Hk. unfold kp_kstr_b in Hk.
    repeat match type of Hk with (_ && _)%bool = true => apply andb_prop in Hk as [Hk ?] end.
    rename Hk into Hp0.
    match goal with H : kp_hull_b _ _ = true |- _ => rename H into Hh end.
    match goal with H : kp_ra_b _ _ = true |- _ => rename H into Hra end.
    match goal with H : kp_somes_b _ _ _ = true |- _ => rename H into Hsl end.
    match goal with H : kp_bytes_b _ _ _ _ _ = true |- _ => rename H into Hby end.
    match goal with H : forallb _ l = true |- _ => rename H into Hnz end.
    match goal with H : (_ <=? LA_G_NL) = true |- _ => apply Z.leb_le in H; rename H into Hpl8 end.
    apply Z.ltb_lt in Hp0.
    pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length l) + 1)) 8 ltac:(lia)) as Hk8.
    exists (map (Z_to_bv 8) l),
      (abytes_of SEGS (rdW W mem) (p + Z.of_nat (length l) + 1)
         (Z.to_nat ((- (p + Z.of_nat (length l) + 1)) mod 8))).
    rewrite length_map.
    split; [unfold LA_G_NL in *; lia|].
    split; [apply (kp_acstr SEGS _ _ B (w_H W) mem p l Ho He HRO Hby Hnz); unfold LA_G_NL in *; lia|].
    split; [unfold LA_G_NL in *; lia|].
    split.
    { apply abytes_of_abytes; [lia | rewrite Z2Nat.id by lia; unfold LA_G_NL in *; lia|].
      intros i Hi. exact (kp_somes_mbyte SEGS (rdW W mem) _ _ Hsl i Hi). }
    split; [rewrite abytes_of_length, Z2Nat.id by lia; lia|].
    split; [unfold amem_range; left; unfold LA_G_NL in *; lia|].
    split; [rewrite ard_aview; exact (kp_ra B TB ly S _ p _ M Hra)|].
    split; [rewrite ard_aview; exact (kp_hull B TB ly S _ p _ M Hh)|].
    apply kp_apart_low; [lia | unfold LA_G_NL in *; lia | exact HspK | exact Hsa0]. }
  destruct HD as (Hnlk & Hwf & Htab & _ & _ & _ & _ & _ & _ & _ & _ & Hifp & _ & _ & _ & _ & Hla).
  exists kbs.
  split; [exact Hnlk|]. split; [exact Hwf|].
  destruct (zsh_gnl_ard B TB SEGS ly S W mem mdl HAR) as (Hgra & Hghv).
  split; [exact Hgra|]. split; [exact Hghv|].
  (* the cursor and the payload *)
  split.
  { exists (c_p cx + q), (c_n cx - q).
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HP) as RP.
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HN) as RN.
    split; [rewrite Ha0; exact (val_mem_of_rdword SEGS (w_H W) mem _ _ HP)|].
    split; [rewrite Ha0; replace (lf_sp1 cx + 280 + 8) with (lf_sp1 cx + 288) by lia;
            exact (val_mem_of_rdword SEGS (w_H W) mem _ _ HN)|].
    split; [exact RP|]. split; [exact RN|].
    split.
    { exists (skipn (Z.to_nat q) (c_pl cx)). destruct Hpl as (Hp0 & Hpe & Hpb).
      rewrite length_skipn. unfold c_n in *. split; [|lia].
      split; [lia|]. rewrite length_skipn. split; [lia|].
      intros i Hi. try rewrite length_skipn in Hi. rewrite lw_nth_error_skipn.
      replace (c_p cx + q + Z.of_nat i) with (c_p cx + Z.of_nat (Z.to_nat q + i)) by lia.
      apply Hpb. lia. }
    destruct (Z.eq_dec (c_n cx) 0) as [Hn0 | Hn0].
    - (* the empty payload: A_EMPTY, nothing to read *)
      destruct Hpn as [(_ & Hpe) | (Hnp & _)]; [|lia].
      assert (Hq0 : q = 0) by lia. subst q. rewrite Hn0, Hpe. unfold A_EMPTY.
      split; [unfold amem_range; left; lia|].
      split; [intros x Hx; lia|]. split; [intros Hx; lia|].
      apply kp_apart_low; [lia | unfold LA_G_NL; lia | exact HspK | exact Hsa0].
    - assert (Hnp : 0 < c_n cx) by (unfold c_n in *; lia).
      pose proof (lf_input_block cx fp ly S W mem mdl k HB HJ Hnp) as Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & _).
      assert (Hoff : off_img (c_p cx) (req_size (c_n cx))) by (eapply blk_off_imgP; eassumption).
      unfold off_img in Hoff.
      assert (Rn : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (c_n cx =? 0) eqn:E; [lia | reflexivity]).
      rewrite Rn in Hbceil, Hoff.
      split; [eapply amem_range_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]|].
      split; [rewrite ard_aview;
              eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]|].
      split; [intros Hpos; rewrite ard_aview;
              eapply shadow_hull_vis_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia | lia]|].
      unfold kernel_apart, apart_frame, apart_gnl, apart, LA_G_NL, LA_LONG_ALIAS, LONG_ALIAS_SIZE, NK_SIZE,
        YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
      repeat split; lia. }
  (* the cursor's own bytes *)
  split; [intros i Hi; apply (apresent_writable SEGS); apply Hwin; rewrite Ha0 in *; lia|].
  split; [rewrite ard_aview, Ha0; apply (kp_stack_ra B ly S _ _ _ M); lia|].
  split; [unfold apart_frame; right; lia|].
  split; [unfold apart_gnl, LA_G_NL, NK_SIZE; right; lia|].
  split; [unfold apart, LA_LONG_ALIAS, LONG_ALIAS_SIZE; right; lia|].
  (* nl_errno.e *)
  split.
  { intros i Hi. pose proof (kp_forallb_seq _ _ KErr (Z.to_nat i) ltac:(lia)) as Hx. cbv beta in Hx.
    rewrite Z2Nat.id in Hx by lia. exact (kp_val_mem4 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hx). }
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M KEr)|].
  split; [apply kp_apart_low; [unfold LA_NL_ERRNO_E; lia | unfold LA_NL_ERRNO_E, LA_G_NL; lia | exact HspK | exact Hsa0]|].
  (* msg_build.codes *)
  split.
  { exists (map (Z_to_bv 8) KP_CODES). split; [|reflexivity].
    apply (kp_abytes SEGS _ _ B (w_H W) mem _ _ Ho He HRO KC); unfold LA_MSG_CODES; cbn; lia. }
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M KCr)|].
  split; [apply kp_apart_low; [unfold LA_MSG_CODES; lia | unfold LA_MSG_CODES, LA_G_NL; lia | exact HspK | exact Hsa0]|].
  (* texts *)
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M KTxr)|].
  split; [apply kp_apart_low; [unfold LA_TEXTS; lia | unfold LA_TEXTS, LA_G_NL, TEXTS_N; lia | exact HspK | exact Hsa0]|].
  split.
  { intros i Hi. pose proof (kp_forallb_seq _ _ KTx (Z.to_nat i) ltac:(unfold TEXTS_N in Hi; lia)) as Hx.
    cbv beta zeta in Hx. apply andb_prop in Hx as [Hw Hs].
    exists (fst (nth (Z.to_nat i) KP_TEXTS (0, []))). rewrite Z2Nat.id in Hw by lia.
    split; [exact (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw)|].
    exact (KSTR _ _ Hs). }
  split; [exact (KSTR _ _ KStrE)|].
  split; [exact (KSTR _ _ KStrX)|].
  (* long_alias *)
  split.
  { destruct Hla as ((la & (Hlab & Hlaw) & Hlal) & Hnul & (sl & (Hslb & _) & Hsll)).
    exists la, sl. split; [|split; [exact Hlal|]; split; [unfold LONG_ALIAS_SIZE; exact Hslb | exact Hsll]].
    split.
    - destruct Hlab as (H0 & H1 & H2). split; [exact H0|]. rewrite length_app. cbn [length].
      split; [unfold LA_LONG_ALIAS in *; lia|]. intros i Hi.
      destruct (Nat.lt_ge_cases i (length la)) as [Hil | Hil].
      + rewrite nth_error_app1 by exact Hil. exact (H2 i Hil).
      + assert (Hi300 : i = length la) by lia. subst i.
        rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error].
        rewrite Hlal. pose proof (Hnul 0%nat ltac:(lia)) as N0. cbn [Z.of_nat] in N0. rewrite Z.add_0_r in N0.
        rewrite N0. reflexivity.
    - assert (Hw : forall (m' : word -> option byte) a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 ->
                 writable_at SEGS m' a) by (rewrite HSEGS; exact LA_LONG_ALIAS_writable).
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hw. lia. }
  split; [rewrite ard_aview; exact (kp_ra B TB ly S _ _ _ M KLar)|].
  split; [rewrite ard_aview; exact (kp_hull B TB ly S _ _ _ M KLah)|].
  split; [unfold apart_frame, LA_LONG_ALIAS, LONG_ALIAS_SIZE; left; lia|].
  (* the interface names *)
  intros tab i nm ix p Hat Hnth Hp.
  pose proof Hat as (Hn1 & _ & Hent). pose proof Htab as (Ht1 & _ & Htent).
  assert (HL : length tab = 64%nat) by (rewrite <- lf_tab_len; apply Nat2Z.inj; congruence).
  assert (Hi64 : (i < 64)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hnth; discriminate).
  destruct (Hent i nm ix Hnth) as (_ & p1 & Hp1 & _ & Hsn1 & _).
  destruct (nth_error lf_tab i) as [[nm0 ix0]|] eqn:Hn0;
    [| exfalso; apply nth_error_None in Hn0; rewrite lf_tab_len in Hn0; lia].
  destruct (Htent i nm0 ix0 Hn0) as (_ & p0 & Hp0 & _ & Hsn0 & _).
  destruct (Hifp (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hqlo & Hqhi).
  pose proof (kp_vm8_mod _ _ _ _ _ Hp1 Hqq) as E1.
  pose proof (kp_vm8_mod _ _ _ _ _ Hp0 Hqq) as E0.
  pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as Ep.
  assert (R1 : 0 <= p1 < 2 ^ 64).
  { destruct Hsn1 as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
  assert (R0 : 0 <= p0 < 2 ^ 64).
  { destruct Hsn0 as ((A1 & A2 & _) & _). rewrite length_app in A2. cbn [length] in A2. lia. }
  rewrite (Z.mod_small p1) in E1 by exact R1. rewrite (Z.mod_small p0) in E0 by exact R0.
  assert (E10 : p1 = p0) by congruence. rewrite E10 in Hsn1.
  pose proof (kp_acstr_unique _ _ _ _ _ Hsn1 Hsn0) as Enm. subst nm.
  assert (Hlen0 : (length nm0 <= 11)%nat).
  { pose proof lf_tab_names_short as Hs. rewrite forallb_forall in Hs.
    specialize (Hs (nm0, ix0) (nth_error_In _ _ Hn0)). apply Nat.leb_le in Hs. exact Hs. }
  apply (kp_apart_name regs p (qq mod 2 ^ 64) (Z.of_nat (length nm0) + 1) Ep ltac:(lia)); [| exact HspK | exact Hsa0 | exact Ha47].
  destruct (Z_lt_le_dec (Z.of_nat i) 60) as [Hlt | Hge].
  - right. rewrite (Hqlo Hlt).
    assert (Hk : 0 <= Z.of_nat i + Z.of_nat i / 15 <= 63) by lia.
    rewrite Z.mod_small by (unfold LA_G_NAMES; lia).
    unfold LA_G_NAMES, LA_G_NL, NK_SIZE, LA_LONG_ALIAS. lia.
  - left. specialize (Hqhi Hge).
    set (j := (i - 59)%nat).
    assert (Hj : (1 <= j < 5)%nat) by (unfold j; lia).
    pose proof (proj1 (forallb_forall _ _) KOdd j ltac:(apply in_seq; lia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw _].
    pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
    replace (LA_ODD + 8 * (Z.of_nat i - 59)) with (LA_ODD + 8 * Z.of_nat j) in Hqhi by (unfold j; lia).
    pose proof (kp_vm8_mod _ _ _ _ _ Hqhi Hv) as Eq.
    pose proof (proj1 (forallb_forall _ _) kp_odd_low j ltac:(apply in_seq; lia)) as Hlow. cbv beta in Hlow.
    apply andb_prop in Hlow as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    rewrite Eq. rewrite Z.mod_small by (unfold LA_G_NL in L2; lia). lia.
Qed.

(* lf_odd_at and lf_texts_at hold at every memory whose read-only bytes are the image's *)
Lemma lf_odd_texts_of_ro : forall (W : world SEGS) mem,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_odd_at (rdW W mem) /\ lf_texts_at (rdW W mem).
Proof.
  intros W mem HRO.
  assert (KT : kp_tabs_b SEGS (as_owned_static B) (as_errno B) = true)
    by (rewrite HSEGS, (ts_owned B TB), (ts_errno B TB); exact kp_tabs_checks).
  unfold kp_tabs_b in KT. apply andb_prop in KT as [KO KX].
  split.
  - intros i Hi. pose proof (kp_forallb_seq _ _ KO i Hi) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hs].
    destruct (kp_rostr SEGS B (w_H W) mem _ _ HRO Hs) as (Hst & Hp0 & Hro).
    exists (fst (nth i KP_ODD (0, []))).
    replace (nth i lf_odd_strs []) with (map (Z_to_bv 8) (snd (nth i KP_ODD (0, []))))
      by (symmetry; apply kp_odd_nth).
    split; [exact (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ eq_refl eq_refl HRO Hw)|].
    split; [exact Hp0|]. split; [exact Hst | exact Hro].
  - intros i Hi. pose proof (kp_forallb_seq _ _ KX i Hi) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hs].
    destruct (kp_rostr SEGS B (w_H W) mem _ _ HRO Hs) as (Hst & Hp0 & Hro).
    exists (fst (nth i KP_TEXTS (0, []))), (map (Z_to_bv 8) (snd (nth i KP_TEXTS (0, [])))).
    split; [exact (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ eq_refl eq_refl HRO Hw)|].
    split; [exact Hp0|]. split; [exact Hst | exact Hro].
Qed.

(* ==========================================================================
   7. kernel's read set at a kernel call site (aleaf_rd's akb premise)
   ========================================================================== *)

Lemma kp_ard_here : kp_ard_b SEGS (as_owned_static B) (as_errno B) = true.
Proof. rewrite HSEGS, (ts_owned B TB), (ts_errno B TB). exact kp_ard_checks. Qed.

Lemma kp_akb_of_b : forall ly S slo shi a,
  kp_akb_b SEGS (as_owned_static B) (as_errno B) a = true -> akb SEGS B ly S slo shi a.
Proof.
  intros ly S slo shi a H. unfold kp_akb_b in H.
  apply andb_prop in H as [H Herr]. apply andb_prop in H as [Hseg Hown].
  right; right; left. split; [|split].
  - apply existsb_exists in Hseg as (s & Hin & Hs). apply andb_prop in Hs as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hin | lia].
  - intros HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz. apply negb_true_iff in Hown.
    assert (Hx : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) (as_owned_static B) = true)
      by (apply existsb_exists; exists r; split; [exact Hr|];
          apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hx in Hown. discriminate.
  - intros Hx. apply negb_true_iff in Herr.
    assert (Ht : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true)
      by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Ht in Herr. discriminate.
Qed.

Lemma kp_akbs_of_b : forall ly S slo shi p n a,
  kp_akbs_b SEGS (as_owned_static B) (as_errno B) p n = true -> p <= a < p + Z.of_nat n ->
  akb SEGS B ly S slo shi a.
Proof.
  intros ly S slo shi p n a H Ha. apply kp_akb_of_b.
  pose proof (kp_forallb_seq _ _ H (Z.to_nat (a - p)) ltac:(lia)) as Hx. cbv beta in Hx.
  replace (p + Z.of_nat (Z.to_nat (a - p))) with a in Hx by lia. exact Hx.
Qed.

(* a byte of the harness's globals G_HARNESS below errno *)
Lemma kp_akb_G : forall ly S slo shi a, gx_ok SEGS B G_HARNESS -> inG G_HARNESS a -> a < TFIB_ERRNO ->
  akb SEGS B ly S slo shi a.
Proof.
  intros ly S slo shi a HG Hin Herr. destruct (HG a Hin) as (Hi & Ho).
  right; right; left. split; [exact Hi|]. split; [exact Ho|]. rewrite (ts_errno B TB). lia.
Qed.

(* the string a kp_kstr_b check describes, as acstr_at, with its place *)
Lemma kp_kstr_acstr : forall H (mem : word -> option byte) p l,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS H mem) ->
  kp_kstr_b SEGS (as_owned_static B) (as_errno B) p l = true ->
  acstr_at SEGS (mrestrict H mem) p (map (Z_to_bv 8) l) /\ 0 < p /\ p + Z.of_nat (length l) + 8 <= LA_G_NL.
Proof.
  intros H mem p l HRO Hk. unfold kp_kstr_b in Hk.
  repeat match type of Hk with (_ && _)%bool = true => apply andb_prop in Hk as [Hk ?] end.
  rename Hk into Hp0. apply Z.ltb_lt in Hp0.
  match goal with Hh : (_ <=? LA_G_NL) = true |- _ => apply Z.leb_le in Hh; rename Hh into Hpl8 end.
  match goal with Hh : kp_bytes_b _ _ _ _ _ = true |- _ => rename Hh into Hby end.
  match goal with Hh : forallb _ l = true |- _ => rename Hh into Hnz end.
  split; [|split; [exact Hp0 | exact Hpl8]].
  apply (kp_acstr SEGS _ _ B H mem p l eq_refl eq_refl HRO Hby Hnz); unfold LA_G_NL in *; lia.
Qed.

Lemma lf_kernel_ard : forall cx fp ly S (W : world SEGS) mem mdl k md mk kbs mbs gbs (regs : bvmap 5 word) P N,
  BASEF cx -> JRN cx fp ly S W mem mdl k ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_P) = Some P ->
  rdword (aview SEGS (w_H W) mem) (lf_sp1 cx + LS_N) = Some N ->
  (exists q, 0 <= q <= c_n cx /\ P = c_p cx + q /\ N = c_n cx - q) ->
  aarg regs 0 = lf_sp1 cx + LS_P -> spZ regs = lf_sp1 cx ->
  forall a, kernel_ard SEGS regs (rdW W mem) a -> akb SEGS B ly S (spZ regs - KERNEL_AK) (spZ regs) a.
Proof.
  intros cx fp ly S W mem mdl k md mk kbs mbs gbs regs P N HB HJ HRO HD HP HN (q & Hq & -> & ->) Ha0 Hsp a Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts cx fp ly S W mem mdl k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (_ & _ & _ & _ & Hpn & _).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (Hs1 : sp0 - 416 - 16 <= lf_sp1 cx <= sp0 - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range sp0 ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16) as (R & _).
    unfold LF_MFRAME in R. exact R. }
  pose proof KERNEL_AK_val as HK.
  unfold LS_P, LS_N, LLVMF_STK in *.
  pose proof kp_ard_here as KA. unfold kp_ard_b in KA.
  repeat match type of KA with (_ && _)%bool = true => apply andb_prop in KA as [KA ?] end.
  rename KA into KAe.
  match goal with Hh : kp_akbs_b _ _ _ LA_MSG_CODES _ = true |- _ => rename Hh into KAc end.
  match goal with Hh : kp_akbs_b _ _ _ LA_TEXTS _ = true |- _ => rename Hh into KAt end.
  match goal with Hh : forallb _ (seq 0 11) = true |- _ => rename Hh into KAts end.
  match goal with Hh : kp_akbs_b _ _ _ LA_STR_EMPTY _ = true |- _ => rename Hh into KAse end.
  match goal with Hh : kp_akbs_b _ _ _ LA_STR_X _ = true |- _ => rename Hh into KAsx end.
  match goal with Hh : forallb _ (seq 1 4) = true |- _ => rename Hh into KAodd end.
  pose proof kp_img_here as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with Hh : forallb _ (seq 1 4) = true, Hh2 : forallb _ (seq 1 4) = true |- _ =>
    lazymatch type of Hh with context [kp_kstr_b] => rename Hh into KOdd end end.
  match goal with Hh : kp_kstr_b _ _ _ LA_STR_X _ = true |- _ => rename Hh into KStrX end.
  match goal with Hh : kp_kstr_b _ _ _ LA_STR_EMPTY _ = true |- _ => rename Hh into KStrE end.
  match goal with Hh : forallb _ (seq 0 11) = true, Hh2 : forallb _ (seq 0 11) = true |- _ =>
    lazymatch type of Hh with context [kp_kstr_b] => rename Hh into KTx end end.
  pose proof (eq_refl (as_owned_static B)) as Ho. pose proof (eq_refl (as_errno B)) as He.
  destruct HD as (Hnlk & Hwf & Htab & _ & _ & _ & _ & _ & _ & _ & _ & Hifp & _ & _ & _ & _ & _).
  assert (HE0 : TFIB_ERRNO = 0x631b6c) by reflexivity.
  unfold kernel_ard in Ha.
  destruct Ha as [Hc | [Hin | [Hg | [He0 | [Hcd | [Htt | [Hts | [Hse | [Hsx | [Hla | Hnm]]]]]]]]]].
  - (* the cursor: the real-stack row, above kernel's window *)
    left. rewrite Ha0, Hsp in *. split; [lia | lia].
  - (* the payload *)
    destruct Hin as (wp & wn & Hwp & Hwn & Rwp & Rwn & Hr).
    rewrite Ha0 in Hwp, Hwn.
    pose proof (kp_vm8_mod _ _ _ _ _ Hwp (val_mem_of_rdword SEGS (w_H W) mem _ _ HP)) as Ewp.
    replace (lf_sp1 cx + 280 + 8) with (lf_sp1 cx + 288) in Hwn by lia.
    pose proof (kp_vm8_mod _ _ _ _ _ Hwn (val_mem_of_rdword SEGS (w_H W) mem _ _ HN)) as Ewn.
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HP) as RP.
    pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W) mem) HN) as RN.
    rewrite (Z.mod_small wp) in Ewp by exact Rwp. rewrite (Z.mod_small (c_p cx + q)) in Ewp by exact RP.
    rewrite (Z.mod_small wn) in Ewn by exact Rwn. rewrite (Z.mod_small (c_n cx - q)) in Ewn by exact RN.
    subst wp wn.
    assert (Hnp : 0 < c_n cx) by lia.
    pose proof (lf_input_block cx fp ly S W mem mdl k HB HJ Hnp) as Hib.
    right; left. exists (c_p cx), (c_n cx). split; [exact Hib|].
    assert (Rn : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (c_n cx =? 0) eqn:E; [lia | reflexivity]).
    rewrite Rn. lia.
  - (* g_nl *)
    apply kp_akb_G; [exact HGX | | unfold LA_G_NL, NK_SIZE in Hg; lia].
    unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold NK_SIZE in Hg. lia.
  - (* nl_errno.e *)
    exact (kp_akbs_of_b ly S _ _ _ 24 a KAe He0).
  - (* msg_build.codes *)
    exact (kp_akbs_of_b ly S _ _ _ 16 a KAc Hcd).
  - (* the texts table *)
    exact (kp_akbs_of_b ly S _ _ _ 88 a KAt ltac:(unfold TEXTS_N in Htt; lia)).
  - (* a texts string *)
    destruct Hts as (i & p & s & Hi & Hp & Hs & Hpa).
    unfold TEXTS_N in Hi.
    pose proof (kp_forallb_seq _ _ KTx (Z.to_nat i) ltac:(lia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hks]. rewrite Z2Nat.id in Hw by lia.
    pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
    destruct (kp_kstr_acstr (w_H W) mem _ _ HRO Hks) as (Hst & Hpt0 & Hptl).
    pose proof (kp_vm8_mod _ _ _ _ _ Hp Hv) as Ep.
    assert (Rp : 0 <= p < 2 ^ 64) by (destruct Hs as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
    rewrite (Z.mod_small p) in Ep by exact Rp. rewrite Z.mod_small in Ep by (unfold LA_G_NL in Hptl; lia).
    subst p. pose proof (kp_acstr_unique _ _ _ _ _ Hs Hst) as Es. subst s. rewrite length_map in Hpa.
    pose proof (kp_forallb_seq _ _ KAts (Z.to_nat i) ltac:(lia)) as Hy. cbv beta zeta in Hy.
    exact (kp_akbs_of_b ly S _ _ _ _ a Hy ltac:(lia)).
  - (* .str.1 *)
    destruct Hse as (s & Hs & Hpa).
    destruct (kp_kstr_acstr (w_H W) mem _ _ HRO KStrE) as (Hst & _ & _).
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hst) as Es. subst s. cbn [map length Z.of_nat] in Hpa.
    exact (kp_akbs_of_b ly S _ _ _ 1 a KAse ltac:(lia)).
  - (* .str.8 *)
    destruct Hsx as (s & Hs & Hpa).
    destruct (kp_kstr_acstr (w_H W) mem _ _ HRO KStrX) as (Hst & _ & _).
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hst) as Es. subst s. cbn [map length Z.of_nat] in Hpa.
    exact (kp_akbs_of_b ly S _ _ _ 2 a KAsx ltac:(cbn; lia)).
  - (* long_alias *)
    apply kp_akb_G; [exact HGX | | unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE in Hla; lia].
    unfold inG, G_HARNESS. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd.
    unfold in_zr. cbn [fst snd]. unfold LONG_ALIAS_SIZE in Hla. lia.
  - (* an interface name *)
    destruct Hnm as (kbs' & tab & i & nm & ix & p & Hk' & Hat & Hnth & Hp & Hs & Hpa).
    assert (Ekb : kbs' = kbs).
    { destruct Hk' as ((A1 & _) & L1). destruct Hnlk as ((A2 & _) & L2).
      apply (lf_abytes_unique _ _ _ _ A1 A2). lia. }
    subst kbs'.
    pose proof Hat as (Hn1 & _ & Hent). pose proof Htab as (Ht1 & _ & Htent).
    assert (HL : length tab = 64%nat) by (rewrite <- lf_tab_len; apply Nat2Z.inj; congruence).
    assert (Hi64 : (i < 64)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hnth; discriminate).
    destruct (Hent i nm ix Hnth) as (_ & p1 & Hp1 & _ & Hsn1 & _).
    destruct (nth_error lf_tab i) as [[nm0 ix0]|] eqn:Hn0;
      [| exfalso; apply nth_error_None in Hn0; rewrite lf_tab_len in Hn0; lia].
    destruct (Htent i nm0 ix0 Hn0) as (_ & p0 & Hp0 & _ & Hsn0 & _).
    destruct (Hifp (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hqlo & Hqhi).
    pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as Ep.
    pose proof (kp_vm8_mod _ _ _ _ _ Hp0 Hqq) as E0.
    assert (Rp : 0 <= p < 2 ^ 64) by (destruct Hs as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
    assert (R0 : 0 <= p0 < 2 ^ 64) by (destruct Hsn0 as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
    rewrite (Z.mod_small p) in Ep by exact Rp. rewrite (Z.mod_small p0) in E0 by exact R0.
    assert (Epp : p = p0) by congruence. rewrite Epp in Hs.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hsn0) as Enm. subst nm.
    destruct (Z_lt_le_dec (Z.of_nat i) 60) as [Hlt | Hge].
    + (* g_names *)
      assert (Hlen0 : (length nm0 <= 4)%nat).
      { pose proof lf_tab_gnames_short as Hsh. rewrite forallb_forall in Hsh.
        specialize (Hsh (nm0, ix0)). apply Nat.leb_le. apply Hsh.
        apply (nth_error_In _ i). rewrite nth_error_firstn. destruct (Nat.ltb_spec i 60); [exact Hn0 | lia]. }
      rewrite (Hqlo Hlt) in E0.
      rewrite Z.mod_small in E0 by (unfold LA_G_NAMES; lia).
      assert (Ha2 : LA_G_NAMES <= a < LA_G_NAMES + 512).
      { clear - E0 Hpa Epp Hlen0 Hlt Hi64. unfold LA_G_NAMES in *. subst p. lia. }
      apply kp_akb_G; [exact HGX | | unfold LA_G_NAMES in Ha2; unfold TFIB_ERRNO; lia].
      unfold inG, G_HARNESS. apply Exists_cons_tl. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. exact Ha2.
    + (* odd[1..4] *)
      specialize (Hqhi Hge).
      set (j := (i - 59)%nat).
      assert (Hj : (1 <= j < 5)%nat) by (unfold j; lia).
      pose proof (proj1 (forallb_forall _ _) KOdd j ltac:(apply in_seq; lia)) as Hx. cbv beta zeta in Hx.
      apply andb_prop in Hx as [Hw Hks].
      pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
      replace (LA_ODD + 8 * (Z.of_nat i - 59)) with (LA_ODD + 8 * Z.of_nat j) in Hqhi by (unfold j; lia).
      pose proof (kp_vm8_mod _ _ _ _ _ Hqhi Hv) as Eq.
      destruct (kp_kstr_acstr (w_H W) mem _ _ HRO Hks) as (Hst & Hpt0 & Hptl).
      rewrite Eq in E0. rewrite Z.mod_small in E0 by (unfold LA_G_NL in Hptl; lia).
      rewrite E0 in Hsn0. pose proof (kp_acstr_unique _ _ _ _ _ Hsn0 Hst) as En. subst nm0.
      rewrite length_map in Hpa.
      pose proof (proj1 (forallb_forall _ _) KAodd j ltac:(apply in_seq; lia)) as Hy. cbv beta zeta in Hy.
      exact (kp_akbs_of_b ly S _ _ _ _ a Hy ltac:(lia)).
Qed.

End b.
End a.
