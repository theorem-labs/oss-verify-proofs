(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 327 of its 371 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a7_w3_c.v, with its module paths and module names changed; 922 of its 1017 lines of code are new or changed and 276 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the CLOSE piece of
   segment B7 of reac_segconf_parse_file's walk, b7cl_ok : B7_S_CLOSE B (lib/B/Prog/pf_seg_B7_m.v:
   HA_KWOK n -> HA_UNK n -> H_CLOSE n). The B7 segment lane of the image-B G3 walk owner (a piece sub-lane), 2026-10-30. proves no function
   (kind: segment lemma of reac_segconf_parse_file's walk, piece B7_S_CLOSE of segment B7).
   ADAPTED from the image-A G3 walk owner's image-A A7 segment lane (a working branch: pf_a7_w3_c.v's w3_trim_step for the
   trim call through PaNoChain.cl_callS_wide, pf_a7_w3_k.v's w3_name_str for the string trim leaves) and from image
   B's proved pieces (the B10b segment lane pf_seg_B10b_j.v: the seed and the reading of a written region; the B9 segment lane
   pf_seg_B9_s1.v: a token run to an interceptor call, aj_art_at, the cut after it), re-derived on image B's code.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 15 instructions and the check stub of B#12:
     CLOSE 0x884cc  srli a1,a0,3; add a1,a1,s4; lb a1,0(a1); bnez a1,0x88fa8
                    check B#12 (store1 of *close at a0 = lp + ci; slow arm 0x88fa8-0x88fb0, error call 0x8927c
                    errpath_store1): the token executor's obligation, from b7_addr_buf (buf's 64 shadow cells are 0)
           0x884dc  sb zero,0(a0)        *close = 0: the one byte lp + ci of buf
           0x884e0  beq s7,s10,0x891c8   UBSan trap T13 (s10 = -1, s7 = lp < 2 ^ 47): decided not taken by the
                                         executor from the seed's range fact on s7 and the pinned s10
           0x884e4  addi a0,s7,1; 0x884e8 jal trim (returns at 0x884ec): trim(line + 1), PaNoChain.cl_callS_wide
                                         (trim writes one byte of parse_file's own class-5 frame: the awr_byte arm
                                         in_frames own, own = [(5, pos)])
           0x884ec  mv s3,a0; auipc/addi a1 = .str.6 0x214a0 "segment" (listing object 41); li a2,7; mv a0,s3;
           0x88500  jal the strncasecmp trampoline (returns at 0x88504): RtSeg.astrncasecmp_realizes (ANCASE)
           0x88504  beqz a0,0x88764      0 -> KWOK (HA_KWOK), else UNK 0x88508 (HA_UNK, r_header = F_unknown)
   The cut facts after each step: b7cl_base_move, pf_base rebuilt from every byte off the write set
   b7cl_W = [alloc_ceiling, s1) (the callees' windows) and buf (the store and trim's NUL); the strings in buf from
   the store's byte and trim's post (b7cl_line1_str, b7cl_trim_str).
   Section hypotheses taken: VRO, SSPX (the transport of the literals, the read-only view and the stack-protector
   cells, as pf_seg_B7_k.v's b7k_base_move), SIGP (trim's call target), OBJ (the literal's atom), TL (the errno cell
   aj_art_at keeps apart), TRIM, ANCASE. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaNoChain PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c trim_c reac_segconf_parse_file_c
  SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B7_f pf_seg_B7_d
  pf_seg_B7_r pf_seg_B7_s pf_seg_B7_k pf_seg_B7_ch pf_seg_B7_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== lists and strings ======================================== *)
Lemma b7cl_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.
Lemma b7cl_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
  intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma b7cl_zb_nth_lt : forall (l : list Z) i, (i < length l)%nat ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = Z_to_bv 8 (nth i l 0).
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth1 by (rewrite length_map; exact Hi).
  change ZB0 with (Z_to_bv 8 0). apply map_nth.
Qed.
Lemma b7cl_zb_nth_end : forall (l : list Z) i, length l = i ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = seg_spec.ZERO.
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Hi, Nat.sub_diag. reflexivity.
Qed.
(* the bytes 1 .. ci - 1 of the line: the header's text between '[' and ']' *)
Lemma b7cl_slice_len : forall (l : list Z) ci, (1 <= ci)%nat -> (ci <= length l)%nat ->
  length (slice 1 ci l) = (ci - 1)%nat.
Proof. intros l ci H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.
Lemma b7cl_slice_nth : forall (l : list Z) ci k, (k < ci - 1)%nat -> nth k (slice 1 ci l) 0 = nth (S k) l 0.
Proof.
  intros l ci k Hk. unfold slice. rewrite nth_firstn.
  destruct (Nat.ltb_spec k (ci - 1)) as [_|]; [|lia].
  rewrite b7cl_nth_skipn. reflexivity.
Qed.
Lemma b7cl_slice_nul : forall (l : list Z) ci, ~ In 0 l -> ~ In 0 (slice 1 ci l).
Proof. intros l ci H. unfold slice. exact (nulfree_firstn _ _ (nulfree_skipn _ _ H)). Qed.

(* the string trim leaves at p + lead after trim(p) of the C string s: its bytes and NUL are trim's post (sa_bytes at
   p of the first lead + |r_trim s| bytes of s, then a NUL); the bytes after the NUL up to the next 8-byte boundary
   are s's own bytes or its slack, which trim did not write (KEEP). pf_a7_w3_k.v's w3_name_str for any string. *)
Lemma b7cl_trim_str : forall segs H mem H' mem' p s,
  sa_str (aview segs H mem) p s ->
  sa_bytes (aview segs H' mem') p
    (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) ->
  (forall a, p + Z.of_nat (seg_spec.trim_lead s + length (r_trim s)) < a ->
     a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
     aview segs H' mem' a = aview segs H mem a) ->
  sa_str (aview segs H' mem') (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s).
Proof.
  intros segs H mem H' mem' p s HS HB HK.
  pose proof HS as ((HZ & HN) & HT).
  destruct (L_trim_holds s HN) as (HL & HE & HNN).
  set (lead := seg_spec.trim_lead s) in *.
  set (nm := r_trim s) in *.
  assert (HR : forall j, (j <= length s)%nat -> 0 <= nth j s 0 < 256).
  { intros j Hj. exact (sa_aview_rng _ _ _ _ _ (b7cl_zs_nth _ p s j HZ Hj)). }
  assert (HBL : length (seg_spec.zb (firstn (lead + length nm) s) ++ [seg_spec.ZERO]) = S (lead + length nm)).
  { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn. cbn [length]. lia. }
  split; [split|].
  - intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    replace (p + Z.of_nat lead + Z.of_nat i) with (p + Z.of_nat (lead + i)) by lia.
    rewrite (HB (lead + i)%nat) by (rewrite HBL; lia). f_equal.
    destruct (Nat.lt_ge_cases i (length nm)) as [Hl | Hg].
    + rewrite (b7cl_zb_nth_lt _ (lead + i)) by (rewrite length_firstn; lia).
      rewrite nth_firstn.
      destruct (Nat.ltb_spec (lead + i) (lead + length nm)) as [_|]; [|lia].
      rewrite (app_nth1 nm [0] 0 Hl).
      assert (Ei : nth i nm 0 = nth (lead + i) s 0).
      { rewrite HE at 1. rewrite nth_firstn.
        destruct (Nat.ltb_spec i (length nm)) as [_|]; [|lia]. apply b7cl_nth_skipn. }
      rewrite Ei. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
    + assert (Hi' : i = length nm) by lia. subst i.
      rewrite (b7cl_zb_nth_end _ (lead + length nm)) by (rewrite length_firstn; lia).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - exact HNN.
  - intros x Hx.
    set (e := p + Z.of_nat lead + Z.of_nat (length nm)) in *.
    set (E := p + Z.of_nat (length s)) in *.
    assert (HeE : e <= E) by (subst e E; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
    pose proof (Z.div_mod E 8 ltac:(lia)) as DE. pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as ME.
    pose proof (Z.div_le_mono e E 8 ltac:(lia) HeE) as Dm.
    rewrite HK by (subst e E; lia).
    destruct (Z_le_gt_dec x E) as [Hle | Hgt].
    + replace x with (p + Z.of_nat (Z.to_nat (x - p))) by lia.
      rewrite (b7cl_zs_nth _ p s (Z.to_nat (x - p)) HZ) by lia. discriminate.
    + unfold sa_tail in HT. apply HT. lia.
Qed.

(* the C string trim gets at 0x884e8: line + 1 after `*close = 0` at line + ci (0x884dc). Its bytes are the line's
   bytes 1 .. ci - 1, read where the store left the line alone; its NUL is the byte the store wrote; the bytes
   after it up to the next 8-byte boundary are the line's ']' slot, NUL or slack. *)
Lemma b7cl_line1_str : forall (rd rd' : reader) lp (l : list Z) ci,
  sa_str rd lp l -> (1 <= ci)%nat -> S ci = length l ->
  (forall a, lp <= a < lp + Z.of_nat (length l) + 8 -> a <> lp + Z.of_nat ci -> rd' a = rd a) ->
  rd' (lp + Z.of_nat ci) = Some 0 ->
  sa_str rd' (lp + 1) (slice 1 ci l).
Proof.
  intros rd rd' lp l ci ((HZ & HN) & HT) Hc1 Hcl K Hw.
  pose proof (b7cl_slice_len l ci Hc1 ltac:(lia)) as HSL.
  split; [split|].
  - intros i Hi. rewrite length_app, HSL in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (ci - 1)) as [Hl | Hg].
    + rewrite app_nth1 by (rewrite HSL; exact Hl). rewrite b7cl_slice_nth by exact Hl.
      rewrite K by lia.
      replace (lp + 1 + Z.of_nat i) with (lp + Z.of_nat (S i)) by lia.
      apply (b7cl_zs_nth rd lp l (S i) HZ). lia.
    + assert (i = ci - 1)%nat as -> by lia. rewrite app_nth2 by (rewrite HSL; lia). rewrite HSL, Nat.sub_diag.
      cbn [nth]. replace (lp + 1 + Z.of_nat (ci - 1)) with (lp + Z.of_nat ci) by lia. exact Hw.
  - exact (b7cl_slice_nul l ci HN).
  - rewrite HSL. replace (lp + 1 + Z.of_nat (ci - 1)) with (lp + Z.of_nat ci) by lia.
    intros x Hx. rewrite K by lia.
    set (e := lp + Z.of_nat ci) in *.
    set (E := lp + Z.of_nat (length l)) in *.
    assert (HeE : E = e + 1) by (subst e E; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
    pose proof (Z.div_mod E 8 ltac:(lia)) as DE. pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as ME.
    pose proof (Z.div_le_mono e E 8 ltac:(lia) ltac:(lia)) as Dm.
    destruct (Z_le_gt_dec x E) as [Hle | Hgt].
    + replace x with (lp + Z.of_nat (Z.to_nat (x - lp))) by lia.
      rewrite (b7cl_zs_nth _ lp l (Z.to_nat (x - lp)) HZ) by lia. discriminate.
    + unfold sa_tail in HT. apply HT. lia.
Qed.

Lemma b7cl_rg : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Ltac b7cl_in := cbn [In app]; repeat first [left; reflexivity | right].
Lemma b7cl_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b7cl_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b7cl_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
  intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* a reader at a reads the byte at a mod 2 ^ 64 (mbyte goes through Z_to_bv 64) *)
Lemma b7cl_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
  intros segs H m a. unfold aview, mbyte.
  replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.

(* ======================================== the seeds ======================================== *)
(* s10 = x26 = -1 as the executor reads it: the word 2 ^ 64 - 1 (the trap test T13's operand) *)
Definition b7cl_M1 : Z := 18446744073709551615.
Lemma b7cl_m1 : w64 (-1) = w64 b7cl_M1.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. Qed.
(* CLOSE 0x884cc: every register its own atom but s10, pinned to the word -1 (so that the executor decides the trap
   test T13 `beq s7,s10` from the range fact of s7); the one region is the byte `sb zero,0(a0)` writes, writable, on
   a0's atom; s4 = SHADOW_OFF (atom 20) is the shadow base of the check B#12 *)
Definition b7cl1_regs : list sv := sr_set sr_atoms 26%bv (SLit b7cl_M1).
Definition b7cl1_regions : smem := [YP09.mkRegion (Some 10%nat) 0 1 0 1 []].
Definition b7cl1_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (23%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0)] [] [].
Definition b7cl1_ss : sstate := mkSS B7_CLOSE b7cl1_regs b7cl1_regions None b7cl1_facts.
Definition b7cl_Bx : sv := SOff 20 0.
(* the shadow entry of the byte the store writes (trim_f.v's tf_SH): the write window of a0's region meets the
   shadow band's span, so cells_safe_b asks for it *)
Definition b7cl1_SH : list shent := [mkSHE 10 0 1].
(* the registers the run CLOSE -> the jal of trim does not write *)
Definition b7cl1_kept : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 27].
(* trim returns at 0x884ec, strncasecmp at 0x88504 *)
Definition B7_CL_RT : Z := AF_reac_segconf_parse_file + 0x6b4.
Definition B7_CL_RN : Z := AF_reac_segconf_parse_file + 0x6cc.
(* 0x884ec (trim's return) and 0x88504 (strncasecmp's return): every register its own atom, no region, no fact *)
Definition b7cl2_ss : sstate := mkSS B7_CL_RT sr_atoms [] None (mkFacts [] [] []).
Definition b7cl3_ss : sstate := mkSS B7_CL_RN sr_atoms [] None (mkFacts [] [] []).
(* 0x884ec writes s3 and a0 .. a2; 0x88504 writes nothing *)
Definition b7cl2_kept : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27].
Definition b7cl3_kept : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma b7cl_pcs : seg_text + B7_CL_RT = 0x884ec /\ seg_text + B7_CL_RN = 0x88504.
Proof. vm_compute. split; reflexivity. Qed.
(* the environment of two runs agrees below 32 with the register file both were seeded from *)
Lemma b7cl_ag_ew : forall (E1 E2 : env) (rr : bvmap 5 word) n z,
  env_agree 32 (Ereg rr []) E1 -> env_agree 32 (Ereg rr []) E2 -> (n < 32)%nat ->
  ew E1 n = z -> ew E2 n = z.
Proof.
  intros E1 E2 rr n z H1 H2 Hn H. rewrite (proj1 H2 n Hn), <- (proj1 H1 n Hn). exact H.
Qed.
Lemma b7cl_u0 : forall (r : word), bv_unsigned r = 0 <-> r = w64 0.
Proof.
  intros r. split.
  - intros H. apply bv_eq. rewrite H. symmetry. apply (b7cl_w64_u 0). lia.
  - intros ->. apply (b7cl_w64_u 0). lia.
Qed.
Lemma b7cl_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the denotation of a register term over atoms of known value *)
Ltac b7cl_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?b7cl_w64_off, ?alu64_add_lit, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [reflexivity | f_equal; lia].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis TL : PALib B.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* ======================================== the cut facts across a write ======================================== *)
(* the bytes a step of the piece may write: the callees' windows below s1 (above alloc_ceiling) and buf *)
Definition b7cl_W (v : pfv) (pos a : Z) : Prop :=
  (alloc_ceiling <= a < pf_s1 v) \/ (b7_buf v pos <= a < b7_buf v pos + 512).
Definition b7cl_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ b7cl_W v pos a -> rd' a = rd a.
(* the keep of a step that writes only below s1 and above the allocator's ceiling (an interceptor call, a run that
   writes nothing): buf is kept too *)
Definition b7cl_keptL (v : pfv) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < pf_s1 v) -> rd' a = rd a.
Lemma b7cl_keptL_W : forall v pos rd rd', b7cl_keptL v rd rd' -> b7cl_kept v pos rd rd'.
Proof. intros v pos rd rd' K a Ha Hw. apply K; [exact Ha|]. intros Hn. apply Hw. left. exact Hn. Qed.
(* a C string kept where its bytes, its NUL and its slack are kept *)
Lemma b7cl_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall a, p <= a < p + Z.of_nat (length s) + 8 -> rd' a = rd a) -> sa_str rd' p s.
Proof.
  intros rd rd' p s ((HZ & HN) & HT) K. split; [split; [|exact HN]|].
  - intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'; cbn [length] in Hi'.
    rewrite K by lia. exact (HZ i Hi).
  - intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
    rewrite K by lia. exact (HT x Hx).
Qed.
Lemma b7cl_kept_trans : forall v pos rd1 rd2 rd3,
  b7cl_kept v pos rd1 rd2 -> b7cl_kept v pos rd2 rd3 -> b7cl_kept v pos rd1 rd3.
Proof. intros v pos rd1 rd2 rd3 H12 H23 a Ha Hw. rewrite (H23 a Ha Hw). exact (H12 a Ha Hw). Qed.

(* the part of pf_base the call-site lemmas read *)
Lemma b7cl_st : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b7_st B v pos lyc Sc Wc memc mdc.
Proof.
  intros v pos lyc Sc Wc rX memc mdc (CX & (HJ & Hly & _ & HP & _) & OBJ0 & _ & FSH).
  constructor; [exact CX | exact HJ | exact Hly | exact HP | exact OBJ0 | exact FSH].
Qed.

(* the numbers of a cut state *)
Lemma b7cl_geo : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + 12832 <= pf_sp0 v /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ (pf_s1 v - pf_sp0 v) mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\ alloc_ceiling < 2 ^ 47 /\
  pf_sp0 v <= 2 ^ 47.
Proof.
  intros v pos lyc Sc Wc rX memc mdc HB.
  pose proof (b7cl_st v pos lyc Sc Wc rX memc mdc HB) as Hst.
  destruct (b7_stk B v pos lyc Sc Wc memc mdc Hst) as (Hsp16 & Hceil & Hslo & _ & Hs1 & Ho16).
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc Hst) as (F1 & F2 & _ & F4).
  destruct (b7k_cx B v (proj1 HB)) as (_ & _ & _ & _ & _ & _ & H47 & _).
  pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in Hslo.
  pose proof YM05.alloc_ceiling_lt as Hac.
  repeat split; lia.
Qed.

(* pf_base after a step that kept every byte off b7cl_W, with the journal it returned at the same layout, the frame
   state changed at most (set_fs), the live blocks permuted, the six registers of pf_fi kept: pf_seg_B7_k.v's
   b7k_base_move with buf's bytes free *)
Lemma b7cl_base_move : forall v pos lyc Sc Wc rX memc mdc sc S2 (W2 : world SEGS) regs2 mem2 md2,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc S2 W2 mem2 md2 0 ->
  (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
  b7cl_kept v pos (rdW Wc memc) (rdW W2 mem2) ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc S2 W2 regs2 mem2 md2 sc.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc S2 W2 regs2 mem2 md2 (CX & FI & OBJ0 & SL & FSH) HJ2 (f2 & HS2) HP2 K KR.
  destruct (b7k_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
  destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
  pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
  destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
  destruct OBJ0 as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
  pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
  pose proof YM05.alloc_ceiling_lt as Hac.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
  rewrite E5 in HFc, HFapp.
  (* the bytes the step kept *)
  assert (K1 : forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha. apply K; [lia|]. unfold b7cl_W, b7_buf, PF_O_BUF. lia. }
  assert (KF : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> ~ (b7_buf v pos <= a < b7_buf v pos + 512) ->
    rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha Hb. apply K; [lia|]. unfold b7cl_W. lia. }
  assert (KH : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> rdW W2 mem2 a = rdW Wc memc a).
  { intros b m a Hb Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hcl & _).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE, E5 in Hd.
    apply K; [lia|]. unfold b7cl_W, b7_buf, PF_O_BUF. lia. }
  assert (KI : forall a, in_img SEGS a -> rdW W2 mem2 a = rdW Wc memc a).
  { intros a Hi. pose proof (pa_img_range a Hi) as Hr.
    pose proof (frm_img SEGS B LAWS lyc Sc Wc memc mdc 5 pos a HAR Hfin) as Hf. rewrite HFE, E5 in Hf.
    unfold kImgEnd in Hr. apply K; [lia|]. unfold b7cl_W, b7_buf, PF_O_BUF.
    intros [W|W]; [lia | apply Hf; [lia | exact Hi]]. }
  assert (KS : forall i, 0 <= i < 256 -> rdW W2 mem2 (pf_SH v pos + i) = rdW Wc memc (pf_SH v pos + i)).
  { intros i Hi. unfold pf_SH, shadow_addr.
    pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
    apply K; [unfold SHADOW_OFF; lia|]. intros [W|W]; [unfold SHADOW_OFF in W; lia|].
    apply (b7k_band_not_app (pf_F v pos) 2048 (SHADOW_OFF + pf_F v pos / 8 + i) HFapp); [unfold SHADOW_OFF; lia|].
    unfold b7_buf, PF_O_BUF in W. lia. }
  assert (K3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) by (intros a Ha _ _; exact (KI a Ha)).
  split; [exact CX|].
  split.
  { split; [exact HJ2|]. split; [exact Hly|].
    split; [exists f2; rewrite HS2, HSf; reflexivity|].
    split; [exact (Permutation_trans HP2 HPerm)|].
    split.
    { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
      pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
      unfold PF_SAVED in Hj13. cbn [length] in Hj13.
      apply K1. lia. }
    split.
    { rewrite <- HFLW. apply rdword_ext. intros k Hk. rewrite E5. apply KF; [lia|]. unfold b7_buf, PF_O_BUF. lia. }
    split; [exact HFRM|].
    split; [exact HTF|].
    split.
    { apply (b7k_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
        [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
      intros a Ha. apply K1. exact Ha. }
    unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
    rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
    cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
  split.
  { destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
      as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
    assert (HT2 : sa_heap B lyc S2 (p_t v) (Z.of_nat (length (p_s v)) + 1))
      by exact (b7k_heap_perm B _ _ _ _ _ _ HP2 HT).
    assert (HC2 : sa_heap B lyc S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b7k_heap_perm B _ _ _ _ _ _ HP2 HC).
    split.
    { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
      - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
        rewrite (KH bt mt) by (exact Hint || lia). exact (Hz i Hi).
      - intros x Hx. apply (AR_block_word_vis SEGS B lyc S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
        + exact (Permutation_in _ (Permutation_sym HP2) Hint).
        + lia.
        + lia. }
    split; [exact (b7k_heap_addr B lyc S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
    split; [exact HT2|].
    split; [exact (b7k_heap_addr B lyc S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
    split; [exact HC2|].
    split; [exact (b7k_cat_move B _ W2 mem2 CAT K3)|].
    split; [intros x Hx; exact (b7k_lit_move B _ W2 mem2 _ _ (LITS x Hx) K3)|].
    split; [intros a Hro Ho He; rewrite (KI a (b7k_in_roP_img VRO a Hro)); exact (ROD a Hro Ho He)|].
    exact (SSPX lyc S2 W2 mem2 md2 HAR2). }
  split.
  { apply (b7k_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b7k_PF_SL_offs v pos)); [lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  intros i Hi. rewrite KS by lia. exact (FSH i Hi).
Qed.

(* c's bytes and cur_name kept off b7cl_W *)
Lemma b7cl_st0_move : forall v pos lyc Sc Wc rX memc mdc (rd' : reader) cf nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b7cl_kept v pos (rdW Wc memc) rd' ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos rd' cf nm k.
Proof.
  intros v pos lyc Sc Wc rX memc mdc rd' cf nm k HB K ((bs & Hbs & Henc) & (f & Hf & Hfe) & HN).
  destruct (b7cl_geo v pos lyc Sc Wc rX memc mdc HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof HB as (CX & FI & OBJ0 & _).
  destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc FI) as (Hfin & _ & _ & _ & _ & HFE).
  pose proof (proj1 (proj1 FI)) as HAR.
  destruct OBJ0 as (_ & _ & _ & _ & (b & m & Hb & H1 & H2) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
  split; [|split; [|exact HN]].
  - exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
    rewrite K; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
    unfold b7cl_W, b7_buf, PF_O_BUF. unfold seg_spec.SEG_C_SIZE in *. lia.
  - exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
    rewrite K; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
    unfold b7cl_W, b7_buf, PF_O_BUF, PF_O_CN. lia.
Qed.

(* the registers of a cut: every one of PF_RL, PF_RM and pf_fi's list is callee-saved *)
Lemma b7cl_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
  intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
  rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.

(* the six registers of pf_fi at a call (pf_rg states them at Z_to_bv 5 r, the code at the bv literal) *)
Lemma b7cl_fi_get : forall v pos lyc Sc Wc rX memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  getr rX 2 = w64 (pf_s1 v) /\ getr rX 3 = w64 (as_gp B) /\ getr rX 4 = w64 (as_tp B) /\
  getr rX 8 = w64 (pf_sp0 v) /\ getr rX 9 = w64 (pf_s1 v) /\ getr rX 20 = w64 SHADOW_OFF.
Proof.
  intros v pos lyc Sc Wc rX memc mdc sc (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG) & _).
  split; [apply (b7cl_bvr _ 2%bv 2); [reflexivity | exact (b7cl_rg rX _ 2 _ HRG ltac:(b7cl_in))]|].
  split; [apply (b7cl_bvr _ 3%bv 3); [reflexivity | exact (b7cl_rg rX _ 3 _ HRG ltac:(b7cl_in))]|].
  split; [apply (b7cl_bvr _ 4%bv 4); [reflexivity | exact (b7cl_rg rX _ 4 _ HRG ltac:(b7cl_in))]|].
  split; [apply (b7cl_bvr _ 8%bv 8); [reflexivity | exact (b7cl_rg rX _ 8 _ HRG ltac:(b7cl_in))]|].
  split; [apply (b7cl_bvr _ 9%bv 9); [reflexivity | exact (b7cl_rg rX _ 9 _ HRG ltac:(b7cl_in))]|].
  apply (b7cl_bvr _ 20%bv 20); [reflexivity | exact (b7cl_rg rX _ 20 _ HRG ltac:(b7cl_in))].
Qed.

(* the byte a run wrote into a one-byte written region (trim_f.v's tr_wbyte at a call state, st_ok) *)
Lemma b7cl_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok SEGS E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
  intros E ss ms H n i Pz v HS Hn HP.
  pose proof (st_ok_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
  pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
  cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
  apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* ======================= the seed at CLOSE and the run to the jal of trim ======================= *)
Lemma b7cl1_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc a0 lp,
  getr rX 10 = w64 a0 -> getr rX 23 = w64 lp -> getr rX 20 = w64 SHADOW_OFF -> getr rX 26 = w64 (-1) ->
  4096 <= a0 <= 2 ^ 47 - 1 -> 4096 <= lp <= 2 ^ 47 - 1 -> apresent (w_H Wc) memc a0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b7cl1_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B7_CLOSE)) memc (seg_rom SEGS))).
Proof.
  intros Wc rX memc a0 lp R10 R23 R20 R26 Ha0 Hlp Hpr.
  set (E := Eimg (Ereg rX [])).
  assert (E10 : ew E 10 = Z_to_bv 64 a0)
    by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 10 10%bv eq_refl); exact R10).
  assert (E23 : ew E 23 = Z_to_bv 64 lp)
    by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 23 23%bv eq_refl); exact R23).
  assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 20 20%bv eq_refl); exact R20).
  rewrite restrict_mkst_fx. unfold b7cl1_ss. apply pa_entry_st_ok_full.
  - unfold b7cl1_regs. apply regs_ok_pin;
      [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite R26; apply b7cl_m1].
  - vm_compute. reflexivity.
  - unfold b7cl1_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hpr.
  - cbn. tauto.
  - split; [|split; exact I].
    cbn [b7cl1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10, E23, E20, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

(* CLOSE 0x884cc .. 0x884e8: the check B#12 and the store of the NUL, the trap T13, a0 = line + 1, the jal of trim *)
Lemma b7cl_run1 : forall v pos lyc Sc Wc rX memc mdc lp (l : list Z) ci (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  sa_str (rdW Wc memc) lp l -> pf_inb (b7_buf v pos) lp l ->
  (1 <= ci)%nat -> S ci = length l ->
  getr rX 23 = w64 lp -> getr rX 10 = w64 (lp + Z.of_nat ci) -> getr rX 26 = w64 (-1) ->
  (forall regs1 mem1 md1,
     pf_base B v pos lyc Sc Wc regs1 mem1 md1 PF_SC_LINE ->
     b7cl_kept v pos (rdW Wc memc) (rdW Wc mem1) ->
     (forall r, In r b7cl1_kept -> getr regs1 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
     getr regs1 26 = w64 (-1) ->
     getr regs1 1 = Z_to_bv 64 (BASE + B7_CL_RT) ->
     getr regs1 10 = w64 (lp + 1) ->
     sa_str (rdW Wc mem1) (lp + 1) (slice 1 ci l) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + AF_trim) regs1 mem1 md1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_CLOSE) rX memc mdc) Q.
Proof.
  intros v pos lyc Sc Wc rX memc mdc lp l ci Q HB HLS HLI Hci1 Hcl R23 R10 R26 KC.
  destruct (b7cl_geo v pos lyc Sc Wc rX memc mdc HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof (b7cl_st v pos lyc Sc Wc rX memc mdc HB) as Hst.
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc HFI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  destruct (b7cl_fi_get v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (R2 & R3 & R4 & R8 & R9 & R20).
  pose proof (b7_AR B v pos lyc Sc Wc memc mdc Hst) as HAR.
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (Hal32 & Happ & Hfb & Hsh).
  change (fs_frame_bytes 5) with 2048 in HFc, HFapp, Hfb.
  pose proof HLI as [HI1 HI2].
  set (a0 := lp + Z.of_nat ci) in *.
  assert (HA0B : b7_buf v pos <= a0 < b7_buf v pos + 512) by (unfold a0; lia).
  assert (HA0F : pf_F v pos <= a0 < pf_F v pos + 2048) by (unfold b7_buf, PF_O_BUF in HA0B; lia).
  assert (Ha0r : 4096 <= a0 <= 2 ^ 47 - 1) by (unfold b7_buf, PF_O_BUF in HA0B; lia).
  assert (Hlpr : 4096 <= lp <= 2 ^ 47 - 1) by (unfold b7_buf, PF_O_BUF in HI1, HA0B; lia).
  assert (Hpr : apresent (w_H Wc) memc a0) by (apply (proj1 (Hfb a0 ltac:(rewrite HFE; lia)))).
  pose proof (b7cl1_seed Wc rX memc a0 lp R10 R23 R20 R26 Ha0r Hlpr Hpr) as HS.
  set (E := Eimg (Ereg rX [])) in HS.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
    by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
  assert (HA0 : env_agree 32 (Ereg rX []) E)
    by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E10 : ew E 10 = Z_to_bv 64 a0) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (E23 : ew E 23 = Z_to_bv 64 lp) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
  assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (U10 : bv_unsigned (ew E 10) = a0) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (UB : U E b7cl_Bx = SHADOW_OFF)
    by (unfold b7cl_Bx; apply (U_atom E 20 SHADOW_OFF E20); unfold SHADOW_OFF; lia).
  assert (UA : U E (SOff 10 0) = a0) by (apply (U_atom E 10 a0 E10); lia).
  destruct (b7_addr_buf B v pos lyc Sc Wc memc mdc a0 1 Hst ltac:(lia) ltac:(lia) ltac:(lia))
    as (_ & _ & _ & HRA & _).
  assert (SHOK : sh_ok SEGS b7cl_Bx b7cl1_SH E (mrestrict (w_H Wc) memc)).
  { unfold sh_ok, b7cl1_SH. apply Forall_cons; [|apply Forall_nil].
    eapply (shent_ok_of_range SEGS (w_H Wc) memc E b7cl_Bx 10%nat a0 1 a0 0 1 HRA UB UA); [lia | lia |].
    intros x Hx Hb. refine (b7k_band_not_app (pf_F v pos) 2048 x HFapp _ _); lia. }
  assert (HAWR : awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (ablocks B (p_ly v) (p_S v)) (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a0).
  { right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite HFE. change (fs_frame_bytes 5) with 2048. lia. }
  unfold cfg_at. change (w64 (BASE + B7_CLOSE)) with (Z_to_bv 64 (BASE + B7_CLOSE)).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    eapply awr_ok_cons_gen with (n := 10%nat) (b := a0); [reflexivity | exact U10 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. assert (a = a0) as -> by lia. exact HAWR. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
    let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
  (* every byte but the one the store wrote *)
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> a0 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hne.
    apply (kept_of_frame (segs := SEGS) E (ss_mem b7cl1_ss) (w_H Wc) memc (ms_mem ms) (fun a' => a' = a0) HFr);
      [|exact Ha | exact Hne].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite U10 in Hrr. lia. }
  assert (HW0 : rdW Wc (ms_mem ms) a0 = Some 0).
  { pose proof (b7cl_wbyte _ _ _ _ 10%nat 0%nat a0 (SLit 0) HS ltac:(vm_compute; reflexivity)) as V.
    rewrite V; [reflexivity|]. cbn [extK]. exact U10. }
  assert (KEPT : b7cl_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
  { intros a Ha Hw. apply KM; [exact Ha|]. intros ->. apply Hw. right. exact HA0B. }
  (* the environment and the registers at the call *)
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HA1 : env_agree 32 (Ereg rX []) Ex) by (env_agree_chain HA0) end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b7cl1_kept) HS HA1
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (HKZ : forall r, In r b7cl1_kept -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
    by (intros r Hr; apply HK; apply in_map; exact Hr).
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (26%bv : bv 5) N26.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (X23 : ew Ex 23 = Z_to_bv 64 lp) by exact (b7cl_ag_ew E Ex rX 23 _ HA0 HA1 ltac:(lia) E23) end.
  assert (Q10 : getr (ms_regs ms) 10 = w64 (lp + 1)) by (rewrite N10; b7cl_den).
  assert (Q26 : getr (ms_regs ms) 26 = w64 (-1)) by (rewrite N26; cbn [sv_denot]; symmetry; apply b7cl_m1).
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. apply HKZ. unfold b7cl1_kept. cbn [In] in Hr |- *. tauto. }
  pose proof (b7cl_base_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _ HB HJ
    ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _) KEPT KR) as HB1.
  assert (HSTR1 : sa_str (rdW Wc (ms_mem ms)) (lp + 1) (slice 1 ci l)).
  { apply (b7cl_line1_str (rdW Wc memc) (rdW Wc (ms_mem ms)) lp l ci HLS Hci1 Hcl); [|exact HW0].
    intros a Ha Hne. apply KM; [unfold b7_buf, PF_O_BUF in HI1, HI2; lia | exact Hne]. }
  pmkst HS.
  rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + AF_trim)) mm (seg_rom SEGS)) mdx)
      with (cfg_at SEGS (BASE + AF_trim) rg mm mdx) end.
  apply (KC (ms_regs ms) (ms_mem ms) _ HB1 KEPT HKZ Q26 N1 Q10 HSTR1).
Qed.

(* ======================================== the call of trim (0x884e8) ======================================== *)
(* trim(p) of the C string s in buf, taken with PaNoChain.cl_callS_wide: trim's footprint is the one byte
   trim_end_addr p s, which lies in parse_file's own class-5 frame, so cl_callSF's "footprint in a live block" rule
   does not serve; the awr_byte arm is `in_frames lyc [(5, pos)]`, and the VIS side condition is vacuous (that byte
   lies below alloc_ceiling, never in parse_file's own stack window). *)
Lemma b7cl_trim_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw p s
  (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  b7_trim_call B lyc Sc Wc memc regsc p s ->
  sa_str (rdW Wc memc) p s -> pf_inb (b7_buf v pos) p s ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  spZ regsc = pf_s1 v ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2,
     pf_base B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE ->
     Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
     aregs_preserved regsc regs2 ->
     b7cl_kept v pos (rdW Wc memc) (rdW W2 mem2) ->
     getr regs2 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) ->
     sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + AF_trim) regsc memc mdc) Q.
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw p s Q HB HTC HS HI R1 Hraw Hra4 Hsp KC.
  destruct (b7cl_geo v pos lyc Sc Wc regsc memc mdc HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof (b7cl_st v pos lyc Sc Wc regsc memc mdc HB) as Hst.
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  destruct (b7k_frame B v pos lyc Sc Wc regsc memc mdc HFI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  pose proof STK_values as (STt & _ & _ & SPF & _).
  destruct (b7cl_fi_get v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (R2 & R3 & R4 & R8 & R9 & R20).
  destruct HTC as (HROD & R10 & Hp64 & HTP & HEV).
  destruct (b7_chain B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as [ch1 HCH].
  destruct (b7_win B v pos lyc Sc Wc memc mdc STK_trim Hst ltac:(rewrite STt; unfold ESTACK; lia))
    as (Wn1 & Wn2 & Wn3).
  pose proof HS as ((_ & HNZ) & _).
  destruct (L_trim_holds s HNZ) as (HLL & HLE & HLN).
  pose proof HI as [HI1 HI2].
  change (fs_frame_bytes 5) with 2048 in HFc, HFapp.
  set (e := trim_end_addr p s) in *.
  assert (He : p <= e <= p + Z.of_nat (length s)) by (unfold e, trim_end_addr; lia).
  assert (HeB : b7_buf v pos <= e < b7_buf v pos + 512) by (unfold b7_buf, PF_O_BUF in *; lia).
  assert (HeF : pf_F v pos <= e < pf_F v pos + 2048) by (unfold b7_buf, PF_O_BUF in HeB; lia).
  assert (Hsp' : spZ regsc = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by lia.
  unfold cfg_at.
  eapply SRr_bind.
  { apply (cl_callS_wide B LAWS Wc regsc memc (w64 (BASE + AF_trim)) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      STK_trim [(e, e + 1)] EV_trim (pf_s1 v - pf_sp0 v) raw ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         getr regs2 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) /\
         sa_bytes (rdW W2 mem2) p
           (seg_spec.zb (firstn (seg_spec.trim_lead s + length (r_trim s)) s) ++ [seg_spec.ZERO]) /\
         sa_kept SEGS Wc memc W2 mem2 regsc STK_trim (fun a => a = e) /\
         sa_noalloc B lyc Sc ly2 S2) HJ Hsp' G5).
    - lia.
    - rewrite STt. lia.
    - exact Wn3.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact Hraw.
    - exact Hra4.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite R8, b7cl_w64_u by lia. exact HCH.
    - intros HPRE1. eapply SRr_mono.
      { exact (TRIM fx lyc Sc Wc regsc memc mdc ch1 p s HPRE1 HROD R10 Hp64 HTP HEV). }
      cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
      exists ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
      split; [exact HJ'|]. split; [exact HP' | exact HQ'].
    - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite HFE. change (fs_frame_bytes 5) with 2048. lia.
    - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      exfalso. rewrite SPF in Hw. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP & (H10' & HBY & HKP & HNA)).
  destruct HNA as (HPerm & Hly2 & HSf).
  change (0 + EV_trim) with 0 in HJo. rewrite Hly2 in HJo, HPerm.
  assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) -> a <> e ->
    rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha Hw Hne. apply HKP; [exact Ha | rewrite Hsp; exact Hw | exact Hne]. }
  assert (KEPT : b7cl_kept v pos (rdW Wc memc) (rdW W2 mem2)).
  { intros a Ha Hw. apply HK0; [exact Ha | |].
    - intros Hn. apply Hw. left. lia.
    - intros ->. apply Hw. right. exact HeB. }
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
  { intros r Hr. apply HP. unfold acallee_saved. cbn [In] in Hr. lia. }
  pose proof (b7cl_base_move v pos lyc Sc Wc regsc memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 HB HJo HSf HPerm
    KEPT KR) as HB2.
  assert (HSTR2 : sa_str (rdW W2 mem2) (p + Z.of_nat (seg_spec.trim_lead s)) (r_trim s)).
  { apply (b7cl_trim_str SEGS (w_H Wc) memc (w_H W2) mem2 p s HS HBY).
    intros a Ha1 Ha2.
    assert (Hae : e < a) by (unfold e, trim_end_addr; lia).
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Hm8.
    apply HK0; [unfold b7_buf, PF_O_BUF in *; lia | unfold b7_buf, PF_O_BUF in *; lia | lia]. }
  exact (KC S2 W2 regs2 mem2 md2 HB2 HPerm HP KEPT H10' HSTR2).
Qed.

(* ================================= the call of strncasecmp (0x88500) ================================= *)
Lemma b7cl_zs_segment : seg_spec.zs (seg_spec.zb S_segment) = S_segment.
Proof. vm_compute. reflexivity. Qed.

Lemma b7cl_ncase_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw x l
  (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  sa_str (rdW Wc memc) x l -> pf_inb (b7_buf v pos) x l ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> spZ regsc = pf_s1 v ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 (seg_litA_rc S_segment) -> getr regsc 12 = w64 7 ->
  (forall regs2 mem2 md2,
     pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE ->
     aregs_preserved regsc regs2 ->
     b7cl_keptL v (rdW Wc memc) (rdW Wc mem2) ->
     (getr regs2 10 = w64 0 <-> strncasecmp l S_segment 7 = 0) ->
     SRr SEGS Wc (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIG SS___interceptor_trampoline_strncasecmp)) memc (seg_rom SEGS))
    mdc) Q.
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw x l Q HB HS HI R1 Hraw Hsp R10 R11 R12 KC.
  destruct (b7cl_geo v pos lyc Sc Wc regsc memc mdc HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof (b7cl_st v pos lyc Sc Wc regsc memc mdc HB) as Hst.
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  destruct (b7cl_fi_get v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (R2 & R3 & R4 & R8 & R9 & R20).
  pose proof STK_values as (STt & _ & _ & SPF & _).
  destruct (b7_win B v pos lyc Sc Wc memc mdc (2 * ESTACK) Hst ltac:(unfold ESTACK; lia)) as (Wn1 & Wn2 & Wn3).
  pose proof HS as ((_ & HNZ) & _).
  destruct (b7_ncase_pre_88500 B v pos lyc Sc Wc memc mdc regsc x l Hst Hsp ltac:(rewrite R1; exact Hraw)
    R3 R4 R10 R11 R12 HS HI) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15
    & P16).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
      (SIG SS___interceptor_trampoline_strncasecmp) Wc regsc memc STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      (pf_s1 v - pf_sp0 v) raw _ HJ ltac:(lia) G5 ltac:(lia) ltac:(unfold ESTACK; lia)
      ltac:(rewrite SPF; unfold ESTACK; lia) R1 (fun a (H : False) => False_ind _ H)).
    exact (ANCASE fx lyc Sc Wc regsc memc mdc x (seg_litA_rc S_segment) 7 (seg_spec.zb l)
      (seg_spec.zb S_segment) P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
  assert (KEPT : b7cl_keptL v (rdW Wc memc) (rdW Wc mem2)).
  { intros a Ha Hw. apply HK2; [exact Ha | | tauto]. intros Hn. apply Hw. lia. }
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
  { intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
  assert (HB2 : pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE).
  { apply (b7cl_base_move v pos lyc Sc Wc regsc memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 HB HJ2);
      [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl
      | exact (b7cl_keptL_W v pos _ _ KEPT) | exact KR]. }
  apply (KC regs2 mem2 md2 HB2 HP2 KEPT).
  destruct (b7_astr_of_sa Wc memc x l HS) as (_ & _ & _ & HZSl & _).
  change (map (fun b : byte => bv_unsigned b) (seg_spec.zb l)) with (seg_spec.zs (seg_spec.zb l)) in HQ.
  change (map (fun b : byte => bv_unsigned b) (seg_spec.zb S_segment))
    with (seg_spec.zs (seg_spec.zb S_segment)) in HQ.
  rewrite HZSl, b7cl_zs_segment in HQ.
  change (Z.to_nat 7) with 7%nat in HQ.
  rewrite (b7_ncase_seg l HNZ) in HQ. exact HQ.
Qed.


(* ================= 0x884ec .. 0x88500: s3 = the body, the literal, the jal of strncasecmp ================= *)
Lemma b7cl_seg_atom : forall E, img_env VAL A_LIM E -> ew E 282%nat = w64 (seg_litA_rc S_segment).
Proof.
  intros E HE. rewrite (img_env_atomP E 282%nat HE) by (unfold A_TEXT, A_LIM; lia).
  change 282%nat with (A_OBJ 41). rewrite (OBJ 41%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64. f_equal; vm_compute; reflexivity.
Qed.

Lemma b7cl_run2 : forall v pos lyc Sc Wc rX memc mdc bp (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  getr rX 10 = w64 bp -> 0 <= bp < 2 ^ 64 ->
  (forall regs2 mem2 md2,
     pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE ->
     b7cl_keptL v (rdW Wc memc) (rdW Wc mem2) ->
     (forall r, In r b7cl2_kept -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
     getr regs2 19 = w64 bp -> getr regs2 10 = w64 bp ->
     getr regs2 11 = w64 (seg_litA_rc S_segment) -> getr regs2 12 = w64 7 ->
     getr regs2 1 = Z_to_bv 64 (BASE + B7_CL_RN) ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (SIG SS___interceptor_trampoline_strncasecmp)) mem2
       (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_CL_RT) rX memc mdc) Q.
Proof.
  intros v pos lyc Sc Wc rX memc mdc bp Q HB R10 Hbp KC.
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  set (E := Eimg (Ereg rX [])).
  assert (HS : st_ok_pi SEGS VAL E b7cl2_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B7_CL_RT)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold b7cl2_ss. apply pa_entry_st_ok_full;
      [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
      | split; [exact I | split; exact I]]. }
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
    by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
  assert (HA0 : env_agree 32 (Ereg rX []) E)
    by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E10 : ew E 10 = Z_to_bv 64 bp) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (SHOK : sh_ok SEGS b7cl_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold cfg_at. change (w64 (BASE + B7_CL_RT)) with (Z_to_bv 64 (BASE + B7_CL_RT)).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    apply awr_ok_nil. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
    let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha.
    apply (kept_of_frame (segs := SEGS) E (ss_mem b7cl2_ss) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
  assert (KEPT : b7cl_keptL v (rdW Wc memc) (rdW Wc (ms_mem ms))) by (intros a Ha _; exact (KM a Ha)).
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HA1 : env_agree 32 (Ereg rX []) Ex) by (env_agree_chain HA0) end.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b7cl2_kept) HS HA1
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (HKZ : forall r, In r b7cl2_kept -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
    by (intros r Hr; apply HK; apply in_map; exact Hr).
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12. prreg HS (19%bv : bv 5) N19.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (X10 : ew Ex 10 = Z_to_bv 64 bp) by exact (b7cl_ag_ew E Ex rX 10 _ HA0 HA1 ltac:(lia) E10) end.
  assert (Q10 : getr (ms_regs ms) 10 = w64 bp) by (rewrite N10; b7cl_den).
  assert (Q19 : getr (ms_regs ms) 19 = w64 bp) by (rewrite N19; b7cl_den).
  assert (Q11 : getr (ms_regs ms) 11 = w64 (seg_litA_rc S_segment))
    by (rewrite N11; apply b7cl_seg_atom; exact HEI).
  assert (Q12 : getr (ms_regs ms) 12 = w64 7) by (rewrite N12; reflexivity).
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. apply HKZ. unfold b7cl2_kept. cbn [In] in Hr |- *. tauto. }
  pose proof (b7cl_base_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _ HB HJ
    ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
    (b7cl_keptL_W v pos _ _ KEPT) KR) as HB2.
  pmkst HS.
  apply (KC (ms_regs ms) (ms_mem ms) _ HB2 KEPT HKZ Q19 Q10 Q11 Q12 N1).
Qed.

(* ======================= 0x88504: `beqz a0` -> KWOK 0x88764 or UNK 0x88508 ======================= *)
Lemma b7cl_br_eq0 : forall E n z b, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (z =? 0) = b.
Proof.
  intros E n z b H Hz Hc. rewrite branch_eq_U, (U_atom E n z H Hz), U_lit in Hc by lia. exact Hc.
Qed.

Lemma b7cl_run3 : forall v pos lyc Sc Wc rX memc mdc ans (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  getr rX 10 = w64 ans -> 0 <= ans < 2 ^ 64 ->
  (ans = 0 -> forall regs3 mem3 md3,
     pf_base B v pos lyc Sc Wc regs3 mem3 md3 PF_SC_LINE ->
     b7cl_keptL v (rdW Wc memc) (rdW Wc mem3) ->
     (forall r, In r b7cl3_kept -> getr regs3 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + B7_KWOK) regs3 mem3 md3) Q) ->
  (ans <> 0 -> forall regs3 mem3 md3,
     pf_base B v pos lyc Sc Wc regs3 mem3 md3 PF_SC_LINE ->
     b7cl_keptL v (rdW Wc memc) (rdW Wc mem3) ->
     (forall r, In r b7cl3_kept -> getr regs3 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + B7_UNK) regs3 mem3 md3) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_CL_RN) rX memc mdc) Q.
Proof.
  intros v pos lyc Sc Wc rX memc mdc ans Q HB R10 Hans KK KU.
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  set (E := Eimg (Ereg rX [])).
  assert (HS : st_ok_pi SEGS VAL E b7cl3_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B7_CL_RN)) memc (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold b7cl3_ss. apply pa_entry_st_ok_full;
      [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
      | split; [exact I | split; exact I]]. }
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
    by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
  assert (HA0 : env_agree 32 (Ereg rX []) E)
    by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E10 : ew E 10 = Z_to_bv 64 ans) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
  assert (SHOK : sh_ok SEGS b7cl_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold cfg_at. change (w64 (BASE + B7_CL_RN)) with (Z_to_bv 64 (BASE + B7_CL_RN)).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - (* a0 = 0: KWOK *)
    pose proof (b7cl_br_eq0 E 10 ans true E10 Hans Hc) as L0. apply Z.eqb_eq in L0. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B7_KWOK.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
      apply awr_ok_nil. }
    cbn [ms_mem mkst] in HFr, HG, HF.
    repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
      let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
        apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
          [|exact Ha | tauto] end.
      intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
    assert (KEPT : b7cl_keptL v (rdW Wc memc) (rdW Wc (ms_mem ms))) by (intros a Ha _; exact (KM a Ha)).
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HA1 : env_agree 32 (Ereg rX []) Ex) by (env_agree_chain HA0) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) b7cl3_kept) HS HA1
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    assert (HKZ : forall r, In r b7cl3_kept -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
      by (intros r Hr; apply HK; apply in_map; exact Hr).
    assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
    { intros r Hr. apply HKZ. unfold b7cl3_kept. cbn [In] in Hr |- *. tauto. }
    pose proof (b7cl_base_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _ HB HJ
      ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
      (b7cl_keptL_W v pos _ _ KEPT) KR) as HB3.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
        with (cfg_at SEGS (BASE + B7_KWOK) rg mm mdx) end.
    exact (KK L0 (ms_regs ms) (ms_mem ms) _ HB3 KEPT HKZ).
  - (* a0 <> 0: UNK *)
    pose proof (b7cl_br_eq0 E 10 ans false E10 Hans Hc) as L0. apply Z.eqb_neq in L0. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B7_UNK.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
      apply awr_ok_nil. }
    cbn [ms_mem mkst] in HFr, HG, HF.
    repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
      let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
        apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
          [|exact Ha | tauto] end.
      intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
    assert (KEPT : b7cl_keptL v (rdW Wc memc) (rdW Wc (ms_mem ms))) by (intros a Ha _; exact (KM a Ha)).
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HA1 : env_agree 32 (Ereg rX []) Ex) by (env_agree_chain HA0) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) b7cl3_kept) HS HA1
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    assert (HKZ : forall r, In r b7cl3_kept -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
      by (intros r Hr; apply HK; apply in_map; exact Hr).
    assert (KR : forall r, In r [2; 3; 4; 8; 9; 20] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
    { intros r Hr. apply HKZ. unfold b7cl3_kept. cbn [In] in Hr |- *. tauto. }
    pose proof (b7cl_base_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) _ HB HJ
      ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
      (b7cl_keptL_W v pos _ _ KEPT) KR) as HB3.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
        with (cfg_at SEGS (BASE + B7_UNK) rg mm mdx) end.
    exact (KU L0 (ms_regs ms) (ms_mem ms) _ HB3 KEPT HKZ).
Qed.

(* ======================================== the piece: CLOSE -> KWOK / UNK ======================================== *)
Lemma b7cl_close : forall n, HA_KWOK B n -> HA_UNK B n -> H_CLOSE (fx := fx) B n.
Proof.
  intros n AKWOK AUNK v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci HI.
  destruct HI as ((HB & HMID & HST & HLEN & HRGL) & HLS & HLI & HHD & HCHR & HNUL & HRG).
  destruct (b7cl_geo v pos lyc Sc Wc rX memc mdc HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
  pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
  pose proof pa_base_lo as HBL. pose proof pa_B_ok as (HBa & HBb & _).
  unfold PF_RL, PF_RM in HRGL.
  pose proof HLS as ((_ & HNZ) & _).
  pose proof (b7_ci_pos (pf_tline (p_s v) o) ci HHD HCHR) as Hci1.
  destruct (b7_close_last (pf_tline (p_s v) o) ci HNZ HCHR HNUL) as (Hcilt & Hcl).
  pose proof HLI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
  destruct (L_trim_holds (slice 1 ci (pf_tline (p_s v) o))
    (b7cl_slice_nul (pf_tline (p_s v) o) ci HNZ)) as (HLL & HLE & HLN).
  rewrite (b7cl_slice_len (pf_tline (p_s v) o) ci Hci1 ltac:(lia)) in HLL.
  (* the entry registers *)
  assert (Z2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b7cl_rg rX _ 2 _ HRG0); b7cl_in).
  assert (Z23 : getr rX (Z_to_bv 5 23) = w64 lp) by (apply (b7cl_rg rX _ 23 _ HRG); b7cl_in).
  assert (Z10 : getr rX (Z_to_bv 5 10) = w64 (lp + Z.of_nat ci)) by (apply (b7cl_rg rX _ 10 _ HRG); b7cl_in).
  assert (Z27 : getr rX (Z_to_bv 5 27) = w64 9) by (apply (b7cl_rg rX _ 27 _ HRG); b7cl_in).
  assert (Z24 : getr rX (Z_to_bv 5 24) = w64 32) by (apply (b7cl_rg rX _ 24 _ HRG); b7cl_in).
  assert (Z26 : getr rX (Z_to_bv 5 26) = w64 (-1)) by (apply (b7cl_rg rX _ 26 _ HRGL); b7cl_in).
  (* the two return addresses *)
  assert (ERT : B7_CL_RT = 14124) by (vm_compute; reflexivity).
  assert (ERN : B7_CL_RN = 14148) by (vm_compute; reflexivity).
  assert (HRTb : 0 <= B7_CL_RT < 2 ^ 40) by (rewrite ERT; lia).
  assert (HRNb : 0 <= B7_CL_RN < 2 ^ 40) by (rewrite ERN; lia).
  assert (HretT : YK0s.ret_ok (Z_to_bv 64 (BASE + B7_CL_RT)))
    by (apply ret_ok_codeptr_v; [lia | rewrite ERT; reflexivity]).
  assert (HretT4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + B7_CL_RT)))
    by (rewrite unsigned_lit_small by lia; lia).
  assert (HretN : YK0s.ret_ok (Z_to_bv 64 (BASE + B7_CL_RN)))
    by (apply ret_ok_codeptr_v; [lia | rewrite ERN; reflexivity]).
  (* 0x884cc .. 0x884e8 *)
  apply (b7cl_run1 v pos lyc Sc Wc rX memc mdc lp (pf_tline (p_s v) o) ci _ HB HLS HLI Hci1 Hcl
    (b7cl_bvr rX 23%bv 23 _ eq_refl Z23) (b7cl_bvr rX 10%bv 10 _ eq_refl Z10)
    (b7cl_bvr rX 26%bv 26 _ eq_refl Z26)).
  intros regs1 mem1 md1 HB1 KEPT1 HKZ1 Q26 N1 Q10 HSTR1.
  assert (HINB1 : pf_inb (b7_buf v pos) (lp + 1) (slice 1 ci (pf_tline (p_s v) o))).
  { unfold pf_inb, b7_buf, PF_O_BUF. rewrite (b7cl_slice_len (pf_tline (p_s v) o) ci Hci1 ltac:(lia)). lia. }
  assert (Hsp1 : spZ regs1 = pf_s1 v).
  { unfold spZ. rewrite (b7cl_bvr regs1 2%bv 2 _ eq_refl (HKZ1 2 ltac:(b7cl_in))), Z2.
    apply b7cl_w64_u. lia. }
  (* trim(line + 1) *)
  apply (b7cl_trim_step v pos lyc Sc Wc regs1 mem1 md1 _ (lp + 1) (slice 1 ci (pf_tline (p_s v) o)) _ HB1
    (b7_trim_site_884e8 B v pos lyc Sc Wc mem1 md1 regs1 o lp ci
       (b7cl_st v pos lyc Sc Wc regs1 mem1 md1 HB1) HLI HHD Q10 HSTR1)
    HSTR1 HINB1 N1 HretT HretT4 Hsp1).
  intros S2 W2 regs2 mem2 md2 HB2 HPerm2 HP2 KEPT2 Q10b HSTR2.
  (* the body, in buf *)
  assert (HINBb : pf_inb (b7_buf v pos) (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
    (b7_body (pf_tline (p_s v) o) ci)).
  { unfold pf_inb, b7_buf, b7_body, PF_O_BUF. lia. }
  pose proof HINBb as [HBP1 HBP2]. unfold b7_buf, PF_O_BUF in HBP1, HBP2.
  (* 0x884ec .. 0x88500 *)
  apply (b7cl_run2 v pos lyc S2 W2 regs2 mem2 md2
    (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o)))) _ HB2 Q10b ltac:(lia)).
  intros regs3 mem3 md3 HB3 KEPT3 HKZ3 Q19 Q10c Q11 Q12 N1b.
  assert (Hsp3 : spZ regs3 = pf_s1 v).
  { unfold spZ. rewrite (b7cl_bvr regs3 2%bv 2 _ eq_refl (HKZ3 2 ltac:(b7cl_in))).
    rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), (HKZ1 2 ltac:(b7cl_in)), Z2.
    apply b7cl_w64_u. lia. }
  assert (HSTR3 : sa_str (rdW W2 mem3)
    (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
    (b7_body (pf_tline (p_s v) o) ci)).
  { apply (b7cl_str_keep (rdW W2 mem2) _ _ _ HSTR2). intros a Ha.
    unfold b7_body in HBP2. apply KEPT3; lia. }
  (* strncasecmp(body, "segment", 7) *)
  apply (b7cl_ncase_step v pos lyc S2 W2 regs3 mem3 md3 _
    (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
    (b7_body (pf_tline (p_s v) o) ci) _ HB3 HSTR3 HINBb N1b HretN Hsp3 Q10c Q11 Q12).
  intros regs4 mem4 md4 HB4 HP4 KEPT4 HANS.
  assert (HSTR4 : sa_str (rdW W2 mem4)
    (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
    (b7_body (pf_tline (p_s v) o) ci)).
  { apply (b7cl_str_keep (rdW W2 mem3) _ _ _ HSTR3). intros a Ha.
    apply KEPT4; lia. }
  (* 0x88504: the answer decides KWOK or UNK *)
  apply (b7cl_run3 v pos lyc S2 W2 regs4 mem4 md4 (bv_unsigned (getr regs4 10)) _ HB4
    ltac:(symmetry; apply Z_to_bv_bv_unsigned) (bv_unsigned_in_range 64 _));
  intros Hans regs5 mem5 md5 HB5 KEPT5 HKZ5.
  all: assert (KA : b7cl_kept v pos (rdW Wc memc) (rdW W2 mem5)) by
    (eapply b7cl_kept_trans; [exact KEPT1|];
     eapply b7cl_kept_trans; [exact KEPT2|];
     eapply b7cl_kept_trans; [exact (b7cl_keptL_W v pos _ _ KEPT3)|];
     eapply b7cl_kept_trans; [exact (b7cl_keptL_W v pos _ _ KEPT4)|];
     exact (b7cl_keptL_W v pos _ _ KEPT5)).
  all: assert (HSTR5 : sa_str (rdW W2 mem5)
    (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
    (b7_body (pf_tline (p_s v) o) ci)) by
    (apply (b7cl_str_keep (rdW W2 mem4) _ _ _ HSTR4); intros a Ha;
     apply KEPT5; lia).
  all: assert (KEEP5 : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 27] ->
    getr regs5 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) by
    (intros r Hr;
     rewrite (HKZ5 r ltac:(unfold b7cl3_kept; cbn [In] in Hr |- *; tauto)),
       (HP4 r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)),
       (HKZ3 r ltac:(unfold b7cl2_kept; cbn [In] in Hr |- *; tauto)),
       (HP2 r ltac:(unfold acallee_saved; cbn [In] in Hr; lia));
     exact (HKZ1 r ltac:(unfold b7cl1_kept; cbn [In] in Hr |- *; tauto))).
  all: assert (Q26b : getr regs5 (Z_to_bv 5 26) = w64 (-1)) by
    (rewrite (HKZ5 26 ltac:(unfold b7cl3_kept; b7cl_in)),
       (HP4 26 ltac:(unfold acallee_saved; lia)),
       (HKZ3 26 ltac:(unfold b7cl2_kept; b7cl_in)),
       (HP2 26 ltac:(unfold acallee_saved; lia));
     exact (b7cl_bvr' regs1 26%bv 26 _ eq_refl Q26)).
  all: assert (Q19b : getr regs5 (Z_to_bv 5 19) =
    w64 (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))) by
    (rewrite (HKZ5 19 ltac:(unfold b7cl3_kept; b7cl_in)), (HP4 19 ltac:(unfold acallee_saved; lia));
     exact (b7cl_bvr' regs3 19%bv 19 _ eq_refl Q19)).
  all: assert (HCORE : b7_core B n v pos lyc S2 W2 regs5 mem5 md5 cf nm o ln d) by
    (split; [exact HB5|]; split; [exact HMID|];
     split; [exact (b7cl_st0_move v pos lyc Sc Wc rX memc mdc _ cf nm _ HB KA HST)|];
     split; [exact HLEN|];
     unfold pf_rg, PF_RL, PF_RM; cbn [app];
     repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
     first [ exact Q26b
           | rewrite KEEP5; [first [exact (b7cl_rg rX _ 18 _ HRGL ltac:(b7cl_in))
                                   | exact (b7cl_rg rX _ 21 _ HRGL ltac:(b7cl_in))
                                   | exact (b7cl_rg rX _ 25 _ HRGL ltac:(b7cl_in))
                                   | exact (b7cl_rg rX _ 22 _ HRGL ltac:(b7cl_in))] | b7cl_in] ]).
  - (* the keyword matched: KWOK 0x88764 *)
    assert (HKW : strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0)
      by (apply HANS; apply b7cl_u0; exact Hans).
    apply (AKWOK fx v pos lyc S2 W2 regs5 mem5 md5 cf nm o ln d ci
      (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))).
    split; [exact HCORE|]. split; [exact HCHR|]. split; [exact HNUL|]. split; [exact HKW|].
    split; [exact HSTR5|]. split; [exact HINBb|].
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + exact Q19b.
    + rewrite KEEP5; [exact Z27 | b7cl_in].
    + rewrite KEEP5; [exact Z24 | b7cl_in].
  - (* the keyword did not match: UNK 0x88508 *)
    assert (HKW : strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 <> 0).
    { intros Hq. apply Hans. apply b7cl_u0. apply HANS. exact Hq. }
    apply (AUNK fx v pos lyc S2 W2 regs5 mem5 md5 cf nm o ln d
      (lp + 1 + Z.of_nat (seg_spec.trim_lead (slice 1 ci (pf_tline (p_s v) o))))
      (b7_body (pf_tline (p_s v) o) ci)).
    split; [exact HCORE|]. split; [exact HSTR5|]. split; [exact HINBb|].
    split; [exact (b7_hdr_unknown cf nm (ln + 1) (pf_tline (p_s v) o) ci HCHR HNUL (or_introl HKW))|].
    unfold pf_rg. apply Forall_cons; [cbn [fst snd]; exact Q19b | apply Forall_nil].
Qed.

End x.

(* the piece of pf_seg_B7_m.v at every FP state *)
Theorem b7cl_ok : B7_S_CLOSE B.
Proof. intros f0 n HK HU. exact (b7cl_close (fx := f0) n HK HU). Qed.
End d.
