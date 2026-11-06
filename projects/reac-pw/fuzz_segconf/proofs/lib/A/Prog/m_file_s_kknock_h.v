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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 666 of its 716 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KKNOCKP (KKNOCK 0x86b20 -> KDONE 0x86cd0; the G2 walk owner's
   guide/MF-CUTS-A.md sections 2 and 4): its "knock" branch, from the interface point KK_HIT 0x86b38 of
   lib/A/Prog/m_file_s_kknock_d.v (ieq "knock" returned 1) to KDONE. The LONGP / KKNOCKP segment lane of the G2 walk owner's G2, piece
   the KKNOCKP knock-branch sub-lane: `kk_hit : forall n, (forall fx0, MF_KDONE_stmt (fx := fx0) B n) -> KK_HITX_stmt B n`.

   THE CODE (listing dis/m_file.fuzz_segconf.asan.s):
     0x86b38 `ld a0,40(s1)`             a0 := &c->n_kept = c + 0x23ac
     0x86b3c .. 0x86b50                 the instrumented check of the 4-byte load of n_kept (a load of the shadow byte
                                        at (a0 >> 3) + s2 and a compare; its slow path 0x86e10-0x86e1c and the error
                                        path 0x87030, a call of errpath_load4, which the proof shows is not reached);
                                        s5 := 128(s1) = c, s6 := s8 = line + 1
     0x86b54 `lw a0,0(a0)`              a0 := n_kept = |kept| (at most 8)
     0x86b58 `ld s8,104(s1)`            s8 := FAKE
     0x86b5c `li a1,7`, `blt a1,a0`     n_kept = 8: to 0x86cc4, no store
     0x86b64 .. 0x86b7c                 a0 := 24(s1) + 4 n_kept = &c->kept_knock[n_kept]; the instrumented check of the
                                        4-byte store there (slow path 0x86e44-0x86e50; the error path 0x87040, a call of
                                        errpath_store4, not reached)
     0x86b80 `li a1,1`, `sw a1,0(a0)`   kept_knock[n_kept] = 1
     0x86b88 `j 0x86cc4`
     0x86cc4 `mv a0,s5`, `mv a1,s6`, 0x86ccc `jal m_refuse`, whose return point is KDONE 0x86cd0

   THE PROOF. The seed is m_file_sd.v's mf_seed at KK_HIT, the spill slots made read-only (nothing here stores a
   slot), with a read-only region of the n_kept cell [c + 0x23ac, c + 0x23b0) (atom 33) and the shadow entry of the
   whole block (mf_she_blk, 9236 bytes), which decides the check of the load.
   - n_kept < 8 (kh_hitA): the n_kept chunk is the caller's value atom 52 with the fact [0, 7], so the token run reads
     `lw` as atom 52 and decides the `blt`. The address &kept_knock[n_kept] is the caller's value atom 53 =
     c + 0x238c + 4 n_kept, with a writable region [0, 4) and a shadow entry [0, 8) (inside the block). A token run
     goes to KH_PIN 0x86b70, a0 is re-shaped to atom 53 (ast_ok_pi_set_reg_fp: the same address), and a second
     token run goes to the `jal`; both checks are decided with no obligation. The runs wrote the 4 bytes at atom 53
     only (kept_of_frame) and the final region gives the word 1; the block's bytes are the entry's with those 4 bytes
     replaced (kh_bytes_upd), which encode mcc with the pending knock flag (kh_enc_knock: mconf_encp true);
     kh_keep_k carries mf_core to m_file_k.v's mf_corek true.
   - n_kept = 8 (kh_hitB): the n_kept chunk is the literal 8; one token run to the `jal`, which writes nothing
     (m_file_k.v's mf_keep_run0); the block's encoding holds with the pending flag (kh_enc_full: the pend clause is
     vacuous at |kept| = 8).
   - The call (kh_jal): m_file_rf.v's mf_refuse_step at the `jal` 0x86ccc with knock = true and mcl = mcc; at the
     returned FP state fx1 the continuation is KDONE at fx1 for the next line: line + 1, mf_next p rest, mf_rest rest,
     the model m_refuse mcc (line + 1) true with cur = Some gi (m_file_k.v's mf_loop_next), s5 = c, s6 = line + 1,
     s8 = FAKE.
   Copied lemmas cite their source: commit 96f5e3c9eb4a's lib/A/Prog/m_file_s_hdrb_1.v (its mcx_ and hb_
   lemmas) and m_file_s_hdrb_5.v (its hb5_ lemmas), and m_file_k.v's mf_keep_k (kh_keep_k, the pending flag in its post).
   Section hypotheses, from the shared list of m_file_m.v change 3, verbatim: VOBJS (the seed's literal bridge),
   SIGP, SSP, RELRO and M_REFUSE (mf_refuse_step). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_refuse_c m_file_c m_file_m m_file_k m_file_mdl
  m_file_sd m_file_rf m_file_s_kknock_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instruction 0x86b70 (the first of the store's check, where a0 is re-shaped) and the `jal` 0x86ccc *)
Definition KH_PIN : Z := AF_m_file + 0xcb4.
Definition KH_JAL : Z := AF_m_file + 0xe10.

(* ===================================== byte lists (pure) ===================================== *)
(* m_file_s_hdrb_1.v mcx_nth_ext *)
Lemma kh_nth_ext : forall {A} (l l' : list A), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros A l. induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - specialize (H 0%nat). cbn in H. discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

(* m_file_s_hdrb_1.v mcx_fld_nth *)
Lemma kh_fld_nth : forall off n (L : list byte) i,
  nth_error (seg_spec.fld off n L) i = if (i <? n)%nat then nth_error L (off + i) else None.
Proof.
  intros off n L i. unfold seg_spec.fld. rewrite nth_error_firstn.
  destruct (i <? n)%nat; [|reflexivity]. rewrite nth_error_skipn. f_equal; lia.
Qed.

(* m_file_s_hdrb_1.v mcx_fld_upd_out *)
Lemma kh_fld_upd_out : forall (L : list byte) k nb off n, (k + length nb <= length L)%nat ->
  (off + n <= k \/ k + length nb <= off)%nat -> seg_spec.fld off n (Mem.upd_bytes L k nb) = seg_spec.fld off n L.
Proof.
  intros L k nb off n H1 H2. apply kh_nth_ext. intros i. rewrite !kh_fld_nth.
  destruct (Nat.ltb_spec0 i n) as [Hi|Hi]; [|reflexivity].
  destruct (Nat.ltb_spec0 (off + i) (length L)) as [Hl|Hl].
  - rewrite Mem.upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (off + i)); destruct (Nat.ltb_spec0 (off + i) (k + length nb)); cbn [andb];
      first [reflexivity | exfalso; lia].
  - rewrite (proj2 (nth_error_None L (off + i))) by lia.
    apply nth_error_None. rewrite Mem.upd_bytes_length by lia. lia.
Qed.

(* m_file_s_hdrb_1.v mcx_fld_upd_same *)
Lemma kh_fld_upd_same : forall (L : list byte) k n nb, n = length nb -> (k + n <= length L)%nat ->
  seg_spec.fld k n (Mem.upd_bytes L k nb) = nb.
Proof.
  intros L k n nb -> H. apply kh_nth_ext. intros i. rewrite kh_fld_nth.
  destruct (Nat.ltb_spec0 i (length nb)) as [Hi|Hi].
  - rewrite Mem.upd_bytes_nth by lia.
    destruct (Nat.leb_spec0 k (k + i)); destruct (Nat.ltb_spec0 (k + i) (k + length nb)); cbn [andb];
      first [f_equal; lia | exfalso; lia].
  - symmetry. apply nth_error_None. lia.
Qed.

(* the offsets of the mconf block in Z, for lia (m_file_s_hdrb_1.v mcx_lia, the mconf fields only) *)
Ltac kh_lia := unfold seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT, seg_spec.MC_KNOCK,
  seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *; lia.

(* the block with kept_knock[n_kept] = 1 (n_kept < 8) encodes the same model with the pending knock flag *)
Lemma kh_enc_knock : forall mc bs, seg_spec.mconf_encp false mc bs -> (length (mc_kept mc) < 8)%nat ->
  seg_spec.mconf_encp true mc
    (Mem.upd_bytes bs (Z.to_nat seg_spec.MC_KNOCK + 4 * length (mc_kept mc)) (Mem.le4 (Z_to_bv 64 1))).
Proof.
  intros mc bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hk.
  set (k := length (mc_kept mc)) in *.
  assert (HL4 : length (Mem.le4 (Z_to_bv 64 1)) = 4%nat) by apply Mem.length_le4.
  assert (HP : (Z.to_nat seg_spec.MC_KNOCK + 4 * k + length (Mem.le4 (Z_to_bv 64 1)) <= length bs)%nat)
    by (rewrite HL4; kh_lia).
  unfold seg_spec.mconf_encp, seg_spec.fldz in *. fold k.
  split; [rewrite Mem.upd_bytes_length by exact HP; exact H1|].
  split; [exact H2|].
  split; [intros i Hi; rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact (H3 i Hi)|].
  split; [rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H4|].
  split; [rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H5|].
  split; [rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H6|].
  split; [exact H7|].
  split.
  { intros i Hi. destruct (H8 i Hi) as [A1 A2]. fold k in Hi.
    split; rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); assumption. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i k) as [-> | Hne].
    - rewrite Nat.eqb_refl. cbn [andb]. unfold seg_spec.flag_enc.
      apply kh_fld_upd_same; [rewrite HL4; reflexivity | rewrite HL4 in HP; exact HP].
    - rewrite (proj2 (Nat.eqb_neq i k) Hne). cbn [andb].
      rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia).
      pose proof (H9 i Hi) as X. cbn [andb] in X. exact X. }
  split; [rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H10|].
  split; [rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H11|].
  rewrite kh_fld_upd_out by (rewrite ?HL4; kh_lia); exact H12.
Qed.

(* at n_kept = 8 the pending flag constrains no entry *)
Lemma kh_enc_full : forall mc bs, seg_spec.mconf_encp false mc bs -> length (mc_kept mc) = 8%nat ->
  seg_spec.mconf_encp true mc bs.
Proof.
  intros mc bs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hk.
  unfold seg_spec.mconf_encp.
  do 8 (split; [assumption|]). split; [intros i Hi; lia|]. auto.
Qed.

(* m_file_s_hdrb_1.v hb_nth_le_bytes / hb_le4_byte: the bytes of le4 *)
Lemma kh_nth_le_bytes : forall n z k, (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  induction n as [|n IH]; intros z k Hk; [exfalso; lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth].
  - rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 2 ^ 8).
    replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma kh_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4, le_byte.
  rewrite kh_nth_le_bytes by exact Hk.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* ===================================== readers ===================================== *)
(* m_file_s_hdrb_1.v hb_val_of_u32: a u32 field of a block read through the reader *)
Lemma kh_val_of_u32 : forall rd c bs off v, sa_bytes rd c bs -> (off + 4 <= length bs)%nat ->
  seg_spec.u32_enc v (seg_spec.fld off 4 bs) -> sa_val rd (c + Z.of_nat off) 4 v.
Proof.
  intros rd c bs off v Hb HL [Hv Hf]. unfold sa_bytes, sa_val in *. intros k Hk.
  replace (c + Z.of_nat off + Z.of_nat k) with (c + Z.of_nat (off + k)) by lia.
  rewrite (Hb (off + k)%nat) by lia. f_equal.
  assert (E : nth k (seg_spec.fld off 4 bs) ZB0 = nth (off + k) bs ZB0).
  { apply nth_error_nth. rewrite kh_fld_nth. destruct (Nat.ltb_spec0 k 4) as [_|C]; [|exfalso; lia].
    apply nth_error_nth'. lia. }
  rewrite <- E, Hf. apply kh_le4_byte; [exact Hv | exact Hk].
Qed.

(* n_kept of the block (the load at c + MC_NKEPT), at either pending flag *)
Lemma kh_rd_nkept : forall pend rd c mc, sa_mconfp pend rd c mc ->
  sa_val rd (c + seg_spec.MC_NKEPT) 4 (Z.of_nat (length (mc_kept mc))).
Proof.
  intros pend rd c mc (bs & Hb & He). pose proof He as (H1 & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _).
  unfold seg_spec.fldz in H10.
  replace (c + seg_spec.MC_NKEPT) with (c + Z.of_nat (Z.to_nat seg_spec.MC_NKEPT)) by kh_lia.
  apply (kh_val_of_u32 rd c bs); [exact Hb | kh_lia | exact H10].
Qed.

(* m_file_s_hdrb_1.v hb_bytes_upd: the block after a write whose part inside it is X at offset k *)
Lemma kh_bytes_upd : forall rd rd' c BS k X, sa_bytes rd c BS -> sa_bytes rd' (c + Z.of_nat k) X ->
  (k + length X <= length BS)%nat ->
  (forall a, c <= a < c + Z.of_nat (length BS) ->
     ~ (c + Z.of_nat k <= a < c + Z.of_nat k + Z.of_nat (length X)) -> rd' a = rd a) ->
  sa_bytes rd' c (Mem.upd_bytes BS k X).
Proof.
  intros rd rd' c BS k X HB HX HL HK. unfold sa_bytes in *. intros i Hi.
  rewrite Mem.upd_bytes_length in Hi by exact HL.
  pose proof (Mem.upd_bytes_nth BS k X i HL Hi) as E. revert E.
  destruct (Nat.leb_spec0 k i) as [H1|H1]; destruct (Nat.ltb_spec0 i (k + length X)) as [H2|H2];
    cbn [andb]; intros E.
  1: { assert (E' : nth i (Mem.upd_bytes BS k X) ZB0 = nth (i - k) X ZB0)
         by (apply nth_error_nth; rewrite E; apply nth_error_nth'; lia).
       rewrite E'. replace (c + Z.of_nat i) with (c + Z.of_nat k + Z.of_nat (i - k)) by lia.
       apply HX. lia. }
  all: assert (E' : nth i (Mem.upd_bytes BS k X) ZB0 = nth i BS ZB0)
         by (apply nth_error_nth; rewrite E; apply nth_error_nth'; lia);
       rewrite E'; rewrite HK by lia; apply HB; exact Hi.
Qed.

(* m_file_s_hdrb_1.v hb_bytes_of_val: a 4-byte value read through the reader is the bytes le4 *)
Lemma kh_bytes_of_val : forall rd a v, 0 <= v < 2 ^ 32 -> sa_val rd a 4 v -> sa_bytes rd a (Mem.le4 (Z_to_bv 64 v)).
Proof.
  intros rd a v Hv HV. unfold sa_val, sa_bytes in *. intros i Hi. rewrite Mem.length_le4 in Hi.
  rewrite HV by exact Hi. f_equal. symmetry. apply kh_le4_byte; assumption.
Qed.

(* m_file_s_hdrb_5.v hb5_val_of_sa / hb5_sa_of_val: a value read through the ASan reader is a value of the
   restricted memory, and back *)
Lemma kh_val_of_sa : forall segs H mem a n z, sa_val (aview segs H mem) a n z -> val_mem segs (mrestrict H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hv. unfold YO0f.le_byte, YG0f.le_byte.
symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Lemma kh_sa_of_val : forall segs H mem a n z, val_mem segs (mrestrict H mem) a n z -> sa_val (aview segs H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, YG0f.le_byte. apply bv_wrap_small. change (bv_modulus 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.

(* m_file_s_hdrb_5.v hb5_atom_val: an atom holding x, as a symbolic value *)
Lemma kh_atom_val : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k Hn Hx. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hx. reflexivity. Qed.

(* ===================================== tactics ===================================== *)
(* the state's form, computed *)
Ltac kh_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* a register of a run's final state, its denotation not normalized (m_file_s_hdrb_7.v hb7_reg, for st_ok_pi) *)
Ltac kh_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac kh_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the first region is kept_knock[n_kept] (atom 53, holding b, U53), written; FP53 says its bytes may be; the rest
   read-only *)
Ltac kh_awr53 U53 FP53 :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 53%nat _); [reflexivity | exact U53 | exact FP53 |];
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ===================================== the symbolic state ===================================== *)
(* the n_kept cell of the block (atom 33), read-only, its chunk e *)
Definition kh_r33 (e : sv) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x23ac 0x23b0 0 0 [YP09.mkChunk 0x23ac (CVal 4 e)].
(* kept_knock[n_kept] (atom 53 = c + 0x238c + 4 n_kept), written by `sw a1,0(a0)` *)
Definition kh_r53 : YP09.region := YP09.mkRegion (Some 53%nat) 0 4 0 4 [].
(* the shadow entries: the whole block, and kept_knock[n_kept]'s granule (`covered (SOff 53 0) 8`) *)
Definition kh_SHA : list shent := [mkSHE 33 0 9236; mkSHE 53 0 8].
Definition kh_SHB : list shent := [mkSHE 33 0 9236].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.
(* the shared hypotheses (m_file_m.v change 3, decision (a), amended) this file needs, verbatim *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstA.STK_m_refuse SegInstA.RLO_A SegInstA.RHI_A SegInstA.seg_litA_fz SegInstA.gotwA SegInstA.guardA.

(* m_file_s_hdrb_5.v hb5_geo: the numbers every piece reads *)
Lemma kh_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ mv_c v mod 16 = 0 /\
alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288 /\
0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX CORE.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & Hc16 & _).
destruct (mf_s1_facts B v CX) as (S1 & S2 & S3). destruct (mf_sp0 B v CX) as (P1 & P2 & P3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S3.
pose proof asan_consts as (C1 & _).
repeat split; try lia.
Qed.

(* m_file_k.v mf_keep_k (same layout and state), with the block holding mcc' at the pending flag knock' *)
Lemma kh_keep_k : forall knock knock' v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) mcc',
mf_cx B v -> mf_corek B knock v lyc Sc Wc memc mdc pos lowsh mcc ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc W2 mem2 md2 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H W2) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh) ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) ->
sa_mconfp knock' (rdW W2 mem2) (mv_c v) mcc' ->
mf_corek B knock' v lyc Sc W2 mem2 md2 pos lowsh mcc'.
Proof.
intros knock knock' v lyc Sc Wc memc mdc pos lowsh mcc W2 mem2 md2 RW mcc' CX0 CORE HJ2 K RWok VSH' V112' MC'.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & Hmc & Hac & Htl).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX0) as (Sp1 & Sp2 & Sp3).
destruct (mf_blk_c_k B knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in Sp1.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof HJ2 as (HAR2 & _).
split; [exact HJ2|]. split; [exact HPerm|]. split.
{ apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact VFL].
  intros k Hk HR. change (Z.of_nat 8) with 8 in Hk.
  exact (mf_rw_ftail_k B knock v lyc Sc Wc memc mdc pos lowsh mcc (frame_addr lyc 1 pos + 120 + k) CX0 CORE ltac:(lia)
    (RWok _ HR)). }
split; [exact VSH'|]. split.
{ intros j r Hj.
  assert (Hj13 : (j < length mf_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length mf_saved_regs] in Hj13.
  apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact (VSV j r Hj)].
  intros k Hk HR. change (Z.of_nat 8) with 8 in Hk.
  exact (mf_rw_stack_k B knock v lyc Sc Wc memc mdc pos lowsh mcc (mv_sp v - 8 - 8 * Z.of_nat j + k) CX0 CORE
    ltac:(unfold mf_s1 in *; lia) (RWok _ HR)). }
split; [exact V112'|].
split; [exact MC'|].
split.
{ destruct Hac as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc); unfold seg_spec.SEG_M_SIZE in *; lia. }
apply (mf_tail_keep_k B knock v lyc Sc Wc memc mdc pos lowsh mcc Sc W2 mem2 md2 RW _ CX0 CORE HJ2 K RWok); [| | exact Htl].
- unfold seg_spec.SEG_M_SIZE in *. lia.
- intros x Hx. lia.
Qed.

(* the block's encoding with the pending flag when n_kept = 8 *)
Lemma kh_corek_full : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> length (mc_kept mcc) = 8%nat ->
  mf_corek B true v lyc Sc Wc memc mdc pos lowsh mcc.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CORE Hk.
destruct CORE as (H1 & H2 & H3 & H4 & H5 & H6 & (bs & Hb & He) & H8 & H9).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6
  (conj (ex_intro _ bs (conj Hb (kh_enc_full mcc bs He Hk))) (conj H8 H9)))))))).
Qed.

(* ============================ the call: m_refuse at the `jal`, then KDONE ============================ *)
Lemma kh_jal : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) ->
forall v lyc Sc Wc (regs : bvmap 5 word) memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_corek B true v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
mf_np v memc Wc (mf_next p rest) ->
getr regs 10 = w64 (mv_c v) -> getr regs 11 = w64 (line + 1) -> getr regs 21 = w64 (mv_c v) ->
getr regs 22 = w64 (line + 1) -> getr regs 24 = w64 (frame_addr lyc 1 pos) ->
mf_at B v Wc regs memc mdc KH_JAL.
Proof.
intros n KDONE v lyc Sc Wc regs memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD NP
  R10 R11 R21 R22 R24.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcok & Hk0 & _).
assert (Hcok2 : mf_cur_ok (m_refuse mcc (line + 1) true) (Some gi)) by (apply mf_cur_ok_refuse; exact Hcok).
change (mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest) with
  (fst (m_lines (m_refuse mcc (line + 1) true, Some gi) (line + 1) (lines (mf_rest rest)))) in MOD.
pose proof (mf_regs_at_call B v lyc pos regs RA) as (S2r & S3r & S4r & S8r).
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc regs memc mdc pos MF_LOW_ON mcc mcc true (Some gi)
  line p rest (mf_next p rest) KH_JAL CX LS FRM CORE CELLS NP S2r S3r S4r S8r LOOP Hne eq_refl Hk0).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact R10.
- exact R11.
- exact (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v) Hcok2 MOD).
- intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE3 CELLS3 NP3 LOOP3 CS.
  assert (Ely2 : ly2 = lyc) by (destruct LS as (E1 & _); destruct LS2 as (E2 & _); congruence).
  subst ly2.
  replace (KH_JAL + 4) with MF_KDONE by (unfold KH_JAL, MF_KDONE; lia).
  pose proof (mf_regs_at_kept B v lyc pos regs regs2 RA CS) as RA3.
  assert (C21 : getr regs2 21 = getr regs 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
  assert (C22 : getr regs2 22 = getr regs 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
  assert (C24 : getr regs2 24 = getr regs 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
  apply (KDONE fx1 v lyc S2 W2 regs2 mem2 md2 pos (m_refuse mcc (line + 1) true) (Some gi) (line + 1)
    (mf_next p rest) (mf_rest rest) CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE3 CELLS3 RA3).
  + rewrite C24. exact R24.
  + destruct (mf_break_snd rest) as (_ & Hlt & _). specialize (Hlt Hne). unfold mf_rest. lia.
  + apply (mf_loop_next v W2 mem2 mcc (Some gi) line p rest (m_refuse mcc (line + 1) true) (Some gi) LOOP3 Hne).
    * unfold m_refuse. cbn [mc_refused]. lia.
    * unfold m_refuse. cbn [mc_overflow]. lia.
    * exact (proj1 (proj2 (m_refuse_sizes mcc (line + 1) true))).
    * exact Hcok2.
  + exact MOD.
  + exact NP3.
  + rewrite C21. exact R21.
  + rewrite C22. exact R22.
Qed.

(* ============================ n_kept = 8: no store, to the `jal` ============================ *)
Lemma kh_hitB : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
getr regs1 24 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
length (mc_kept mcc) = 8%nat ->
mf_at B v Wc regs1 memc mdc KK_HIT.
Proof.
intros n KDONE v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24 NP Hk8.
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (kh_geo v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
unfold seg_spec.SEG_M_SIZE in G2, Hbc2.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & Bk3 & Bk4 & _ & Bkm).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mbc 1 pos HAR Hbc Hin) as Hsep.
change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
unfold in_app in Bk3.
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
pose proof LOOP as (_ & _ & _ & _ & _ & Hcok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (kh_val_of_sa _ _ _ _ _ _ (kh_rd_nkept false _ _ _ HMC)) as VNK.
rewrite Hk8 in VNK. change (Z.of_nat 8) with 8 in VNK.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
(* the seed *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] KK_HIT
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (SHE1 : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE 33 0 9236))
  by (subst E; apply (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc); [exact CX | exact CORE | unfold seg_spec.SEG_M_SIZE; lia]).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
(* the spill slots read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. kh_norm HS1.
(* the n_kept cell, the literal 8 *)
assert (HS2 := st_ok_pi_add_region E _ _ (kh_r33 (SLit 8)) HS1 ltac:(vm_compute; reflexivity)).
clear HS1.
lapply HS2; clear HS2; [intros HS2|].
2:{ unfold region_ok, kh_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 8) 8); [reflexivity | cbn; lia | cbn; lia |].
    cbn [restrict ms_mem mkst]. change (N.to_nat 4) with 4%nat. exact VNK. }
lapply HS2; clear HS2; [intros HS2|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint, kh_r33.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U33, ?U2, ?U8, ?U34, ?U36.
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.SEG_M_SIZE in *. rewrite HSB in *.
    repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
assert (SHOK : sh_ok SEGS (SOff 32 0) kh_SHB E (mrestrict (w_H Wc) memc)) by (constructor; [exact SHE1 | constructor]).
unfold mf_at.
(* 0x86b38 .. 0x86b60, 0x86cc4 .. 0x86cc8: the check of n_kept (decided), s5 = c, s6 = line + 1, n_kept = 8, s8 = FAKE,
   a0 = c, a1 = line + 1; to the `jal` *)
paj_run_to_tok RUNTO HS2 HJ SHOK Bspan KH_JAL.
{ kh_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdw CX CORE CELLS HJ K0)
  as (CORE' & CELLS' & NPK & LOOPK).
prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (25%bv : bv 5) Q25.
prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (10%bv : bv 5) Q10.
prreg HS2 (11%bv : bv 5) Q11. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (22%bv : bv 5) Q22.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
pmkst HS2.
change (Z_to_bv 64 (BASE + 8088)) with (Z_to_bv 64 (BASE + KH_JAL)).
apply (kh_jal n KDONE v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc gi line p rest CX LS FRM
  (kh_corek_full v lyc Sc Wc (ms_mem ms) mdw pos MF_LOW_ON mcc CORE' Hk8) CELLS' RA' Hn Hne
  (LOOPK mcc (Some gi) line p rest LOOP) MOD (NPK _ NP)).
- rewrite Q10, E33. reflexivity.
- rewrite Q11, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite Q21, E33. reflexivity.
- rewrite Q22, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite Q24, E34. reflexivity.
Qed.

(* ============================ n_kept < 8: kept_knock[n_kept] = 1, to the `jal` ============================ *)
Lemma kh_hitA : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) ->
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
getr regs1 24 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
(length (mc_kept mcc) < 8)%nat ->
mf_at B v Wc regs1 memc mdc KK_HIT.
Proof.
intros n KDONE v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24 NP Hk8.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & HMC & HAD & HTL).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (kh_geo v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
unfold seg_spec.SEG_M_SIZE in G2, Hbc2.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & Bk3 & Bk4 & _ & Bkm).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mbc 1 pos HAR Hbc Hin) as Hsep.
change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
unfold in_app in Bk3.
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
pose proof LOOP as (_ & _ & _ & _ & _ & Hcok & Hk0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcok) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (kh_val_of_sa _ _ _ _ _ _ (kh_rd_nkept false _ _ _ HMC)) as VNK.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
(* &kept_knock[n_kept] *)
set (q := mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc))).
assert (Hq : q = mv_c v + 9100 + 4 * Z.of_nat (length (mc_kept mcc))) by (unfold q, seg_spec.MC_KNOCK; lia).
(* the model: m_refuse keeps the refusal, kept grows to n_kept + 1, at most the final kept *)
assert (Hcok2 : mf_cur_ok (m_refuse mcc (line + 1) true) (Some gi)) by (apply mf_cur_ok_refuse; exact Hcok).
assert (HKF : (S (length (mc_kept mcc)) <= length (mc_kept (mf_final v)))%nat).
{ pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v) Hcok2 MOD)
    as L.
  unfold m_refuse in L. cbv zeta in L. cbn [mc_kept] in L.
  rewrite (proj2 (Z.ltb_lt (Z.of_nat (length (mc_kept mcc))) 8) ltac:(lia)) in L.
  rewrite length_app in L. cbn [length] in L. lia. }
(* the 4 bytes the store writes: in m_file's footprint and in the block *)
assert (FP53 : forall a, q + 0 <= a < q + 4 ->
  awr_byte SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (ablocks B (mv_ly v) (mv_S v))
    (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a).
{ intros a Ha. right; left. split.
  - eexists; split; [cbn [M_FILE_FP In]; right; right; right; left; reflexivity|]. cbn [fst snd].
    unfold mv_k0 in *. rewrite Hq in Ha. unfold seg_spec.MC_KNOCK. lia.
  - exists bc, mbc. split; [exact Hbc | rewrite Hq in Ha; lia]. }
(* the seed, with the caller's values n_kept (atom 52) and &kept_knock[n_kept] (atom 53) *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest)
  [Z.of_nat (length (mc_kept mcc)); q] KK_HIT true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [Z.of_nat (length (mc_kept mcc)); q]) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) [Z.of_nat (length (mc_kept mcc)); q])
    (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (E52 : ew E 52 = Z_to_bv 64 (Z.of_nat (length (mc_kept mcc))))
  by (subst E; exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) _ 0 ltac:(unfold A_TEXT; lia))).
assert (E53 : ew E 53 = Z_to_bv 64 q)
  by (subst E; exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) _ 1 ltac:(unfold A_TEXT; lia))).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (subst E; apply mfE_U32).
assert (SHE1 : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE 33 0 9236))
  by (subst E; apply (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc); [exact CX | exact CORE | unfold seg_spec.SEG_M_SIZE; lia]).
clear HE.
assert (SHE2 : shent_ok SEGS (SOff 32 0) E (mrestrict (w_H Wc) memc) (mkSHE 53 0 8)).
{ apply (mf_she_at E Wc memc 53 q 8 UB E53); [rewrite Hq; lia | lia | |].
  - destruct (mf_addr_sub _ (mv_c v) seg_spec.SEG_M_SIZE q 8 HAD) as (_ & _ & _ & HRA & _);
      [rewrite Hq; lia | rewrite Hq; unfold seg_spec.SEG_M_SIZE; lia | lia | exact HRA].
  - intros x Hx. apply (mf_blk_app B v CX). rewrite Hq in Hx. unfold seg_spec.SEG_M_SIZE. lia. }
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (U52 : bv_unsigned (ew E 52) = Z.of_nat (length (mc_kept mcc))) by (rewrite E52; apply unsigned_lit_small; lia).
assert (U53 : bv_unsigned (ew E 53) = q) by (rewrite E53; apply unsigned_lit_small; rewrite Hq; lia).
(* the spill slots read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. kh_norm HS1.
(* the n_kept cell, atom 52 *)
assert (HS2 := st_ok_pi_add_region E _ _ (kh_r33 (SOff 52 0)) HS1 ltac:(vm_compute; reflexivity)).
clear HS1.
lapply HS2; clear HS2; [intros HS2|].
2:{ unfold region_ok, kh_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SOff 52 0) (Z.of_nat (length (mc_kept mcc))));
      [rewrite (kh_atom_val E 52 _ 0 E52 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    cbn [restrict ms_mem mkst]. change (N.to_nat 4) with 4%nat. exact VNK. }
lapply HS2; clear HS2; [intros HS2|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint, kh_r33.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U33, ?U2, ?U8, ?U34, ?U36.
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.SEG_M_SIZE in *. rewrite HSB in *.
    repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
(* kept_knock[n_kept], atom 53, writable *)
assert (HS3 := st_ok_pi_add_region E _ _ kh_r53 HS2 ltac:(vm_compute; reflexivity)).
clear HS2.
lapply HS3; clear HS3; [intros HS3|].
2:{ unfold region_ok, kh_r53. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U53. split; [rewrite Hq; lia|]. split; [rewrite Hq; lia|]. split; [|constructor].
    intros o Ho. cbn [restrict ms_mem mkst]. apply (apresent_writable SEGS).
    exact (proj1 (Bk4 (q + o) ltac:(rewrite Hq; lia))). }
lapply HS3; clear HS3; [intros HS3|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint, kh_r53, kh_r33.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U53, ?U33, ?U2, ?U8, ?U34, ?U36. rewrite Hq.
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.SEG_M_SIZE in *. rewrite HSB in *.
    repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
(* the facts on atoms 52 (n_kept <= 7) and 53 (4-aligned) *)
apply (st_ok_pi_add_fact E _ _ 52 (mkAF 0 7 0)) in HS3;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U52; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
apply (st_ok_pi_add_fact E _ _ 53 (HPTR 2)) in HS3;
  [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U53; change (2 ^ 2) with 4; rewrite Hq;
     split; [lia|]; split; [|lia];
     replace (mv_c v + 9100 + 4 * Z.of_nat (length (mc_kept mcc))) with
       ((mv_c v / 16 * 4 + 2275 + Z.of_nat (length (mc_kept mcc))) * 4)
       by (pose proof (Z.div_mod (mv_c v) 16 ltac:(lia)); lia);
     apply Z_mod_mult].
kh_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) kh_SHA E (mrestrict (w_H Wc) memc))
  by (constructor; [exact SHE1 | constructor; [exact SHE2 | constructor]]).
unfold mf_at.
(* 0x86b38 .. 0x86b6c: the check of n_kept (decided), s5 = c, s6 = line + 1, n_kept <= 7 (decided), s8 = FAKE,
   a0 = 24(s1) + 4 n_kept *)
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KH_PIN.
{ kh_awr53 U53 FP53. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 4) -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun x => q <= x < q + 4) HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq' | Hinw];
      [injection Hq' as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U53 in Hr; lia] |]);
    destruct Hinw | ] end.
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
rename ms into ms1. rename mat into mat1. clear HF HFr HG.
(* a0 re-shaped to atom 53: the same address *)
kh_reg HS3 (10%bv : bv 5) Q10p.
assert (D53 : sv_denot E (SOff 53 0) = getr (ms_regs (restrict (w_H Wc) ms1)) 10%bv).
{ cbn [ms_regs restrict]. rewrite Q10p. rewrite (denot_lit_U E (SOff 53 0)), (denot_lit_U E (SAlu _ _ _)). f_equal.
  rewrite (U_atom E 53 q E53 ltac:(rewrite Hq; lia)). rewrite !U_SAlu, U_SLit.
  rewrite (U_atom_off E 33 (mv_c v) 9100 E33 ltac:(lia) ltac:(lia)), (U_atom E 52 _ E52 ltac:(lia)).
  cbn [zalu_raw]. rewrite (zcanon_id 2) by (unfold M64; lia). change (Z.land 2 63) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite (zcanon_id (Z.of_nat (length (mc_kept mcc)) * 4)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). rewrite Hq. lia. }
apply (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 53 0)) in HS3; [| reflexivity | exact D53].
kh_norm HS3.
(* 0x86b70 .. 0x86b88, 0x86cc4 .. 0x86cc8: the check of the store (decided), kept_knock[n_kept] = 1, a0 = c,
   a1 = line + 1; to the `jal` *)
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KH_JAL.
{ kh_awr53 U53 FP53. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 4) -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun x => q <= x < q + 4) HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq' | Hinw];
      [injection Hq' as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U53 in Hr; lia] |]);
    destruct Hinw | ] end.
set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *.
(* the runs wrote kept_knock[n_kept] only *)
set (RW := fun x => q <= x < q + 4).
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnR. rewrite (K2 a Ha HnR). exact (K1 a Ha HnR). }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a Ha. unfold RW in Ha. unfold mf_rw. right; left. rewrite Hq in Ha. unfold seg_spec.SEG_M_SIZE. lia. }
assert (RWS : mf_rws v RW).
{ intros a HR Hs. unfold RW in HR. rewrite Hq in HR. lia. }
(* the stored word: 1 *)
pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR53. cbn [restrict ms_mem] in HR53.
pose proof (field_of_region_any E _ 53 q _ 0 4 0 4 0 4%N (SLit 1) HR53 U53 ltac:(cbn; left; reflexivity)
  ltac:(cbn; lia)) as VW.
replace (bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VW by (vm_compute; reflexivity).
change (N.to_nat 4) with 4%nat in VW. rewrite Z.add_0_r in VW.
(* the cells the cut facts read, kept *)
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_ON).
{ intros j Hj.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ KK);
    [rewrite HSB; lia | change (Z.of_nat 1) with 1; rewrite HSB; lia | | exact (VSH j Hj)].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 1) with 1 in Hk.
  apply (mf_blk_app B v CX (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j + k));
    [rewrite Hq in HR; unfold seg_spec.SEG_M_SIZE; lia | rewrite HSB; lia]. }
assert (V112' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos)).
{ apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 8 _ KK); [lia | change (Z.of_nat 8) with 8; lia | | exact V112].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. rewrite Hq in HR. lia. }
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136 & _).
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8
  (mf_cur_ptr (mv_c v) (Some gi))).
{ apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 8 _ KK); [lia | change (Z.of_nat 8) with 8; lia | | exact C136].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. rewrite Hq in HR. lia. }
assert (NP' : mf_np v (ms_mem ms) Wc (mf_next p rest)).
{ unfold mf_np in NP |- *.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 8 _ KK); [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros k Hk HR. unfold RW in HR. change (Z.of_nat 8) with 8 in Hk. rewrite Hq in HR. lia. }
(* the block: the entry's bytes with kept_knock[n_kept] = 1, the model with the pending knock flag *)
assert (MC' : sa_mconfp true (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ destruct HMC as (bs & HBS & HENC).
  pose proof HENC as (HBL & _).
  exists (Mem.upd_bytes bs (Z.to_nat seg_spec.MC_KNOCK + 4 * length (mc_kept mcc)) (Mem.le4 (Z_to_bv 64 1))).
  split; [| exact (kh_enc_knock mcc bs HENC Hk8)].
  apply (kh_bytes_upd (rdW Wc memc) (rdW Wc (ms_mem ms)) (mv_c v) bs _ _ HBS).
  - replace (mv_c v + Z.of_nat (Z.to_nat seg_spec.MC_KNOCK + 4 * length (mc_kept mcc))) with q
      by (rewrite Hq; kh_lia).
    apply kh_bytes_of_val; [lia|]. apply kh_sa_of_val. exact VW.
  - rewrite Mem.length_le4. kh_lia.
  - intros a Ha HnA. rewrite Mem.length_le4 in HnA. unfold seg_spec.SEG_M_SIZE in HBL.
    apply KK; [lia|]. unfold RW. intros HR. apply HnA. rewrite Hq in HR. kh_lia. }
pose proof (kh_keep_k false true v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Wc (ms_mem ms) md2 RW mcc CX
  (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) HJ KK RWok VSH' V112' MC') as COREK.
pose proof (mf_keep_cells B v lyc pos Wc Wc memc (ms_mem ms) RW (Some gi) (Some gi) CX KK RWS CELLS V136') as CELLS'.
pose proof (mf_loop_keep_k B false v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Sc Wc (ms_mem ms) md2 RW mcc (Some gi) line
  p rest CX (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) HJ (Permutation_refl _) KK RWok LOOP)
  as LOOP'.
(* the registers at the `jal` *)
prreg HS3 (2%bv : bv 5) Q2. prreg HS3 (3%bv : bv 5) Q3. prreg HS3 (4%bv : bv 5) Q4. prreg HS3 (8%bv : bv 5) Q8.
prreg HS3 (9%bv : bv 5) Q9. prreg HS3 (18%bv : bv 5) Q18. prreg HS3 (19%bv : bv 5) Q19. prreg HS3 (25%bv : bv 5) Q25.
prreg HS3 (26%bv : bv 5) Q26. prreg HS3 (24%bv : bv 5) Q24. prreg HS3 (10%bv : bv 5) Q10.
prreg HS3 (11%bv : bv 5) Q11. prreg HS3 (21%bv : bv 5) Q21. prreg HS3 (22%bv : bv 5) Q22.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26. apply EE. reflexivity. }
pmkst HS3.
change (Z_to_bv 64 (BASE + 8088)) with (Z_to_bv 64 (BASE + KH_JAL)).
apply (kh_jal n KDONE v lyc Sc Wc (ms_regs ms) (ms_mem ms) md2 pos mcc gi line p rest CX LS FRM COREK CELLS' RA' Hn Hne
  LOOP' MOD NP').
- rewrite Q10, E33. reflexivity.
- rewrite Q11, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite Q21, E33. reflexivity.
- rewrite Q22, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite Q24, E34. reflexivity.
Qed.

(* ===================================== KK_HITX from KDONE ===================================== *)
Lemma kk_hit : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) -> KK_HITX_stmt B n.
Proof.
intros n KDONE. unfold KK_HITX_stmt, KK_ATX_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24 NP.
pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & _ & HENC) & _).
pose proof HENC as (_ & _ & _ & _ & _ & _ & Hk & _).
destruct (Nat.lt_ge_cases (length (mc_kept mcc)) 8) as [Hlt | Hge].
- exact (kh_hitA n KDONE v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24
    NP Hlt).
- exact (kh_hitB n KDONE v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP MOD R24
    NP ltac:(lia)).
Qed.

End e.
End f.
End d.
