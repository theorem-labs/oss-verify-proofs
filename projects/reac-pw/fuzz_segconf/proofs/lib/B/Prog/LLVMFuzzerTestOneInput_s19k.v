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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 837 of its 889 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s17.v, with its module paths and module names changed; 552 of its 687 lines of code are new or changed and 754 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (asan-ubsan, pin c3796c0b38f3): the kit for segment S10 of
   LLVMFuzzerTestOneInput's walk (0x856f4 .. 0x85864: check_refusals and the refusal loop), the pure model and
   encoding facts of the two harness blocks c (rconf, 0x40e8 bytes) and m (mconf, 0x2414 bytes) read through the
   ASan reader, and the walk facts the segment's points share (s19_inv, its transfer across a state change that keeps
   every byte below the allocation ceiling and every byte at and above s1 outside the set-up's slot windows, and one
   program call of a contract with apost_base / sa_kept / sa_noalloc, s19_prog_call). Every lemma is closed with
   Qed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* helpers: a field of a byte list, a little-endian word's bytes, and a C string field / a u32 field of a block
   read through the reader *)
Lemma s19_nth_fld : forall (bs : list byte) k n j d, (j < n)%nat ->
  nth j (seg_spec.fld k n bs) d = nth (k + j) bs d.
Proof.
  intros bs k n j d Hj. unfold seg_spec.fld. rewrite nth_firstn.
  destruct (Nat.ltb_spec j n) as [_|H]; [|lia]. apply nth_skipn.
Qed.

Lemma s19_nth_le_bytes : forall n z j d, (j < n)%nat ->
  nth j (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
  induction n as [|n IH]; intros z j d Hj; [lia|].
  destruct j as [|j]; cbn [Z_to_le_bytes nth].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 2 f_equal. lia.
Qed.

Lemma s19_val_of : forall (rd : reader) a bs k v, sa_bytes rd a bs -> (k + 4 <= length bs)%nat ->
  0 <= v < 2 ^ 32 -> seg_spec.fld k 4 bs = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v)) ->
  sa_val rd (a + Z.of_nat k) 4 v.
Proof.
  intros rd a bs k v B L V E j Hj.
  replace (a + Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (k + j)) by lia.
  rewrite (B (k + j)%nat) by lia. f_equal.
  rewrite <- (s19_nth_fld bs k 4 j ZB0 Hj), E, (s19_nth_le_bytes 4 _ j ZB0 Hj).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma s19_str_of : forall (rd : reader) a bs k cap s, sa_bytes rd a bs -> (k + cap <= length bs)%nat ->
  seg_spec.cstr_enc cap s (seg_spec.fld k cap bs) -> (k + length s + 8 <= length bs)%nat ->
  sa_str rd (a + Z.of_nat k) s.
Proof.
  intros rd a bs k cap s B L (Lf & Ls & N0 & Ef) Lt.
  split; [split|].
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    replace (a + Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (k + j)) by lia.
    rewrite (B (k + j)%nat) by lia. f_equal.
    rewrite <- Ef. rewrite nth_firstn. destruct (Nat.ltb_spec j (S (length s))) as [_|H]; [|lia].
    unfold seg_spec.zs.
    assert (E0 : nth j (map bv_unsigned (seg_spec.fld k cap bs)) 0 =
                 nth j (map bv_unsigned (seg_spec.fld k cap bs)) (bv_unsigned ZB0))
      by (apply nth_indep; rewrite length_map; lia).
    rewrite E0, map_nth. rewrite s19_nth_fld by lia. reflexivity.
  - exact N0.
  - intros x Hx.
    assert (M : 0 <= (a + Z.of_nat k + Z.of_nat (length s)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite (B (Z.to_nat (x - a))) by lia. discriminate.
Qed.

Lemma s19_hull_mono : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8.
Proof.
  intros x y H. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|].
  apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* the model: the harness's checks pass on every input (SegModel.segconf_agrees), so at the state after the file
   loop check_refusals holds and every refusal / kept pair passes check_kept *)
Lemma s19_checks : forall pl : list byte,
  SegModel.check_refusals (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl)))
    (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl))) = true /\
  SegModel.check_kept_all (SegModel.rc_refusal (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl))))
    (SegModel.mc_kept (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl)))) = true.
Proof.
  intros pl.
  assert (Hb : Forall (fun b => 0 <= b < 256) (seg_spec.seg_in pl)).
  { unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map, Forall_forall. intros b _.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. }
  pose proof (SegModel.segconf_agrees (seg_spec.seg_in pl) Hb) as H.
  change (SegModel.decode (seg_spec.seg_in pl)) with (seg_spec.seg_pay pl) in H.
  unfold SegModel.harness_ok in H. unfold seg_spec.seg_rc, seg_spec.seg_mc.
  revert H. destruct (SegModel.run (seg_spec.seg_pay pl)) as [[c m] ret]. cbn [fst snd]. intros H.
  cbv beta iota zeta in H.
  apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6].
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  split; assumption.
Qed.

Lemma s19_nref_eq : forall rc mc, SegModel.check_refusals rc mc = true ->
  length (SegModel.rc_refusal rc) = length (SegModel.mc_kept mc).
Proof.
  intros rc mc H. unfold SegModel.check_refusals in H. apply andb_true_iff in H as [_ H2].
  apply Nat.eqb_eq in H2. exact H2.
Qed.

Lemma s19_kept_nth : forall gs ws i, SegModel.check_kept_all gs ws = true ->
  (i < length gs)%nat -> (i < length ws)%nat ->
  SegModel.strncmp (nth i gs []) (fst (nth i ws ([], false))) (SegModel.strlen (fst (nth i ws ([], false)))) = 0 /\
  (negb (snd (nth i ws ([], false))) || SegModel.strstr_found (nth i gs []) SegModel.TNP) = true.
Proof.
  intros gs ws i H Hg Hw.
  assert (K : SegModel.check_kept (nth i gs []) (nth i ws ([], false)) = true).
  { revert ws i H Hg Hw. induction gs as [|g gs IH]; intros [|w ws] i H Hg Hw; cbn [length] in Hg, Hw; try lia.
    cbn [SegModel.check_kept_all] in H. apply andb_true_iff in H as [H1 H2].
    destruct i as [|i]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia | lia]. }
  unfold SegModel.check_kept in K. apply andb_true_iff in K as [K1 K2].
  apply Z.eqb_eq in K1. split; assumption.
Qed.

(* the reader's block c: refusal[i] as a C string with its 8-byte tail, and n_refusals *)
Lemma s19_refusal : forall (rd : reader) c rc i, sa_rconf rd c rc ->
  (i < length (SegModel.rc_refusal rc))%nat ->
  sa_str rd (c + 11912 + 200 * Z.of_nat i) (nth i (SegModel.rc_refusal rc) []) /\
  Z.of_nat (length (nth i (SegModel.rc_refusal rc) [])) + 1 <= 200.
Proof.
  intros rd c rc i (bs & B & L & L32 & HS & UN & L8 & HR & UR & _) Hi.
  pose proof (HR i Hi) as Er. unfold seg_spec.SEG_C_SIZE in L.
  set (kr := Z.to_nat seg_spec.RC_REFUSAL) in *. assert (Ekr : Z.of_nat kr = 11912) by reflexivity. clearbody kr.
  set (t := nth i (SegModel.rc_refusal rc) []) in *. clearbody t.
  pose proof Er as (Lf & Ls & _).
  split.
  - replace (c + 11912 + 200 * Z.of_nat i) with (c + Z.of_nat (kr + 200 * i)) by lia.
    apply (s19_str_of rd c bs (kr + 200 * i) 200); [exact B | lia | exact Er | lia].
  - lia.
Qed.

Lemma s19_nref_val : forall (rd : reader) c rc, sa_rconf rd c rc ->
  sa_val rd (c + 13512) 4 (Z.of_nat (length (SegModel.rc_refusal rc))) /\
  (length (SegModel.rc_refusal rc) <= 8)%nat.
Proof.
  intros rd c rc (bs & B & L & L32 & HS & UN & L8 & HR & UR & _).
  unfold seg_spec.SEG_C_SIZE in L.
  destruct UR as [V E]. unfold seg_spec.fldz, seg_spec.RC_NREF in E.
  set (kn := Z.to_nat 13512) in *. assert (Ekn : Z.of_nat kn = 13512) by reflexivity. clearbody kn.
  split; [|exact L8].
  replace (c + 13512) with (c + Z.of_nat kn) by lia.
  apply (s19_val_of rd c bs kn); [exact B | lia | exact V | exact E].
Qed.

(* the model's block m: kept[i] as a C string with its 8-byte tail, kept_knock[i], and n_kept *)
Lemma s19_kept : forall (rd : reader) m mc i, sa_mconf rd m mc ->
  (i < length (SegModel.mc_kept mc))%nat ->
  sa_str rd (m + 8204 + 112 * Z.of_nat i) (fst (nth i (SegModel.mc_kept mc) ([], false))) /\
  Z.of_nat (length (fst (nth i (SegModel.mc_kept mc) ([], false)))) + 1 <= 112 /\
  sa_val rd (m + 9100 + 4 * Z.of_nat i) 4 (seg_spec.b2z (snd (nth i (SegModel.mc_kept mc) ([], false)))).
Proof.
  intros rd m mc i (bs & B & L & L32 & HS & UN & UO & UR & HL8 & HK & HP & UK & _) Hi.
  destruct (HK i Hi) as (Ek & Fk).
  unfold seg_spec.SEG_M_SIZE in L.
  set (w := nth i (SegModel.mc_kept mc) ([], false)) in *. clearbody w.
  set (kk := Z.to_nat seg_spec.MC_KEPT) in *. assert (Ekk : Z.of_nat kk = 8204) by reflexivity. clearbody kk.
  set (kn := Z.to_nat seg_spec.MC_KNOCK) in *. assert (Ekn : Z.of_nat kn = 9100) by reflexivity. clearbody kn.
  pose proof Ek as (Lk & Ls & _).
  split; [|split].
  - replace (m + 8204 + 112 * Z.of_nat i) with (m + Z.of_nat (kk + 112 * i)) by lia.
    apply (s19_str_of rd m bs (kk + 112 * i) 112); [exact B | lia | exact Ek | lia].
  - lia.
  - replace (m + 9100 + 4 * Z.of_nat i) with (m + Z.of_nat (kn + 4 * i)) by lia.
    apply (s19_val_of rd m bs (kn + 4 * i)); [exact B | lia | | exact Fk].
    unfold seg_spec.b2z. destruct (snd w); lia.
Qed.

Lemma s19_nkept_val : forall (rd : reader) m mc, sa_mconf rd m mc ->
  sa_val rd (m + 9132) 4 (Z.of_nat (length (SegModel.mc_kept mc))) /\
  (length (SegModel.mc_kept mc) <= 8)%nat.
Proof.
  intros rd m mc (bs & B & L & L32 & HS & UN & UO & UR & HL8 & HK & HP & UK & _).
  unfold seg_spec.SEG_M_SIZE in L.
  destruct UK as [V E]. unfold seg_spec.fldz, seg_spec.MC_NKEPT in E.
  set (kn := Z.to_nat 9132) in *. assert (Ekn : Z.of_nat kn = 9132) by reflexivity. clearbody kn.
  split; [|exact HL8].
  replace (m + 9132) with (m + Z.of_nat kn) by lia.
  apply (s19_val_of rd m bs kn); [exact B | lia | exact V | exact E].
Qed.

(* sa_addr of a sub-range *)
Lemma s19_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
  sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (H0 & H1 & H2 & H3 & H4) Hq Hn Hn'.
  split; [lia|]. split; [lia|]. split.
  - unfold amem_range in *. destruct H2 as [H2|[H2 H2']]; [left | right]; lia.
  - split.
    + exact (range_addressable_sub rd SHADOW_OFF q n q' n' H3 Hq Hn).
    + intros _. specialize (H4 ltac:(lia)). intros s Hs. apply H4.
      pose proof (s19_hull_mono q q' Hq) as M1.
      pose proof (s19_hull_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
      lia.
Qed.

(* the band room check_address asks past a string inside a block whose range is an amem_range *)
Lemma s19_amem_sub : forall q n q' n', amem_range q n -> q <= q' -> q' + n' <= q + n -> amem_range q' n'.
Proof.
  intros q n q' n' H Hq Hn. unfold amem_range in *.
  destruct H as [H|[H H']]; [left | right]; lia.
Qed.


(* ================================ the walk facts of the segment ================================ *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c
LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================= reader facts ======================================= *)
Lemma s19_rdword_rng : forall segs H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|cbn in Hw; discriminate Hw].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|cbn in Hw; discriminate Hw].
cbn in Hw. injection Hw as <-.
apply sa_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7.
lia.
Qed.
Lemma s19_bytes_xfer : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K H i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma s19_rconf_xfer : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s19_bytes_xfer rd rd' c bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma s19_mconf_xfer : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s19_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma s19_rdword_xfer : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v K H. rewrite (rdword_ext rd rd'); [exact H | exact K]. Qed.
Lemma s19_val_xfer : forall (rd rd' : reader) a n v,
  (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v K H k Hk. rewrite K by lia. exact (H k Hk). Qed.
(* a callee-saved register a call keeps *)
Lemma s19_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* the realigned base register s1 = (SP0 - 352) & ~31 from a 16-aligned SP0: 352 or 368 below *)
Lemma s19_s1_cases : forall z, z mod 16 = 0 ->
  (z - 352) - (z - 352) mod 32 = z - 352 \/ (z - 352) - (z - 352) mod 32 = z - 368.
Proof.
intros z Hz. pose proof (Z.mod_pos_bound (z - 352) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (z - 352) 32 ltac:(lia)) as Hd. pose proof (Z.div_mod z 16 ltac:(lia)) as Hd2.
rewrite Hz in Hd2. lia.
Qed.

(* the inner points of S10 (offsets from BASE = 0x84dc0) *)
Definition LO_CR_RA : Z := 0x940.    (* 0x85700, check_refusals returned *)
Definition LO_K857a8 : Z := 0x9e8.   (* 0x857a8, the head of the refusal loop *)
Definition LO_CA_RA : Z := 0xa24.    (* 0x857e4, check_address returned *)
Definition LO_CK_RA : Z := 0xa54.    (* 0x85814, check_knock_refused returned *)
(* the shadow band of the token runner *)
Definition s19_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* an atom plus an offset *)
Lemma s19_denot_off : forall E n v o, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n o) = Z_to_bv 64 (v + o).
Proof. intros E n v o He Hv. cbn [sv_denot]. rewrite He, unsigned_lit_small by lia. reflexivity. Qed.
(* the shadow address the code forms, ((a + o) >> 3) + the shadow base *)
Lemma s19_U_sh : forall E n bx v o, ew E n = Z_to_bv 64 v -> ew E bx = Z_to_bv 64 SB -> 0 <= v < 2 ^ 64 ->
  0 <= v + o < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n o) (SLit 3)) (SOff bx 0)) = shadow_addr (v + o).
Proof.
intros E n bx v o Hn Hb Hv Ho. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v o Hn) by lia. rewrite U_SLit, (U_atom E bx SB Hb) by (unfold SB; lia).
change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + o) / 8)) by (unfold M64; Z.div_mod_to_equations; lia).
unfold shadow_addr, SHADOW_OFF, SB. rewrite Z.add_comm. apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.
(* the complement the code forms, a xor -1 *)
Lemma s19_U_not : forall E n v o, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + o < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n o) (SLit (-1))) = lt_not (v + o).
Proof. intros E n v o Hn Hv Ho. rewrite (YI08.U_not_off E n v o Hn Hv Ho). unfold lt_not. reflexivity. Qed.
(* a register a run set, at its value (fuzz_command's lhh_reg_U) *)
Lemma s19_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* awr_ok reads only the regions' bases and windows (the S00 walk's s10_awr_skel) *)
Lemma s19_awr_skel : forall segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own,
  skeleton rs' = skeleton rs -> awr_ok segs B Ex rs STK sp0 FP bl0 blc fr0 lyx own ->
  awr_ok segs B Ex rs' STK sp0 FP bl0 blc fr0 lyx own.
Proof. intros segs B Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own Hsk H a Ha. apply H. exact (in_wrange_skeleton Ex rs' rs a Hsk Ha). Qed.
(* the signed tests of small values (n_kept, n_refusals, i) *)
Lemma s19_br_ge : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 128 -> 0 <= y < 128 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. cbn [branch_taken]. rewrite Ha, Hb, bv_lts_small by lia. reflexivity. Qed.
Lemma s19_br_lt : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 128 -> 0 <= y < 128 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. cbn [branch_taken]. rewrite Ha, Hb, bv_lts_small by lia. reflexivity. Qed.
(* a register of a state, as the symbolic state names it (fuzz_command's lhh_prraw) *)
Ltac s19_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
(* an 8-byte chunk of a region, read back as a word (the S00 walk's s10_rd_chunk8) *)
Lemma s19_rd_chunk8 : forall E H mem base off a e v cs,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  a = base + off -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a e v cs Hc Hin -> He Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 e v Hc He); [exact Hv | cbn; lia].
Qed.
End rd.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---- the image facts across a change outside the image (the S21 / ret walk's s25_lit_kept / s25_img_kept,
   image B's S21 / ret commit 315447ae529c, LLVMFuzzerTestOneInput_s25k.v:279-341) ---- *)
Lemma s19_lit_kept : forall H H' (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H' mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H' mem') a s.
Proof.
intros H H' mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H' mem' _ Hrom)].
split; [|exact Hn0].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi.
refine (proj1 (Himg (a + Z.of_nat i) _)). lia.
Qed.
Lemma s19_img_kept : forall cx H H' (mem mem' : word -> option byte),
  (forall x, kImgLo <= x < kImgEnd -> aview SEGS H' mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H' mem').
Proof.
intros cx H H' mem mem' K0 HI.
assert (K : forall x, in_img SEGS x -> aview SEGS H' mem' x = aview SEGS H mem x).
{ intros x Hx. apply K0. pose proof (pa_img_range x Hx) as Hr. unfold kImgLo. lia. }
unfold lt_img in *. destruct HI as (HRO & HIM & HGI).
destruct HIM as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
split; [|split].
- intros a Hro Ho He. rewrite K0; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + pose proof (pa_img_range a (ex_intro _ s (conj Hs Hr))) as Ha. unfold kImgLo. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgLo, kImgEnd. lia.
- unfold seg_himg.
  split.
  { intros kk Hkk. rewrite K; [exact (H1 kk Hkk)|]. refine (proj1 (H2 _ _)). lia. }
  split; [exact H2|].
  split.
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (s19_lit_kept H H' mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (s19_lit_kept H H' mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H' mem') (pin_spec.row_addr catA i)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (s19_lit_kept H H' mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hw i Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H' mem') (wordsA + 8 * Z.of_nat i)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (s19_lit_kept H H' mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn kk Hkk. rewrite K; [exact (Hv i Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H' mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H' mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros i Hi. rewrite K; [exact (HGI i Hi)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* a word chunk of a region from the word it holds *)
Lemma s19_word_chunk : forall (W : world SEGS) mem E e base off v,
  rdword (rdW W mem) (base + off) = Some v -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros W mem E e base off v Hw He.
pose proof (s19_rdword_rng _ _ _ _ _ Hw) as Hr.
apply (chunk_ok_val SEGS E _ base off 8 e v); [exact He | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
(* a value read through the ASan reader is a value of the restricted memory (A's SegRecRest.v val_mem_of_aval) *)
Lemma s19_val_mem_of_sa : forall segs H mem a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk).
unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv.
f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a 4-byte chunk of a region from the value it holds *)
Lemma s19_u32_chunk : forall (W : world SEGS) mem E e base off v,
  sa_val (rdW W mem) (base + off) 4 v -> 0 <= v < 2 ^ 32 -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 e)).
Proof.
intros W mem E e base off v Hv Hr He.
apply (chunk_ok_val SEGS E _ base off 4 e v); [exact He | cbn; lia | cbn; lia |].
exact (s19_val_mem_of_sa SEGS _ _ _ _ _ Hv).
Qed.
Lemma s19_slots_xfer : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall k, 0 <= k < 8 -> rd' (x_s1 cx + o + k) = rd (x_s1 cx + o + k)) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L K H o v Hin. rewrite (rdword_ext rd rd'); [exact (H o v Hin)|]. intros k Hk. exact (K o v Hin k Hk).
Qed.
Lemma s19_saved_xfer : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' K H i r Hn.
pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hn; discriminate)) as Hi. cbn [length LT_SAVED] in Hi.
rewrite (rdword_ext rd rd'); [exact (H i r Hn)|]. intros k Hk. apply K. lia.
Qed.

(* a range inside a live heap block is addressable, with its shadow words visible, at that state *)
Lemma s19_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
  0 <= q -> 0 < n -> sa_addr (rdW W mem) q n /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hq Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
split; [|lia].
split; [lia|]. split; [lia|].
split; [exact (amem_range_sub_app b (req_size m) q n Happ Hc ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
Lemma s19_hblk_of : forall ly S (W : world SEGS) mem md rd q n, AR SEGS B ly S W mem md ->
  lt_hblk B ly S rd q n -> 0 < n -> lt_hblk B ly S (rdW W mem) q n.
Proof.
intros ly S W mem md rd q n HAR (Hin & H4 & H16 & _) Hn.
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
exact (proj1 (s19_addr_of_heap ly S W mem md q n HAR ltac:(exists q, n; split; [exact Hin | lia]) ltac:(lia) Hn)).
Qed.

(* ---- where the frame, the side-stack frame and its shadow lie, at a cut ---- *)
Lemma s19_frame_at : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  frames S = [(3, x_fpos cx)] /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\ x_fr cx mod 32 = 0 /\
  x_sh cx = 2147450880 + x_fr cx / 8 /\
  alloc_ceiling <= x_sp0 cx - STK_LLVMFuzzerTestOneInput /\ (x_s1 cx = x_sp0 cx - 352 \/ x_s1 cx = x_sp0 cx - 368) /\
  x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\ x_s1 cx mod 32 = 0 /\ x_sp0 cx <= ly_top (x_ly cx).
Proof.
intros cx ly S W mem md k HBASE HJ.
pose proof HBASE as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & HFR0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _ & _ & _ & Hlo & _).
assert (Hfr : frames S = [(3, x_fpos cx)]) by (rewrite Hfrs, HFR0; reflexivity).
assert (HF : frame_addr ly 3 (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr; rewrite HlyF; reflexivity).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (Hal32 & Happ & _ & Hsh).
rewrite HF in Hal32, Happ, Hsh.
change (fs_frame_bytes 3) with 512 in Happ, Hsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s19_s1_cases (x_sp0 cx) Hal16) as Hs1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [exact Hfr|]. split; [exact HF|].
split; [lia|]. split; [lia|]. split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; lia|].
split; [exact Hal32|].
split; [unfold x_sh, shadow_addr, SHADOW_OFF; reflexivity|].
unfold x_s1, LT_FRAME. unfold x_sp0 in *.
split; [lia|]. split; [exact Hs1|]. split; [lia|]. split; [exact Hal16|].
split; [|lia].
rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity.
Qed.

(* ---- the facts every point of S10 carries: K856f4's premises but lt_base and sa_frm0 ---- *)
Definition s19_inv (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc c m : Z) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem) (LT_LC cx c m ++ [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem) c m (x_run cx).
(* the bytes s19_inv reads: below alloc_ceiling (the heap, the side-stack frame and the shadow, the image), and the
   s1 slots outside [104, 120) and [128, 168) (the slots S10's set-up writes) *)
Definition s19_kz (cx : lcx) (a : Z) : Prop :=
  a < alloc_ceiling \/ (x_s1 cx <= a < x_s1 cx + 104) \/ (x_s1 cx + 120 <= a < x_s1 cx + 128) \/ x_s1 cx + 168 <= a.

Lemma s19_LT_LC_off : forall cx c m o v,
  In (o, v) (LT_LC cx c m ++ [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) ->
  (16 <= o <= 64) \/ o = 120 \/ 168 <= o <= 216.
Proof.
intros cx c m o v Hin. unfold LT_LC in Hin. cbn [In app] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

Lemma s19_inv_xfer : forall cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2,
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> s19_kz cx a -> rdW W2 mem2 a = rdW W mem a) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  mo_le MT (x_S cx) S2 acc ->
  s19_inv cx ly2 S2 W2 regs2 mem2 md2 k acc c m.
Proof.
intros cx ly S W regs mem md k acc c m ly2 S2 W2 regs2 mem2 md2 HBASE HINV HJ2 P2 P3 P4 P8 P9 KK HPRM HMLE.
destruct HINV as (HCORE & Hc & Hm & SLOTS & HCM).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S200 & FSH & S184)
  & HIMG & HBL & HBUD).
destruct (s19_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ2) as HAR2.
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [E|E]; rewrite E; lia).
clear S1c. unfold STK_LLVMFuzzerTestOneInput in STKc.
assert (Klo : forall a, 0 <= a < alloc_ceiling -> rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | unfold s19_kz; left; lia]).
assert (Kst : forall a, x_s1 cx <= a < x_s1 cx + 104 -> rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | unfold s19_kz; right; left; lia]).
assert (Khi : forall a, x_s1 cx + 168 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | unfold s19_kz; right; right; right; lia]).
pose proof Hc as (Hinc & _ & _ & _). pose proof Hm as (Hinm & _ & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & Hc4 & Hcc & Hcapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & Hm4 & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hcc, Hmc.
assert (Hc2 : lt_hblk B ly2 S2 (rdW W mem) c seg_spec.SEG_C_SIZE).
{ destruct Hc as (Hin & H4 & H16 & HA). split; [exact (Permutation_in _ (Permutation_sym HPRM) Hin)|].
  split; [exact H4|]. split; [exact H16 | exact HA]. }
assert (Hm2 : lt_hblk B ly2 S2 (rdW W mem) m seg_spec.SEG_M_SIZE).
{ destruct Hm as (Hin & H4 & H16 & HA). split; [exact (Permutation_in _ (Permutation_sym HPRM) Hin)|].
  split; [exact H4|]. split; [exact H16 | exact HA]. }
split; [|split; [|split; [|split]]].
- split; [|split; [|split]].
  + split; [exact HJ2|].
    split; [rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|].
    split; [rewrite P8; exact Rs0|]. split; [rewrite P9; exact Rs1|].
    split; [apply (s19_saved_xfer cx (rdW W mem)); [intros a Ha; apply Khi; lia | exact SAVED]|].
    split; [apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Klo; lia | exact HD0]|].
    split; [apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Klo; lia | exact HD8]|].
    split; [apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Klo; lia | exact HD16]|].
    split; [apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Klo; unfold LT_FLAGW; lia | exact HFLW]|].
    split; [apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Khi; lia | exact S200]|].
    split.
    * intros i Hi. rewrite lt_fsh_len in Hi. rewrite Klo by (rewrite Esh; lia). exact (FSH i ltac:(rewrite lt_fsh_len; lia)).
    * apply (s19_rdword_xfer (rdW W mem)); [intros q Hq; apply Khi; lia | exact S184].
  + apply (s19_img_kept cx (w_H W) (w_H W2) mem mem2); [|exact HIMG].
    intros x Hx. apply Klo. unfold kImgLo, kImgEnd in Hx. lia.
  + unfold lt_blocks in *. exact (Permutation_trans HPRM HBL).
  + destruct HBUD as (B1 & B2 & B3 & _ & B5 & B6). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [exact HMLE|]. split; [exact B5 | exact B6].
- exact (s19_hblk_of ly2 S2 W2 mem2 md2 _ c _ HAR2 Hc2 ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
- exact (s19_hblk_of ly2 S2 W2 mem2 md2 _ m _ HAR2 Hm2 ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
- apply (s19_slots_xfer cx (rdW W mem)); [|exact SLOTS].
  intros o v Hin q Hq. pose proof (s19_LT_LC_off cx c m o v Hin) as Ho. apply KK; [lia|].
  unfold s19_kz. lia.
- destruct HCM as [HRC HMC]. split.
  + apply (s19_rconf_xfer (rdW W mem)); [|exact HRC].
    intros i Hi. unfold seg_spec.SEG_C_SIZE in Hi. apply Klo. lia.
  + apply (s19_mconf_xfer (rdW W mem)); [|exact HMC].
    intros i Hi. unfold seg_spec.SEG_M_SIZE in Hi. apply Klo. lia.
Qed.

(* the two blocks of the invariant, in the forms the callees' pres state them *)
Lemma s19_inv_blk : forall cx ly S (W : world SEGS) regs mem md k acc c m,
  s19_inv cx ly S W regs mem md k acc c m ->
  (c <> 0 /\ c mod 16 = 0 /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\ sa_addr (rdW W mem) c seg_spec.SEG_C_SIZE /\
   4096 <= c /\ c + seg_spec.SEG_C_SIZE <= alloc_ceiling) /\
  (m <> 0 /\ m mod 16 = 0 /\ sa_heap B ly S m seg_spec.SEG_M_SIZE /\ sa_addr (rdW W mem) m seg_spec.SEG_M_SIZE /\
   4096 <= m /\ m + seg_spec.SEG_M_SIZE <= alloc_ceiling).
Proof.
intros cx ly S W regs mem md k acc c m (HCORE & (Hinc & Hc4 & Hc16 & Hca) & (Hinm & Hm4 & Hm16 & Hma) & _).
pose proof HCORE as ((HJ & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ (proj1 HJ) Hinc) as (_ & _ & Hcc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ (proj1 HJ) Hinm) as (_ & _ & Hmc & _).
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc.
split; (split; [lia|]; split; [assumption|]; split; [|split; [assumption | split; lia]]).
- exists c, seg_spec.SEG_C_SIZE. split; [exact Hinc | lia].
- exists m, seg_spec.SEG_M_SIZE. split; [exact Hinm | lia].
Qed.
(* the events: no allocator event is past EV_MAX at a point of S10 *)
Lemma s19_inv_nev : forall cx ly S (W : world SEGS) regs mem md k acc c m,
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W regs mem md k acc c m HBASE (HCORE & _).
pose proof HCORE as ((HJ & _) & _ & _ & HBUD).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
pose proof HBUD as (Hk0 & Hr0 & Hkr & _). lia.
Qed.

(* ---- a call of a program function whose contract posts apost_base with footprint [], no allocator event,
   sa_kept of everything outside its own stack window and sa_noalloc (check_refusals, check_address,
   check_knock_refused), made with sp = s1 = S1 and s0 = SP0 (the frame pointer): the facts of S10 hold after it,
   and every byte below alloc_ceiling or at and above S1 is kept ---- *)
Hypothesis MTFL : ameter_fs_laws MT.
Lemma s19_prog_call : forall (STK1 pc : Z) cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md k acc c m
  (raw : word),
  lt_base B MT cx -> s19_inv cx ly S W regs mem md k acc c m ->
  0 <= STK1 <= 8224 ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ch, afn_pre SEGS B STK1 ly S W regs mem md ch ->
     SRr SEGS W (cfg_at SEGS pc regs mem md)
       (apost_base SEGS B STK1 [] regs ly S W mem md 0
          (fun ly' S' W' regs' mem' md' =>
             sa_kept SEGS W mem W' mem' regs STK1 (fun _ => False) /\ sa_noalloc B ly S ly' S'))) ->
  (forall (W2 : world SEGS) ly2 S2 regs2 mem2 md2,
     s19_inv cx ly2 S2 W2 regs2 mem2 md2 k acc c m -> aregs_preserved regs regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ x_s1 cx <= a) -> rdW W2 mem2 a = rdW W mem a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros STK1 pc cx ly S W regs mem md k acc c m raw HBASE HINV HSTK1 Hra Hraw Hra4 HCALL HK.
pose proof HINV as (HCORE & _).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _) & _ & _ & HBUD).
destruct (s19_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfrs & HFA & F4096 & Fceil & Fapp & F32 & Esh & STKc & S1c & SP47 & SP16 & S132 & SPtop).
assert (S1r : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (destruct S1c as [Eq|Eq]; rewrite Eq; lia).
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0)
  by (destruct S1c as [Eq|Eq]; rewrite Eq;
      [replace (x_sp0 cx - 352 - x_sp0 cx) with (-22 * 16) by lia
      | replace (x_sp0 cx - 368 - x_sp0 cx) with (-23 * 16) by lia]; apply Z_mod_mult).
unfold STK_LLVMFuzzerTestOneInput in STKc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBASE as (HPRE0 & HSTKP & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (Hsp : spZ regs = x_s1 cx) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = x_sp0 cx) by (unfold s0Z; rewrite Rs0; apply unsigned_lit_small; lia).
(* the stack from S1 to the top is readable: any frame pointer chain at S1 with s0 = SP0 *)
assert (ASP : astack_pres ly (w_H W) mem (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ eapply (astack_pres_journal SEGS B pa_segs_low); [exact HJ | exact HSTKP |].
  intros a (r & Hr & Hlo & Hhi) Ha. unfold ltoi_PG, longlA, A_LONGL, LONGL_N in Hr. cbn [In] in Hr.
  destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold x_sp0 in *. lia. }
pose proof (astack_rd_mono ly (rdW W mem) (x_sp0 cx - STK_LLVMFuzzerTestOneInput) (x_s1 cx)
  ltac:(unfold STK_LLVMFuzzerTestOneInput; lia) (astack_rd_of_pres SEGS ly (w_H W) mem _ ASP)) as ARD.
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ARD ltac:(right; right; right; lia)) as [ch1 Hch].
eapply SRr_bind.
{ apply (cl_callS B LAWS W regs mem (Z_to_bv 64 pc) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx)
    (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STK1 [] 0 (x_s1 cx - x_sp0 cx) raw ch1
    (fun ly' S' W' regs' mem' md' =>
       sa_kept SEGS W mem W' mem' regs STK1 (fun _ => False) /\ sa_noalloc B ly S ly' S') HJ).
  - rewrite Hsp. lia.
  - exact Ho16.
  - lia.
  - lia.
  - unfold STK_LLVMFuzzerTestOneInput. lia.
  - rewrite Rgp. exact Hgp0.
  - rewrite Rtp. exact Htp0.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - rewrite Hs0. replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia. exact Hch.
  - intros HPRE1. eapply SRr_mono; [exact (HCALL ch1 HPRE1)|].
    intros W3 c3 _ H3. unfold apost_base in H3. rewrite Hra in H3. exact H3.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (KEPT & NOA)).
replace (k + 0) with k in HJ2 by lia.
destruct NOA as (HPRM & -> & (f & ->)).
assert (KK : forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ x_s1 cx <= a) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha Hz. apply KEPT; [exact Ha | rewrite Hsp; lia | intros []]. }
assert (P2 : getr regs2 2 = getr regs 2) by exact (s19_pres_reg regs regs2 2%bv 2 HP ltac:(unfold acallee_saved; lia) eq_refl).
assert (P3 : getr regs2 3 = getr regs 3) by exact (s19_pres_reg regs regs2 3%bv 3 HP ltac:(unfold acallee_saved; lia) eq_refl).
assert (P4 : getr regs2 4 = getr regs 4) by exact (s19_pres_reg regs regs2 4%bv 4 HP ltac:(unfold acallee_saved; lia) eq_refl).
assert (P8 : getr regs2 8 = getr regs 8) by exact (s19_pres_reg regs regs2 8%bv 8 HP ltac:(unfold acallee_saved; lia) eq_refl).
assert (P9 : getr regs2 9 = getr regs 9) by exact (s19_pres_reg regs regs2 9%bv 9 HP ltac:(unfold acallee_saved; lia) eq_refl).
apply (HK W2 ly (set_fs f S) regs2 mem2 md2); [|exact HP | exact KK].
apply (s19_inv_xfer cx ly S W regs mem md k acc c m ly (set_fs f S) W2 regs2 mem2 md2 HBASE HINV HJ2 P2 P3 P4 P8 P9).
- intros a Ha Hz. apply KK; [exact Ha|]. unfold s19_kz in Hz. lia.
- exact HPRM.
- destruct HBUD as (_ & _ & _ & HMLE & _). exact (mo_le_set_fs_r MT MTFL _ _ f acc HMLE).
Qed.

(* ---- the head of the refusal loop (0x857a8 `ld a0,152(s1)`), turn i: the loop's registers and the five slots
   S10's set-up wrote (128 ~(M + 0x238c), 136 ~(M + 0x200c), 144 ~(C + 0x2e88), 152 C & 7 = 0, 160 SH(M + 0x23ac));
   i < n_kept ----*)
Definition s19_lslots (c m : Z) : list (Z * Z) :=
  [(128, lt_not (m + 9100)); (136, lt_not (m + 8204)); (144, lt_not (c + 11912)); (152, 0);
   (160, shadow_addr (m + 9132))].
Definition K857a8_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_kept (x_mcF cx)))%nat ->
  s19_inv cx ly S W regs mem md k acc c m ->
  lt_slots cx (rdW W mem) (s19_lslots c m) ->
  getr regs 18 = w64 (c + 11912) -> getr regs 19 = w64 (shadow_addr (c + 13512)) ->
  getr regs 21 = w64 (4 * Z.of_nat i) -> getr regs 22 = w64 (c + 13512) -> getr regs 23 = w64 (200 * Z.of_nat i) ->
  getr regs 24 = w64 (Z.of_nat i) -> getr regs 25 = w64 (m + 9132) -> getr regs 26 = w64 (m + 9100) ->
  getr regs 27 = w64 (112 * Z.of_nat i - 896) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_K857a8)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
End e.
End c.
End b.
