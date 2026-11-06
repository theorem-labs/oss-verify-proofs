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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 567 of its 619 lines of code are new or changed and 401 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece f (p6) of segment
   S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
   the statement s22_p6_stmt of LLVMFuzzerTestOneInput_s22k.v, from the continue join S22_JOIN (0x85b58) to the head
   of turn i + 1 (cut K85b0c (S i), 0x85b0c) when i + 1 < m->n, or past the loop (cut K85e50, 0x85e50).

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new).

   THE FORM: image A's S08 walk (LLVMFuzzerTestOneInput_s17.v lt_seg_S08: a plain run
   through the stores to the frame's shadow, a split of the latch, a run to each cut, the cut facts carried by one
   transport lemma), image B's S21 / ret walk (the slot 184(s1) = SH(FR) as a chunk of an s1
   region; lt_img across a write outside the image, s25_img_kept), and the seed of image A's piece a
   (image A's S14 walk (piece a): the shadow byte of an instrumented check as a read-only region of literal 0). The code
   (dis:872-887 and 1053-1057 of dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s):
   - 0x85b58 .. 0x85b68: a0 := 184(s1) = SH(FR); sb -8 at SH(FR) + 4, 5, 6: v's three shadow bytes f8 f8 f8 (v out of
     scope, lt_fsh LFO_NV -> LFO_N);
   - 0x85b6c .. 0x85b74: check 30 of the 4-byte load of m->n: a0 := 176(s1) = SH(m + 0x2000), lb a0,0(a0): the seed
     holds that shadow byte as the literal 0 (m's block is addressable over the whole granule m + 0x2000 .. + 8), so
     bnez a0 falls through and the slow path 0x85e28 is never entered;
   - 0x85b78 .. 0x85b7c: a0 := 216(s1) = &m->n = m + 0x2000 (s8 = m), lw a0,0(a0) = m->n = length segs (sa_mconf's
     u32 at MC_N, in [0, 32], so the sign extension is the identity);
   - 0x85b80 .. 0x85b8c: s4 := i + 1, s10 := -(m + 256 (i + 1)), s11 := s6 := m + 256 (i + 1);
   - 0x85b90: blt s4, a0: split; taken (i + 1 < m->n): back to 0x85b0c, closed by LTA_K85b0c (S i) with
     x_decl (S i) = x_decl i; not taken (i + 1 = m->n): j 0x85e50, closed by LTA_K85e50 with s22_decl_all and slot
     112's value fst (x_decl i) mod 2 ^ 64 = fst (x_decl i) (0 <= fst <= i < 32).
   Every cut fact is carried by p6_keep: the runs write only v's three shadow bytes. No Section hypothesis: the
   allocator laws are YG0q.AR_laws_ok. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaStep PaShadow SegSyms SegList SegPa PaJournal SegPaLib PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at 0x85b58 ----
   Every register is its own atom (s1 = atom 9, s8 = m = atom 24, a6 = atom 16, s4 = i = atom 20). Extra atoms:
   32 = SH(FR), 33 = SH(m + 0x2000), 34 = m->n. Regions: 0 v's three shadow bytes SH(FR) + 4 .. 6, written; 1 the
   slots 176(s1) = SH(m + 0x2000), 184(s1) = SH(FR), 216(s1) = m + 0x2000, read only; 2 the shadow byte of m->n,
   read only, the literal 0; 3 m->n at m + 0x2000, read only. The fact on atom 34 (m->n in [0, 32]) makes lw's sign
   extension the identity. *)
Definition p6_r0 : YP09.region := YP09.mkRegion (Some 32%nat) 4 7 4 7 [].
Definition p6_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 176 224 0 0
  [YP09.mkChunk 176 (CVal 8 (SOff 33 0)); YP09.mkChunk 184 (CVal 8 (SOff 32 0));
   YP09.mkChunk 216 (CVal 8 (SOff 24 0x2000))].
Definition p6_r2 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition p6_r3 : YP09.region := YP09.mkRegion (Some 24%nat) 0x2000 0x2004 0 0
  [YP09.mkChunk 0x2000 (CVal 4 (SOff 34 0))].
Definition p6_facts : facts := mkFacts [(34%nat, mkAF 0 32 0)] [] [].
Definition ss_p6 : sstate := mkSS S22_JOIN sr_atoms [p6_r0; p6_r1; p6_r2; p6_r3] None p6_facts.

(* ---- pure facts ---- *)
(* v's shadow bytes are the only bytes of the frame's 36 that LFO_NV and LFO_N set apart *)
Lemma p6_fsh_same : forall j, (j < 36)%nat -> ~ (4 <= j < 7)%nat -> nth j (lt_fsh LFO_NV) 0 = nth j (lt_fsh LFO_N) 0.
Proof. intros j Hj Hn. do 36 (destruct j as [|j]; [first [reflexivity | lia] |]). lia. Qed.
Lemma p6_fsh_f8 : forall j, (4 <= j < 7)%nat -> nth j (lt_fsh LFO_N) 0 = 248.
Proof. intros j Hj. do 7 (destruct j as [|j]; [first [reflexivity | lia] |]). lia. Qed.

(* the four bytes of a u32 field holding a count of at most 32 *)
Lemma p6_u32_bytes : forall v f, 0 <= v <= 32 -> seg_spec.u32_enc v f ->
  forall k, (k < 4)%nat -> bv_unsigned (nth k f ZB0) = le_byte v 4 k.
Proof.
intros v f Hv (_ & ->) k Hk.
replace v with (Z.of_nat (Z.to_nat v)) by lia.
assert (Hn : (Z.to_nat v <= 32)%nat) by lia.
generalize (Z.to_nat v) Hn. clear v Hv Hn. intros n Hn.
do 33 (destruct n as [|n]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

(* m->n through the reader: its four bytes at m + 0x2000, and the count's bound *)
Lemma p6_mn_val : forall (rd : reader) m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & Hbs & Henc). destruct Henc as (Hlen & Hle & _ & Hn & _).
split; [|exact Hle].
intros kk Hkk.
pose (o := 8192%nat).
assert (Hoz : Z.of_nat o = 8192) by reflexivity.
assert (Hidx : (o + kk < length bs)%nat) by (unfold seg_spec.SEG_M_SIZE in Hlen; clearbody o; lia).
pose proof (Hbs (o + kk)%nat Hidx) as Hb.
replace (m + seg_spec.MC_N + Z.of_nat kk) with (m + Z.of_nat (o + kk)) by (unfold seg_spec.MC_N; clearbody o; lia).
rewrite Hb. f_equal.
assert (Hn' : nth (o + kk) bs ZB0 = nth kk (seg_spec.fldz seg_spec.MC_N 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat seg_spec.MC_N) with o. change (Z.to_nat 4) with 4%nat.
  rewrite nth_firstn. destruct (Nat.ltb_spec kk 4); [|lia]. rewrite nth_skipn. reflexivity. }
rewrite Hn'. refine (p6_u32_bytes _ _ _ Hn kk Hkk). lia.
Qed.

(* blt on two values below 2 ^ 63 is the unsigned test *)
Lemma p6_br_lt : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. unfold U in *. rewrite !bv_signed_small by assumption. reflexivity. Qed.

(* addi on a register that holds the word of a *)
Lemma p6_bv_add : forall a c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + c) = Z_to_bv 64 (a + c).
Proof.
intros a c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the s1 slots of the m_declared loop lie at 16(s1) .. 216(s1) *)
Lemma p6_slot_off : forall (cx : lcx) c m tab mt i o v,
  In (o, v) (LT_LV cx c m ++ LT_LD cx m tab mt i) -> 16 <= o <= 216.
Proof.
intros cx c m tab mt i o v Hin. unfold LT_LV, LT_LD in Hin. cbn [app In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

(* ---- facts carried from one reader to another that agrees on their bytes ---- *)
Lemma p6_bytes_xfer : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K H i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma p6_rconf_xfer : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rcf K (bs & Hb & He). exists bs. split; [|exact He].
apply (p6_bytes_xfer rd rd' c bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma p6_mconf_xfer : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
apply (p6_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma p6_rtab_xfer : forall (rd rd' : reader) a t,
  (forall i, 0 <= i < 18 * Z.of_nat (length t) -> rd' (a + i) = rd (a + i)) -> sa_rtab rd a t -> sa_rtab rd' a t.
Proof.
intros rd rd' a t K (bs & Hb & He). exists bs. split; [|exact He].
apply (p6_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma p6_mtab_xfer : forall (rd rd' : reader) a t,
  (forall i, 0 <= i < 20 * Z.of_nat (length t) -> rd' (a + i) = rd (a + i)) -> sa_mtab rd a t -> sa_mtab rd' a t.
Proof.
intros rd rd' a t K (bs & Hb & He). exists bs. split; [|exact He].
apply (p6_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma p6_guard_xfer : forall (rd rd' : reader) tab cap,
  (forall j, 0 <= j < 18 -> rd' (tab + seg_spec.RVLAN_SIZE * cap + j) = rd (tab + seg_spec.RVLAN_SIZE * cap + j)) ->
  sa_guardtab rd tab cap -> sa_guardtab rd' tab cap.
Proof.
intros rd rd' tab cap K H. unfold sa_guardtab in *. apply (p6_bytes_xfer rd rd'); [|exact H].
intros j Hj. apply K. unfold seg_spec.GUARD_BYTES in Hj. rewrite repeat_length in Hj. lia.
Qed.
Lemma p6_val_xfer : forall (rd rd' : reader) a n v,
  (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v K H k Hk. rewrite K by exact Hk. exact (H k Hk). Qed.
Lemma p6_rdword_xfer : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v K H. rewrite (rdword_ext rd rd'); [exact H | exact K]. Qed.
Lemma p6_slots_xfer : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall k, 0 <= k < 8 -> rd' (x_s1 cx + o + k) = rd (x_s1 cx + o + k)) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L K H o v Hin. rewrite (rdword_ext rd rd'); [exact (H o v Hin)|]. intros k Hk. exact (K o v Hin k Hk).
Qed.
Lemma p6_saved_xfer : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' K H i r Hn.
pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hn; discriminate)) as Hi. cbn [length LT_SAVED] in Hi.
rewrite (rdword_ext rd rd'); [exact (H i r Hn)|]. intros k Hk. apply K. lia.
Qed.


Lemma p6_rdword_rng : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|cbn in Hw; discriminate Hw].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|cbn in Hw; discriminate Hw].
cbn in Hw. injection Hw as <-.
apply sa_aview_rng in E0, E1, E2, E3, E4, E5, E6, E7.
lia.
Qed.
Lemma p6_word_chunk : forall (W : world SEGS) mem E (n : nat) base off v,
  rdword (rdW W mem) (base + off) = Some v -> ew E n = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E n base off v Hw He.
pose proof (p6_rdword_rng _ _ _ _ Hw) as Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) v);
  [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS _ _ _ _ Hw).
Qed.
(* a value read through the reader is a value of the restricted memory *)
Lemma p6_val_mem : forall H mem a n v, sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
match goal with |- _ = Z_to_bv 8 ?x => replace x with (bv_unsigned b) by (rewrite Hv; reflexivity) end.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma p6_chunk4 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sa_val (rdW W mem) (base + off) 4 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 4 _ v).
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
- cbn. lia.
- exact (p6_val_mem _ _ _ 4 _ Hrd).
Qed.
Lemma p6_chunk1z : forall (W : world SEGS) mem E base,
  rdW W mem base = Some 0 -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk 0 (CVal 1 (SLit 0))).
Proof.
intros W mem E base Hb.
apply (chunk_ok_val SEGS E _ base 0 1 _ 0); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
apply (p6_val_mem _ _ _ 1 0). intros kk Hkk. destruct kk as [|kk]; [|lia].
replace (base + 0 + Z.of_nat 0) with base by lia. rewrite Hb. reflexivity.
Qed.
(* a 1-byte chunk whose value is the word -8 reads 0xf8 *)
Lemma p6_rd_f8 : forall (W : world SEGS) mem E base off e,
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 (-8) -> rdW W mem (base + off) = Some 248.
Proof.
intros W mem E base off e Hc He. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [option_map].
vm_compute. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the image facts across a write outside the image (image B's S21 / ret walk's s25_lit_kept /
   s25_img_kept) ---- *)
Lemma p6_lit_kept : forall H (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros H mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H mem' _ Hrom)].
split; [|exact Hn0].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi.
refine (proj1 (Himg (a + Z.of_nat i) _)). lia.
Qed.
Lemma p6_img_kept : forall cx H (mem mem' : word -> option byte),
  (forall x, kImgLo <= x < kImgEnd -> aview SEGS H mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H mem').
Proof.
intros cx H mem mem' K0 HI.
assert (K : forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x).
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
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (p6_lit_kept H mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (p6_lit_kept H mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (pin_spec.row_addr catA i)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (p6_lit_kept H mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hw i Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (wordsA + 8 * Z.of_nat i)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (p6_lit_kept H mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn kk Hkk. rewrite K; [exact (Hv i Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros i Hi. rewrite K; [exact (HGI i Hi)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* ---- a harness block at a later state: rebuilt from the allocator invariant (image A's S07 / S08 walk's
   s17_hblk_of) ---- *)
Lemma p6_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
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
Lemma p6_hblk_of : forall ly S (W : world SEGS) mem md rd q n, AR SEGS B ly S W mem md ->
  lt_hblk B ly S rd q n -> 0 < n -> lt_hblk B ly S (rdW W mem) q n.
Proof.
intros ly S W mem md rd q n HAR (Hin & H4 & H16 & _) Hn.
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|].
exact (proj1 (p6_addr_of_heap ly S W mem md q n HAR ltac:(exists q, n; split; [exact Hin | lia]) ltac:(lia) Hn)).
Qed.

(* ---- the frame at a cut: where the side-stack frame, its shadow and the base register s1 lie ---- *)
Lemma p6_frame_at : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  In (3, x_fpos cx) (frames S) /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  x_sh cx = 2147450880 + x_fr cx / 8 /\
  (forall j, 0 <= j < 64 -> apresent (w_H W) mem (x_sh cx + j)) /\
  alloc_ceiling <= x_s1 cx /\ x_s1 cx + 352 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47.
Proof.
intros cx ly S W mem md k HBASE HJ.
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HF : frame_addr ly 3 (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (_ & Happ & _ & Hsh).
destruct (frames_bounds SEGS B LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H4096 & Hceilf & _).
rewrite HF in Happ, Hsh, H4096, Hceilf. change (fs_frame_bytes 3) with 512 in Happ, Hsh, Hceilf.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
rewrite HSTK in Hslo.
change (spZ (x_regs cx)) with (x_sp0 cx) in Hslo, Hshi.
pose proof (Z.mod_pos_bound (x_sp0 cx - LT_FRAME) 32 ltac:(lia)) as M32.
split; [exact Hin|]. split; [exact HF|]. split; [exact H4096|]. split; [exact Hceilf|]. split; [exact Happ|].
split; [unfold x_sh, shadow_addr, SHADOW_OFF; reflexivity|].
split; [intros j Hj; exact (proj1 (Hsh j ltac:(lia)))|].
unfold x_s1, LT_FRAME in *. lia.
Qed.

(* ---- v's three shadow bytes are the walk's to write: its own class-3 frame's shadow ---- *)
Lemma p6_awr : forall E cx ly r rs STK sp0 FP bl0 blc fr0,
  YP09.r_base r = Some 32%nat -> YP09.r_wlo r = 4 -> YP09.r_whi r = 7 -> bv_unsigned (ew E 32) = x_sh cx ->
  frame_addr ly 3 (x_fpos cx) = x_fr cx ->
  awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)] ->
  awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 ly [(LT_FCLS, x_fpos cx)].
Proof.
intros E cx ly r rs STK sp0 FP bl0 blc fr0 Hb Hlo Hhi U32 HFA Hrs.
eapply awr_ok_cons_gen; [exact Hb | exact U32 | | exact Hrs].
intros a Ha. rewrite Hlo, Hhi in Ha.
right; right; right; left. exists 3, (x_fpos cx). split; [left; reflexivity|]. right.
unfold in_zr. cbn [fst snd]. rewrite HFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh in Ha. lia.
Qed.

(* ---- the cut facts of turn i, carried across the runs: v's three shadow bytes are f8, every other byte is kept ---- *)
Lemma p6_keep : forall cx i ly S (W : world SEGS) regs mem md regs2 mem2 md2 k acc c m tab mt,
  lt_base B MT cx ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W mem2 a = rdW W mem a) ->
  (forall o, 4 <= o < 7 -> rdW W mem2 (x_sh cx + o) = Some 248) ->
  s22_inv B MT cx i c m tab mt LFO_N ly S W regs2 mem2 md2 k acc.
Proof.
intros cx i ly S W regs mem md regs2 mem2 md2 k acc c m tab mt HBASE HINV HJ2 P2 P3 P4 P8 P9 KK W3.
destruct HINV as (Hi & Hdecl & HCORE & Hc & Hm & Htab & Hmt & HSL & HCM & HTABS).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S200 & FSH & S184)
  & HIMG & HBL & HBUD).
destruct (p6_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfin & HFA & F4096 & Fceil & Fapp & Esh & SHP & S1c & S1sp & SP47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
(* the window lies in the frame's shadow: no stack, image, frame or heap byte is in it *)
assert (NWs : forall a, x_s1 cx <= a -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)) by (intros a Ha; rewrite Esh; lia).
assert (NWi : forall a, a < kImgEnd -> ~ (x_sh cx + 4 <= a < x_sh cx + 7))
  by (intros a Ha; rewrite Esh; unfold kImgEnd in Ha; lia).
assert (NWa : forall p n a, in_app p n -> p <= a < p + n -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros p n a Hin Ha Hw. rewrite Esh in Hw.
  exact (fshadow_not_app (x_fr cx) 64 p n a ltac:(lia) ltac:(lia) Hin ltac:(lia) Ha). }
assert (Kst : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | apply NWs; lia]).
assert (Kfr : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha; apply KK; [lia | exact (NWa _ _ a Fapp Ha)]).
assert (Kim : forall x, kImgLo <= x < kImgEnd -> rdW W mem2 x = rdW W mem x)
  by (intros x Hx; apply KK; [unfold kImgLo, kImgEnd in Hx; lia | apply NWi; lia]).
assert (Kblk : forall p n, In (p, n) (ablocks B ly S) -> forall a, p <= a < p + req_size n -> rdW W mem2 a = rdW W mem a).
{ intros p n Hin a Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hce & Happ & _).
  apply KK; [lia | exact (NWa _ _ a Happ Ha)]. }
pose proof HTABS as (Hlen0 & Hrt & Hgd & Hnv & Hmtb & Hmtl).
split; [exact Hi|]. split; [exact Hdecl|].
split.
{ split; [|split; [exact (p6_img_kept cx (w_H W) mem mem2 Kim HIMG) | split; [exact HBL | exact HBUD]]].
  split; [exact HJ2|].
  split; [rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|].
  split; [rewrite P8; exact Rs0|]. split; [rewrite P9; exact Rs1|].
  split; [apply (p6_saved_xfer cx (rdW W mem)); [intros a Ha; apply Kst; lia | exact SAVED]|].
  split; [apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD0]|].
  split; [apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD8]|].
  split; [apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; lia | exact HD16]|].
  split; [apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kfr; unfold LT_FLAGW; lia | exact HFLW]|].
  split; [apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kst; lia | exact S200]|].
  split.
  - intros j Hj. rewrite lt_fsh_len in Hj.
    destruct (Nat.ltb_spec j 4) as [Hlo|Hlo]; [|destruct (Nat.ltb_spec j 7) as [Hhi|Hhi]].
    + rewrite KK by (rewrite ?Esh; lia). rewrite <- (p6_fsh_same j Hj ltac:(lia)). apply FSH. rewrite lt_fsh_len. exact Hj.
    + rewrite (p6_fsh_f8 j ltac:(lia)). apply W3. lia.
    + rewrite KK by (rewrite ?Esh; lia). rewrite <- (p6_fsh_same j Hj ltac:(lia)). apply FSH. rewrite lt_fsh_len. exact Hj.
  - apply (p6_rdword_xfer (rdW W mem)); [intros q Hq; apply Kst; lia | exact S184]. }
split; [exact (p6_hblk_of ly S W mem2 md2 _ c _ HAR2 Hc ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
split; [exact (p6_hblk_of ly S W mem2 md2 _ m _ HAR2 Hm ltac:(unfold seg_spec.SEG_M_SIZE; lia))|].
split; [exact (p6_hblk_of ly S W mem2 md2 _ tab _ HAR2 Htab ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia))|].
split; [exact (p6_hblk_of ly S W mem2 md2 _ mt _ HAR2 Hmt ltac:(unfold x_mtn, seg_spec.MVLAN_SIZE; lia))|].
split.
{ apply (p6_slots_xfer cx (rdW W mem)); [|exact HSL].
  intros o v Hin q Hq. pose proof (p6_slot_off cx c m tab mt i o v Hin). apply Kst. lia. }
pose proof Hc as (Hinc & _). pose proof Hm as (Hinm & _). pose proof Htab as (Hint & _). pose proof Hmt as (Hinmt & _).
split.
{ destruct HCM as [HRC HMC].
  pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ RqC].
  pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ RqM].
  split.
  - apply (p6_rconf_xfer (rdW W mem)); [|exact HRC]. intros j Hj. apply (Kblk c _ Hinc). lia.
  - apply (p6_mconf_xfer (rdW W mem)); [|exact HMC]. intros j Hj. apply (Kblk m _ Hinm). lia. }
pose proof (req_size_pos (x_tabn cx) ltac:(unfold x_tabn, seg_spec.RVLAN_SIZE; lia)) as [_ RqT].
pose proof (req_size_pos (x_mtn cx) ltac:(unfold x_mtn, seg_spec.MVLAN_SIZE; lia)) as [_ RqMT].
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
split; [exact Hlen0|].
split; [apply (p6_rtab_xfer (rdW W mem)); [|exact Hrt]; intros j Hj; apply (Kblk tab _ Hint); lia|].
split; [apply (p6_guard_xfer (rdW W mem)); [|exact Hgd]; intros j Hj; apply (Kblk tab _ Hint);
  unfold seg_spec.RVLAN_SIZE; lia|].
split; [apply (p6_val_xfer (rdW W mem)); [|exact Hnv]; intros j Hj; apply Kfr; unfold FO_N; lia|].
split; [apply (p6_mtab_xfer (rdW W mem)); [|exact Hmtb]; intros j Hj; apply (Kblk mt _ Hinmt); lia | exact Hmtl].
Qed.

(* the write permission of a run from the seed or from a later state of it: only region 0 has a window *)
Ltac p6_awr_tac U32 HFA :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end;
  eapply p6_awr; [reflexivity | reflexivity | reflexivity | exact U32 | exact HFA |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* what a run keeps: every byte outside v's three shadow bytes *)
Ltac p6_keep_tac cx HFr U32 K :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => x_sh cx + 4 <= a < x_sh cx + 7) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
          repeat (destruct Hin' as [Hq | Hin'];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr; cbv beta; lia |]);
          destruct Hin')) as K.
(* v's three shadow bytes at the end of a run: the chunks of region 0 *)
Ltac p6_w3_tac HS U32 D8 W3 cx W ms :=
  let RG := fresh "RG" in let RGc := fresh "RGc" in
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG;
  assert (W3 : forall o, 4 <= o < 7 -> rdW W (ms_mem ms) (x_sh cx + o) = Some 248);
  [ destruct RG as (_ & _ & _ & RGc); cbn [YP09.r_base base_val YP09.r_chunks] in RGc; rewrite U32 in RGc;
    let o := fresh "o" in let Ho := fresh "Ho" in let Ho' := fresh "Ho'" in
    intros o Ho; assert (Ho' : o = 4 \/ o = 5 \/ o = 6) by lia;
    destruct Ho' as [-> | [-> | ->]];
      (eapply p6_rd_f8; [apply (proj1 (Forall_forall _ _) RGc); cbn [In]; repeat (first [left; reflexivity | right])
                        | exact D8])
  | clear RG ].

Lemma s22_p6 : s22_p6_stmt B MT.
Proof.
intros i HNX HE50. unfold S22_JOIN_stmt.
intros cx ly S W regs mem md k acc c m tab mt HBASE HFRM HDECL HINV R16 R24 HRK.
pose proof HINV as (Hi & Hdecl & HCORE & HBc & Hm & Htab & Hmt & HSL & HCM & HTABS).
destruct HRK as (R20 & R22 & R26 & R27).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & _ & _ & _ & _ & _ & _ & _ & S184) & _).
destruct (p6_frame_at cx ly S W mem md k HBASE HJ)
  as (Hfin & HFA & F4096 & Fceil & Fapp & Esh & SHP & S1c & S1sp & SP47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
(* the block m: m->n, its shadow byte, and where m lies against the frame and the shadow *)
pose proof Hm as (HinM & Hm4 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HinM) as (_ & _ & HMceil & HMapp & _ & _ & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMceil, HMapp.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR HinM Hfin) as HMF.
change LT_FCLS with 3 in HMF. rewrite HFA in HMF.
change (fs_frame_bytes 3) with 512 in HMF. change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMF.
assert (HMFd : m + 9236 <= x_fr cx \/ x_fr cx + 512 <= m) by (unfold zdisjoint in HMF; cbn [fst snd] in HMF; exact HMF).
clear HMF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HMapp.
pose proof HCM as (_ & HMC).
destruct (p6_mn_val (rdW W mem) m (x_mcF cx) HMC) as (Hval & Hle32).
set (len := length (SegModel.mc_seg (x_mcF cx))) in *.
assert (Hshb : rdW W mem (shadow_addr (m + seg_spec.MC_N)) = Some 0).
{ pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE (m + seg_spec.MC_N) 8 HAR HinM
    ltac:(unfold seg_spec.MC_N; lia) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; unfold seg_spec.MC_N; lia))
    as HRA.
  unfold seg_spec.MC_N in *.
  destruct (HRA (m + 8192) ltac:(lia)) as (s0 & Hs0 & Hok0).
  destruct (HRA (m + 8199) ltac:(lia)) as (s7 & Hs7 & Hok7).
  unfold shadow_of_addr in Hs0, Hs7.
  assert (Hq : (m + 8199) / 8 = (m + 8192) / 8) by lia.
  rewrite Hq, Hs0 in Hs7. injection Hs7 as <-.
  unfold shadow_addr. rewrite Hs0. unfold saddr_ok in Hok7. destruct Hok7 as [-> | Hok7]; [reflexivity | lia]. }
assert (SL176 : rdword (rdW W mem) (x_s1 cx + 176) = Some (shadow_addr (m + seg_spec.MC_N)))
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (SL216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HSL; unfold LT_LV, LT_LD; cbn [app In]; repeat (first [left; reflexivity | right])).
assert (HQb : 2147450880 <= shadow_addr (m + seg_spec.MC_N) <= 2147450880 + (m + 8192) / 8)
  by (unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N; lia).
assert (HQe : shadow_addr (m + seg_spec.MC_N) = 2147450880 + (m + 8192) / 8)
  by (unfold shadow_addr, SHADOW_OFF, seg_spec.MC_N; reflexivity).
(* the environment: the registers at 0x85b58, then SH(FR), SH(m + 0x2000), m->n *)
set (E := Eimg (Ereg regs [Z_to_bv 64 (x_sh cx); Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N)); Z_to_bv 64 (Z.of_nat len)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) =
  nth j [Z_to_bv 64 (x_sh cx); Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N)); Z_to_bv 64 (Z.of_nat len)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = Z_to_bv 64 (x_sh cx)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N))) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (Z.of_nat len)) by exact (EX 2%nat ltac:(lia)).
clear EX.
assert (U32 : bv_unsigned (ew E 32) = x_sh cx) by (rewrite E32; apply unsigned_lit_small; rewrite Esh; lia).
assert (U33 : bv_unsigned (ew E 33) = shadow_addr (m + seg_spec.MC_N))
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = Z.of_nat len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E24 : ew E 24 = Z_to_bv 64 m) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U24 : bv_unsigned (ew E 24) = m) by (rewrite E24; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
(* the seed of the executor at 0x85b58 *)
assert (HS : st_ok_pi SEGS VAL E ss_p6
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_JOIN)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_p6. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok, p6_r0, p6_r1, p6_r2, p6_r3;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U32. split; [lia|]. split; [rewrite Esh; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply SHP. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (p6_word_chunk W mem E 33 (x_s1 cx) 176 _ SL176 E33).
      * exact (p6_word_chunk W mem E 32 (x_s1 cx) 184 _ S184 E32).
      * apply (chunk_ok_val SEGS E _ (x_s1 cx) 216 8 (SOff 24 0x2000) (m + seg_spec.MC_N)).
        -- cbn [sv_denot]. rewrite U24. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold seg_spec.MC_N. lia.
        -- cbn. lia.
        -- exact (val_mem_of_rdword SEGS _ _ _ _ SL216).
    + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil]. exact (p6_chunk1z W mem E _ Hshb).
    + rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      exact (p6_chunk4 W mem E m 0x2000 34 (Z.of_nat len) E34 ltac:(lia) Hval).
  - apply pairwise_disjoint_of_extents. unfold p6_r0, p6_r1, p6_r2, p6_r3, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U9, U33, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HQe, Esh.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold facts_ok, p6_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U34, Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia. }
assert (AWR0 : awr_ok SEGS B E (ss_mem ss_p6) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ unfold ss_p6. cbn [ss_mem].
  apply (p6_awr E cx ly p6_r0 [p6_r1; p6_r2; p6_r3]); [reflexivity | reflexivity | reflexivity | exact U32 | exact HFA |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (UA : U E (SOff 20 1) = Z.of_nat i + 1) by (apply (U_atom_off E 20 (Z.of_nat i) 1 E20); lia).
assert (UB : U E (SOff 34 0) = Z.of_nat len) by (apply (U_atom E 34 (Z.of_nat len) E34); lia).
assert (D8 : sv_denot E (SLit 18446744073709551608) = Z_to_bv 64 (-8)).
{ apply bv_eq. change (U E (SLit 18446744073709551608) = bv_unsigned (Z_to_bv 64 (-8))).
  rewrite U_lit by lia. vm_compute. reflexivity. }
clearbody E.
unfold cfg_at. change (w64 (BASE + S22_JOIN)) with (Z_to_bv 64 (BASE + S22_JOIN)).
(* 0x85b58 .. 0x85b8c: a0 := 184(s1) = SH(FR), v's three shadow bytes := f8; a0 := 176(s1) = SH(m + 0x2000) and its
   byte 0, so bnez a0 falls through; a0 := 216(s1) = m + 0x2000, a0 := m->n; s4 := i + 1, s10 -= 256, s11 += 256,
   s6 += 256; the run stops at blt s4, a0 (0x85b90) *)
paj_run_sh RUNP HS HJ.
{ exact AWR0. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (md1 := mdx) in *; clearbody md1 end.
cbn [ms_mem mkst] in HF, HFr, HG.
p6_keep_tac cx HFr U32 K1.
clear HF HFr HG. rename ms into ms1.
psrr_branch_pi RUNP BR HS.
- (* taken: i + 1 < m->n, back to the head of turn i + 1 (0x85b0c) *)
  rewrite (p6_br_lt E (SOff 20 1) (SOff 34 0)) in Hc by (rewrite ?UA, ?UB; lia).
  rewrite UA, UB in Hc. apply Z.ltb_lt in Hc.
  assert (Hlt : (Datatypes.S i < len)%nat) by lia.
  paj_run_to_sh RUNTOP HS HJ LO_K85b0c.
  { p6_awr_tac U32 HFA. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (md2 := mdx) in *; clearbody md2 end.
  p6_keep_tac cx HFr U32 K2.
  clear HF HFr HG.
  p6_w3_tac HS U32 D8 W3 cx W ms.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (16%bv : bv 5) P16. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite (EE 16%nat 16%bv eq_refl) in P16.
  rewrite E20, p6_bv_add in P20.
  rewrite (EE 22%nat 22%bv eq_refl), R22 in P22. unfold w64 in P22. rewrite p6_bv_add in P22.
  rewrite (EE 26%nat 26%bv eq_refl), R26 in P26. unfold w64 in P26. rewrite p6_bv_add in P26.
  rewrite (EE 27%nat 27%bv eq_refl), R27 in P27. unfold w64 in P27. rewrite p6_bv_add in P27.
  pmkst HS.
  destruct (p6_keep cx i ly S W regs mem md (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HBASE HINV HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W3)
    as (_ & _ & HCORE2 & Hc2 & Hm2 & Htab2 & Hmt2 & HSL2 & HCM2 & HTABS2).
  assert (ELD : LT_LD cx m tab mt (Datatypes.S i) = LT_LD cx m tab mt i) by (unfold LT_LD; rewrite HDECL; reflexivity).
  refine (HNX fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HBASE HFRM Hlt HCORE2 Hc2 Hm2 Htab2 Hmt2
    _ _ _ _ _ _ _ HCM2 _).
  + rewrite P16. exact R16.
  + rewrite P20. unfold w64. f_equal. lia.
  + rewrite P22. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + rewrite P26. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + rewrite P27. unfold w64, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. f_equal. lia.
  + rewrite HDECL. lia.
  + rewrite ELD. exact HSL2.
  + rewrite HDECL. exact HTABS2.
- (* not taken: i + 1 = m->n, j 0x85e50, past the loop *)
  rewrite (p6_br_lt E (SOff 20 1) (SOff 34 0)) in Hc by (rewrite ?UA, ?UB; lia).
  rewrite UA, UB in Hc. apply Z.ltb_ge in Hc.
  assert (Hlast : Datatypes.S i = len) by lia.
  paj_run_to_sh RUNTOP HS HJ LO_K85e50.
  { p6_awr_tac U32 HFA. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (md2 := mdx) in *; clearbody md2 end.
  p6_keep_tac cx HFr U32 K2.
  clear HF HFr HG.
  p6_w3_tac HS U32 D8 W3 cx W ms.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (24%bv : bv 5) P24.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  rewrite E24 in P24.
  pmkst HS.
  destruct (p6_keep cx i ly S W regs mem md (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HBASE HINV HJ
    P2 P3 P4 P8 P9 ltac:(intros a Ha Hn; rewrite (K2 a Ha Hn); exact (K1 a Ha Hn)) W3)
    as (_ & _ & HCORE2 & Hc2 & Hm2 & Htab2 & Hmt2 & HSL2 & HCM2 & HTABS2).
  assert (EMD : x_decl cx i = SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)).
  { rewrite <- HDECL. unfold x_decl. apply s22_decl_all. exact Hlast. }
  refine (HE50 fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HBASE HFRM HCORE2 Hc2 Hm2 Htab2 Hmt2
    _ _ HCM2 _).
  + rewrite P24. reflexivity.
  + intros o v Hin. apply HSL2. rewrite <- EMD in Hin.
    rewrite (Z.mod_small (fst (x_decl cx i)) (2 ^ 64)) in Hin by lia.
    unfold LT_LV, LT_LD. cbn [In app] in Hin |- *.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; repeat (first [left; reflexivity | right]) |]).
    destruct Hin.
  + rewrite <- EMD. exact HTABS2.
Qed.

End e.
End f.
End d.
