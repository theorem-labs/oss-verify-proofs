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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 607 of its 657 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece c (p3) of
   segment S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
   the statement s22_p3_stmt of LLVMFuzzerTestOneInput_s22k.v, the digit loop of the inlined m_split from its head
   S22_VD (0x85be8) to the continue join S22_JOIN (0x85b58) or the head of the parent loop S22_VP (0x85c58).

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new).

   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s:908-935, SegList.v:957-984):
   - 0x85be8 .. 0x85bec: a4 := a3 - 58; bltu a4, a7 (a7 = -10): the byte is not a digit -> JOIN;
   - 0x85bf0 .. 0x85bfc: s5 := s5 * 10 + (a3 & 15); bltu t1, s5 (t1 = 4094): the value passed 4094 -> JOIN;
   - 0x85c00: beq a1, a5 (a5 = -1), the UBSan trap of the cursor's increment: decided in the run by the range of a1
     (a byte of m's block, below the allocation ceiling);
   - 0x85c04 .. 0x85c10: the instrumented check (check 32) of the byte at a2 = a1 + 1, slow path 0x85c28 .. 0x85c30:
     consumed by the check runner through the shadow entry of that byte (m's block is addressable);
   - 0x85c14 .. 0x85c20: a1 += 1, a3 := lbu 0(a1), a2 += 1; bnez a3 -> VD (one digit more);
   - 0x85c24, 0x85c3c: the NUL: beqz s5 (the value 0) -> JOIN;
   - 0x85c40 .. 0x85c54: a1 := 0, s7 := a0 - s3 = pn, a0 := a0 + s10 = pn, a2 := pn + (pn = 0) = pn, a3 := ~s3 -> VP.
   No store. The proof: induction on length tail - t (tail = the bytes after the last '.'), one symbolic run per turn
   from the seed ss_vd (the registers of S22_VD_stmt as atoms, a5 / a7 / t0 / t1 as literals, a2 = a1 + 1, the next
   byte as atom 32 in a read-only region at a1, the shadow entry of that byte), split at the four branches. Every fact
   of s22_inv is carried by c_inv_kept: the runs have no write window, so every byte is kept.

   THE FORM: the image-B segment files of this walk (the S21 / ret walk's LLVMFuzzerTestOneInput_s25.v / _s25k.v,
   commit 315447ae529c: c_lit_kept / c_img_kept are its s25_lit_kept / s25_img_kept; the S01 / S02 walk's _s12k.v,
   commit c9accd8a8a50: c_hblk is its lk_hblk, c_core_kept the full-agreement case of its
   lk_core_run) and the image-A twin's exploration (image A's S14 walk (piece c), vd_seed / vd_shok). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at S22_VD (0x85be8) ----
   Every register is its own atom but t0 = 10, t1 = 4094, a5 = -1, a7 = -10 (literals, so that the compares with
   them are literal compares) and a2 = a1 + 1. Atom 32 is the next byte (at a1 + 1), in a read-only region at a1.
   The shadow base is a6 (atom 16). Facts: a1 is a byte of m's block (so a1 = -1, the trap at 0x85c00, is decided
   false in the run), a3 and atom 32 are bytes, s5 is at most 4094. The shadow entry covers the byte at a1 + 1, the
   byte check 32 reads. *)
Definition VDx : sv := SOff 16 0.
Definition VDspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition vd_reg : YP09.region := YP09.mkRegion (Some 11%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition vd_facts : facts :=
  mkFacts [ (16%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, mkAF 4096 0x7fffff800000 0); (13%nat, mkAF 0 255 0);
            (21%nat, mkAF 0 4094 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition vd_sregs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (5%bv : bv 5) (SLit 10)) (6%bv : bv 5) (SLit 4094))
    (15%bv : bv 5) (SLit 18446744073709551615)) (17%bv : bv 5) (SLit 18446744073709551606)) (12%bv : bv 5) (SOff 11 1).
Definition ss_vd : sstate := mkSS S22_VD vd_sregs [vd_reg] None vd_facts.
Definition vd_SH : list shent := [mkSHE 11 1 2].
(* the value after one more digit, as the run computes it (s5 * 10 + (a3 & 15)) *)
Definition C_V1 : sv := SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit 10)) (SAlu ALU_AND (SOff 13 0) (SLit 15)).
(* pn = a0 + s10 = DOT - &m->seg[i] *)
Definition C_PN : sv := SAlu ALU_ADD (SOff 10 0) (SOff 26 0).

(* ---- pure facts ---- *)
Lemma c_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
intros l k. revert l. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|x l].
- cbn [skipn]. rewrite (@nth_overflow Z [] j 0) by (cbn [length]; lia).
  rewrite (@nth_overflow Z [] (Datatypes.S k + j) 0) by (cbn [length]; lia). reflexivity.
- cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma c_nth_name : forall (name : list Z) di j, (Datatypes.S di + j <= length name)%nat ->
  nth (Datatypes.S di + j) (name ++ [0]) 0 = nth j (skipn (Datatypes.S di) name) 0.
Proof.
intros name di j H. rewrite c_nth_skipn.
destruct (Nat.lt_ge_cases (Datatypes.S di + j) (length name)) as [Hl | Hg].
- apply app_nth1. exact Hl.
- assert (E : (Datatypes.S di + j)%nat = length name) by lia. rewrite E.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  symmetry. apply nth_overflow. lia.
Qed.

Lemma c_land15 : forall d, 48 <= d <= 57 -> Z.land d 15 = d - 48.
Proof.
intros d Hd.
assert (Hk : exists k, (k < 10)%nat /\ d = 48 + Z.of_nat k) by (exists (Z.to_nat (d - 48)); split; lia).
destruct Hk as (k & Hk & ->). do 10 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* bltu a4, a7 at 0x85bec with a4 = a3 - 58, a7 = -10: taken exactly on a byte that is not a digit *)
Lemma c_dig_ltu : forall d, 0 <= d < 256 ->
  (zcanon (d + -58) <? 18446744073709551606) = negb (SegModel.isdigit d).
Proof. apply s22_byte_all. vm_compute. reflexivity. Qed.

Lemma c_isdigit : forall d, SegModel.isdigit d = true -> 48 <= d <= 57.
Proof.
intros d H. unfold SegModel.isdigit in H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma c_fold_S : forall (l : list Z) t, (t < length l)%nat ->
  forallb SegModel.isdigit (firstn t l) = true -> SegModel.isdigit (nth t l 0) = true ->
  forallb SegModel.isdigit (firstn (Datatypes.S t) l) = true /\
  fold_left SegModel.dstep (firstn (Datatypes.S t) l) 0 =
    SegModel.dstep (fold_left SegModel.dstep (firstn t l) 0) (nth t l 0).
Proof.
intros l t Ht Hall Hd. rewrite (s22_firstn_S l t 0 Ht). split.
- rewrite forallb_app. rewrite Hall. cbn [forallb]. rewrite Hd. reflexivity.
- rewrite fold_left_app. reflexivity.
Qed.

(* the next byte of a NUL-free name is the NUL exactly at the end of the tail *)
Lemma c_tail_nz : forall (name : list Z) di j, SegModel.nulfree name -> (j < length (skipn di name))%nat ->
  nth j (skipn di name) 0 <> 0.
Proof.
intros name di j Hnf Hj H0. apply Hnf. rewrite <- H0.
rewrite c_nth_skipn. apply nth_In. rewrite length_skipn in Hj. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- two readers that agree on every byte ---- *)
Definition c_rdeq (rd rd' : reader) : Prop := forall a, rd' a = rd a.
Lemma c_rdeq_refl : forall rd, c_rdeq rd rd.
Proof. intros rd a. reflexivity. Qed.
Lemma c_rdeq_trans : forall rd1 rd2 rd3, c_rdeq rd1 rd2 -> c_rdeq rd2 rd3 -> c_rdeq rd1 rd3.
Proof. intros rd1 rd2 rd3 K1 K2 a. rewrite K2. apply K1. Qed.
Lemma c_word : forall (rd rd' : reader) a v, c_rdeq rd rd' -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v K H. rewrite (rdword_ext rd rd' a); [exact H | intros kk _; apply K]. Qed.
Lemma c_bytes : forall rd rd' a bs, c_rdeq rd rd' -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K H j Hj. rewrite K. exact (H j Hj). Qed.
Lemma c_zs : forall rd rd' a l, c_rdeq rd rd' -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l K H j Hj. rewrite K. exact (H j Hj). Qed.
Lemma c_val : forall rd rd' a n v, c_rdeq rd rd' -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v K H j Hj. rewrite K. exact (H j Hj). Qed.

(* a run whose regions have no write window keeps every byte *)
Lemma c_frame_kept : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> c_rdeq (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' HF Hw a. apply aview_eq_of. apply HF. intros (r & Hin & Hrg).
rewrite forallb_forall in Hw. specialize (Hw r Hin). apply Z.leb_le in Hw. lia.
Qed.

(* a byte the reader shows, as a 1-byte value of the restricted memory *)
Lemma c_val1 : forall (H : word -> bool) (mem : word -> option byte) a b,
  aview SEGS H mem a = Some b -> 0 <= b < 256 -> val_mem SEGS (mrestrict H mem) a 1 b.
Proof.
intros H mem a b Hv Hb k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [bb|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hbb. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 bb), Hbb. f_equal.
cbv [YO0f.le_byte]. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* ---- the seed ---- *)
Lemma c_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem a d b v,
  getr regs 5 = w64 10 -> getr regs 6 = w64 LT_VIDMAX -> getr regs 15 = w64 (-1) -> getr regs 17 = w64 (-10) ->
  getr regs 11 = w64 a -> getr regs 12 = w64 (a + 1) -> getr regs 13 = w64 d ->
  getr regs 16 = w64 SHADOW_OFF -> getr regs 21 = w64 v ->
  4096 <= a <= 0x7fffff800000 -> 0 <= d <= 255 -> 0 <= b <= 255 -> 0 <= v <= 4094 ->
  rdW W mem (a + 1) = Some b ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 b])) ss_vd
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VD)) mem (seg_rom SEGS))).
Proof.
intros W regs mem a d b v R5 R6 R15 R17 R11 R12 R13 R16 R21 Ha Hd Hb Hv HV.
set (E := Eimg (Ereg regs [Z_to_bv 64 b])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E11 : ew E 11 = Z_to_bv 64 a) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E13 : ew E 13 = Z_to_bv 64 d) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E16 : ew E 16 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E21 : ew E 21 = Z_to_bv 64 v) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 b)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U11 : bv_unsigned (ew E 11) = a) by (rewrite E11; apply unsigned_lit_small; lia).
unfold ss_vd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold vd_sregs.
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite R12. cbn [sv_denot]. rewrite U11. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite R17. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite R15. cbn [sv_denot]. unfold w64. apply Z_to_bv64_eq_mod. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite R6. reflexivity. }
  apply regs_ok_rereg; [|reflexivity|].
  2: { rewrite R5. reflexivity. }
  apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vd_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ a 1 1 (SOff 32 0) b);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  apply c_val1; [exact HV | lia].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok vd_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E16, E11, E13, E21, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.

(* the shadow entry of the byte at a1 + 1 (check 32) *)
Lemma c_shok : forall (W : world SEGS) (regs : bvmap 5 word) mem a b,
  getr regs 16 = w64 SHADOW_OFF -> getr regs 11 = w64 a -> 0 <= a < 2 ^ 64 - 2 ->
  range_addressable (rdW W mem) SHADOW_OFF (a + 1) 1 ->
  (a + 1 < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a + 1) ->
  sh_ok SEGS VDx vd_SH (Eimg (Ereg regs [Z_to_bv 64 b])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem a b R16 R11 Ha RA Hband. unfold sh_ok, vd_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem _ VDx 11 (a + 1) 1 a 1 2 RA).
- unfold VDx. apply U_atom; [|unfold SHADOW_OFF; lia].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 16%nat 16%bv eq_refl). exact R16.
- apply U_atom; [|lia].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 11%nat 11%bv eq_refl). exact R11.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. lia.
Qed.

(* ---- the values the run computes ---- *)
(* s5 * 10 + (a3 & 15) after a digit a3 *)
Lemma c_U_v1 : forall E v d, ew E 21 = Z_to_bv 64 v -> ew E 13 = Z_to_bv 64 d -> 0 <= v <= 4094 -> 48 <= d <= 57 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit 10)) (SAlu ALU_AND (SOff 13 0) (SLit 15))) = SegModel.dstep v d.
Proof.
intros E v d H21 H13 Hv Hd. unfold SegModel.dstep.
rewrite U_SAlu, U_SMd, (U_and_lit E (SOff 13 0) 15) by lia.
rewrite (U_atom E 21 v H21), (U_atom E 13 d H13), U_lit by lia.
cbn [zalu_raw zmd_raw]. rewrite c_land15 by lia.
rewrite (zcanon_small (v * 10)) by lia. apply zcanon_small. lia.
Qed.

(* pn = a0 + s10 = (x + di) + (-x) *)
Lemma c_U_pn : forall E x di, ew E 10 = Z_to_bv 64 (x + di) -> ew E 26 = Z_to_bv 64 (- x) ->
  0 < x -> 0 <= di -> x + di < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff 10 0) (SOff 26 0)) = di.
Proof.
intros E x di H10 H26 Hx Hdi Hxd.
assert (H26' : ew E 26 = Z_to_bv 64 (2 ^ 64 - x)).
{ rewrite H26. apply Z_to_bv64_eq_mod.
  replace (- x) with ((2 ^ 64 - x) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 10 (x + di) H10) by lia. rewrite (U_atom E 26 (2 ^ 64 - x) H26') by lia.
unfold zcanon, M64. replace (x + di + (2 ^ 64 - x)) with (di + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* a2 = pn + (pn = 0) with pn >= 1 *)
Lemma c_U_a2 : forall E x di, ew E 10 = Z_to_bv 64 (x + di) -> ew E 26 = Z_to_bv 64 (- x) ->
  0 < x -> 1 <= di -> x + di < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 26 0))
         (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 26 0)) (SLit 1))) = di.
Proof.
intros E x di H10 H26 Hx Hdi Hxd.
pose proof (c_U_pn E x di H10 H26 Hx ltac:(lia) Hxd) as HP.
rewrite U_SAlu, HP, U_SAlu, HP, U_lit by lia. cbn [zalu_raw].
replace (di <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
unfold zcanon, M64. rewrite Z.mod_0_l by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

(* s7 = a0 - s3 = (x + di) + x * (-1) *)
Lemma c_U_s7 : forall E x di, ew E 10 = Z_to_bv 64 (x + di) -> ew E 19 = Z_to_bv 64 x ->
  0 <= x -> 0 <= di -> x + di < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) = di.
Proof.
intros E x di H10 H19 Hx Hdi Hxd. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E 10 (x + di) H10) by lia. rewrite (U_atom E 19 x H19) by lia. rewrite U_SLit.
unfold zcanon, M64. change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r by lia.
replace (x + di + x * 18446744073709551615) with (di + x * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma c_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* turn i adds nothing when the name does not split *)
Lemma c_decl : forall cx i, (i < length (SegModel.mc_seg (x_mcF cx)))%nat -> 0 <= fst (x_decl cx i) ->
  SegModel.m_split (SegModel.ms_name (x_seg cx i)) = None -> x_decl cx (Datatypes.S i) = x_decl cx i.
Proof. intros cx i Hi Hpos Hs. unfold x_decl. apply s22_decl_step_skip; [exact Hi | exact Hpos | right; exact Hs]. Qed.

(* ---- register reads after a run ---- *)
(* a register as the symbolic state names it (prreg without the normalisation) *)
Ltac c_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* a register the run kept *)
Ltac c_keq HS EE :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = getr ?regs0 ?r =>
    let P := fresh "P" in c_prraw HS r P; rewrite P; clear P;
    let nn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact (EE nn r eq_refl) end.
Ltac c_kept HS EE regs0 :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let Q := fresh "Q" in assert (Q : getr (ms_regs ms) r = getr regs0 r) by c_keq HS EE; rewrite Q; clear Q end.
(* a register that holds a literal *)
Ltac c_lit HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let P := fresh "P" in c_prraw HS r P; rewrite P; clear P;
    cbn [sv_denot]; unfold w64; apply Z_to_bv64_eq_mod; reflexivity end.
(* a register that holds a computed value: the goal becomes its U *)
Ltac c_U HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let P := fresh "P" in c_prraw HS r P; apply (c_reg_U _ _ _ _ _ P); clear P end.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- every fact of s22_inv at a memory that agrees on every byte ---- *)
(* the S21 / ret walk's s25_lit_kept / s25_img_kept (LLVMFuzzerTestOneInput_s25k.v, image B's S21 / ret commit
   315447ae529c) *)
Lemma c_lit_kept : forall H (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros H mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H mem' _ Hrom)].
split; [|exact Hn0].
intros j Hj. rewrite K; [exact (Hzs j Hj)|].
rewrite length_app in Hj. cbn [length] in Hj.
refine (proj1 (Himg (a + Z.of_nat j) _)). lia.
Qed.

Lemma c_img_kept : forall cx H (mem mem' : word -> option byte),
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
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (c_lit_kept H mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (c_lit_kept H mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros j Hn. destruct (Hr j Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (pin_spec.row_addr catA j)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (c_lit_kept H mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros j Hn. destruct (Hw j Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (wordsA + 8 * Z.of_nat j)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (c_lit_kept H mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros j Hn kk Hkk. rewrite K; [exact (Hv j Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros j Hj. rewrite K; [exact (HGI j Hj)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* the S01 / S02 walk's lk_hblk (LLVMFuzzerTestOneInput_s12k.v, image B's S01 / S02 commit c9accd8a8a50) *)
Lemma c_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* lt_core at a memory that agrees on every byte, with the journal there and sp, gp, tp, s0, s1 kept *)
Lemma c_core_kept : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md',
  lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  c_rdeq (rdW W mem) (rdW W mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' HC HJ' K P2 P3 P4 P8 P9.
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [intros j r Hj; exact (c_word _ _ _ _ K (HSV j r Hj))|].
  split; [exact (c_word _ _ _ _ K HH0)|].
  split; [exact (c_word _ _ _ _ K HH8)|].
  split; [exact (c_word _ _ _ _ K HH16)|].
  split; [exact (c_word _ _ _ _ K HFL)|].
  split; [exact (c_word _ _ _ _ K H200)|].
  split; [exact (c_zs _ _ _ _ K HSH)|].
  exact (c_word _ _ _ _ K H184).
- apply (c_img_kept cx (w_H W) mem mem'); [intros x _; apply K | exact HI].
- exact HBL.
- exact HBUD.
Qed.

Lemma c_inv_kept : forall cx i c m tab mt o ly S (W : world SEGS) regs mem md k acc regs' mem' md',
  s22_inv B MT cx i c m tab mt o ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  c_rdeq (rdW W mem) (rdW W mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s22_inv B MT cx i c m tab mt o ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt o ly S W regs mem md k acc regs' mem' md' HI HJ' K P2 P3 P4 P8 P9.
destruct HI as (Hi & Hdecl & HCORE & Hc & Hm & Htab & Hmt & HSL & HCM & HTABS).
pose proof (proj1 HJ') as HAR.
split; [exact Hi|]. split; [exact Hdecl|].
split; [exact (c_core_kept cx ly S W regs mem md k acc 4 o _ regs' mem' md' HCORE HJ' K P2 P3 P4 P8 P9)|].
split; [exact (c_hblk ly S W mem' md' c _ HAR (proj1 Hc))|].
split; [exact (c_hblk ly S W mem' md' m _ HAR (proj1 Hm))|].
split; [exact (c_hblk ly S W mem' md' tab _ HAR (proj1 Htab))|].
split; [exact (c_hblk ly S W mem' md' mt _ HAR (proj1 Hmt))|].
split; [intros oo vv Hin; exact (c_word _ _ _ _ K (HSL oo vv Hin))|].
split.
- destruct HCM as ((bs & Hbs & He) & (bs' & Hbs' & He')).
  split; [exists bs; split; [exact (c_bytes _ _ _ _ K Hbs) | exact He]|].
  exists bs'. split; [exact (c_bytes _ _ _ _ K Hbs') | exact He'].
- destruct HTABS as (T1 & (bs & Hbs & He) & T3 & T4 & (bs' & Hbs' & He') & T6).
  split; [exact T1|]. split; [exists bs; split; [exact (c_bytes _ _ _ _ K Hbs) | exact He]|].
  split; [exact (c_bytes _ _ _ _ K T3)|]. split; [exact (c_val _ _ _ _ _ K T4)|].
  split; [exists bs'; split; [exact (c_bytes _ _ _ _ K Hbs') | exact He'] | exact T6].
Qed.

(* ---- after a run: the model named mdr, the memory agreement K carried to the new state, the state named msc ---- *)
Ltac c_after K mdr msc HS :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?dd |} _ =>
    let mdn := fresh "mdn" in set (mdn := dd) in *; clearbody mdn; try clear mdr; rename mdn into mdr end;
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K' := fresh "Kn" in
    pose proof (c_rdeq_trans _ _ _ K (c_frame_kept _ _ _ _ _ HFr ltac:(vm_compute; reflexivity))) as K';
    clear K; rename K' into K end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
  repeat match goal with Hx : mem_grows _ _ |- _ => clear Hx end;
  try clear msc;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m0) => rename m0 into msc end.

(* ---- the loop: one turn from S22_VD, by induction on the digits left ---- *)
Lemma c_loop : forall i, S22_JOIN_stmt B MT i -> S22_VP_stmt B MT i ->
  forall n cx ly S W regs mem md k acc (c m tab mt : Z) (di t : nat) (v : Z),
  (length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) - t <= n)%nat ->
  lt_base B MT cx -> sa_frm0 ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs mem md k acc ->
  SegModel.ms_ignore (x_seg cx i) = false ->
  SegModel.strrchr (SegModel.ms_name (x_seg cx i)) 46 = Some di -> (di <> 0)%nat ->
  (t < length (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))))%nat ->
  forallb SegModel.isdigit (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) = true ->
  v = fold_left SegModel.dstep (firstn t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i)))) 0 ->
  0 <= v <= 4094 ->
  getr regs 5 = w64 10 -> getr regs 6 = w64 LT_VIDMAX ->
  getr regs 10 = w64 (seg_spec.mseg_addr m i + Z.of_nat di) ->
  getr regs 11 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t) ->
  getr regs 12 = w64 (seg_spec.mseg_addr m i + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) ->
  getr regs 13 = w64 (nth t (skipn (Datatypes.S di) (SegModel.ms_name (x_seg cx i))) 0) ->
  getr regs 15 = w64 (-1) -> getr regs 16 = w64 SHADOW_OFF -> getr regs 17 = w64 (-10) ->
  getr regs 19 = w64 (seg_spec.mseg_addr m i) -> getr regs 21 = w64 v -> getr regs 24 = w64 m ->
  s22_rk m i regs ->
  SRr SEGS W (cfg_at SEGS (BASE + S22_VD) regs mem md) (lt_post B MT cx).
Proof.
intros i HJOIN HVP n. induction n as [|n IH];
  intros cx ly S W regs mem md k acc c m tab mt di t v Hn HB Hfrm HINV Hig Hdi Hdi0 Ht Hall Hv Hvr
    R5 R6 R10 R11 R12 R13 R15 R16 R17 R19 R21 R24 HRK; [exfalso; lia|].
set (name := SegModel.ms_name (x_seg cx i)) in *.
set (tail := skipn (Datatypes.S di) name) in *.
set (base := seg_spec.mseg_addr m i) in *.
pose proof HINV as (Hi & Hdecl & HCORE & HcB & Hm & Htab & Hmt & HSL & HCM & HTABS).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & F2 & F3 & F4 & F8 & F9 & _).
pose proof (proj1 HJ) as HAR.
pose proof Hm as (HinM & Hm4 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HinM) as (_ & _ & HMceil & HMapp & _ & _ & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMceil, HMapp.
pose proof asan_consts as (C1 & _).
pose proof HRK as (K20 & K22 & K26 & K27).
assert (Hi32 : (i < 32)%nat).
{ destruct HCM as (_ & (bs & _ & (_ & Hle & _))). unfold x_mcF in Hi. lia. }
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hstr & Hlen16 & Hnf).
change (SegModel.ms_name (x_seg cx i)) with name in Hstr, Hlen16, Hnf.
change (seg_spec.mseg_addr m i) with base in Hstr.
assert (Hdl : (di < length name)%nat).
{ pose proof (SegModel.strrchr_lt name 46 di Hdi) as H. rewrite (SegModel.cut_nul_id name Hnf) in H. exact H. }
assert (Htl : length tail = (length name - Datatypes.S di)%nat) by (unfold tail; apply length_skipn).
assert (Hbase : base = m + 256 * Z.of_nat i) by (unfold base, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
destruct Hstr as (Hzs & _).
assert (RDd : rdW W mem (base + Z.of_nat (Datatypes.S di) + Z.of_nat t) = Some (nth t tail 0)).
{ replace (base + Z.of_nat (Datatypes.S di) + Z.of_nat t) with (base + Z.of_nat (Datatypes.S di + t)) by lia.
  rewrite (Hzs (Datatypes.S di + t)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. apply c_nth_name. lia. }
assert (RDb : rdW W mem (base + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1) = Some (nth (Datatypes.S t) tail 0)).
{ replace (base + Z.of_nat (Datatypes.S di) + Z.of_nat t + 1)
    with (base + Z.of_nat (Datatypes.S di + Datatypes.S t)) by lia.
  rewrite (Hzs (Datatypes.S di + Datatypes.S t)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. apply c_nth_name. lia. }
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ RDd) as Hdr.
pose proof (sa_aview_rng SEGS (w_H W) mem _ _ RDb) as Hbr.
set (d := nth t tail 0) in *.
set (b := nth (Datatypes.S t) tail 0) in *.
set (a := base + Z.of_nat (Datatypes.S di) + Z.of_nat t) in *.
assert (Ea : a = base + Z.of_nat (Datatypes.S di) + Z.of_nat t) by reflexivity.
clearbody a.
assert (Ha : 4096 <= a /\ a + 2 <= m + 9236) by lia.
assert (RA : range_addressable (rdW W mem) SHADOW_OFF (a + 1) 1).
{ apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE (a + 1) 1 HAR HinM); [lia|].
  change (req_size seg_spec.SEG_M_SIZE) with 9236. lia. }
assert (Hband : a + 1 < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= a + 1).
{ unfold in_app in HMapp. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
pose proof (c_seed W regs mem a d b v R5 R6 R15 R17 R11 R12 R13 R16 R21 ltac:(lia) ltac:(lia) ltac:(lia) Hvr RDb)
  as HS.
pose proof (c_shok W regs mem a b R16 R11 ltac:(lia) RA Hband) as SHOK.
set (E := Eimg (Ereg regs [Z_to_bv 64 b])) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r).
{ intros nn r Hnn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (E32 : ew E 32 = Z_to_bv 64 b)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clearbody E.
assert (E10 : ew E 10 = Z_to_bv 64 (base + Z.of_nat di)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 a) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E13 : ew E 13 = Z_to_bv 64 d) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E19 : ew E 19 = Z_to_bv 64 base) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 v) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = Z_to_bv 64 (- base)) by (rewrite (EE 26%nat 26%bv eq_refl); exact K26).
pose proof (c_rdeq_refl (rdW W mem)) as K.
unfold cfg_at. change (w64 (BASE + S22_VD)) with (Z_to_bv 64 (BASE + S22_VD)).
(* 0x85be8 .. 0x85bec: a4 := a3 - 58; bltu a4, a7 *)
paj_run_tok RUN HS HJ SHOK VDspan.
{ awr_ok_tac. }
c_after K mdr msc HS.
psrr_branch_tok RUN BR HS SHOK VDspan.
- (* a3 is not a digit: to the join, m_split fails *)
  assert (Hnd : SegModel.isdigit d = false).
  { rewrite branch_ltu_U, U_SOff, U_lit, E13, unsigned_lit_small in Hc by lia.
    rewrite c_dig_ltu in Hc by lia. destruct (SegModel.isdigit d); [discriminate Hc | reflexivity]. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
  { awr_ok_tac. }
  c_after K mdr msc HS.
  assert (Hsplit : SegModel.m_split name = None).
  { apply (s22_split_none_digits name di Hdi). apply (s22_digits_none_nondigit tail t Ht). exact Hnd. }
  pmkst HS.
  refine (HJOIN cx ly S W (ms_regs msc) (ms_mem msc) mdr k acc c m tab mt HB Hfrm _ _ _ _ _).
  + exact (c_decl cx i Hi (proj1 Hdecl) Hsplit).
  + exact (c_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc (ms_regs msc) (ms_mem msc) mdr HINV HJ K
      ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE)).
  + c_kept HS EE regs. exact R16.
  + c_kept HS EE regs. exact R24.
  + unfold s22_rk. split; [|split; [|split]]; c_kept HS EE regs; assumption.
- (* a3 is a digit *)
  assert (Hdig : SegModel.isdigit d = true).
  { rewrite branch_ltu_U, U_SOff, U_lit, E13, unsigned_lit_small in Hc by lia.
    rewrite c_dig_ltu in Hc by lia. destruct (SegModel.isdigit d); [reflexivity | discriminate Hc]. }
  clear Hc.
  pose proof (c_isdigit d Hdig) as Hd48.
  destruct (c_fold_S tail t Ht Hall Hdig) as (Hall1 & Hfold1).
  change (nth t tail 0) with d in Hfold1. rewrite <- Hv in Hfold1.
  (* 0x85bf0 .. 0x85bfc: s5 := s5 * 10 + (a3 & 15); bltu t1, s5 *)
  paj_run_tok RUN HS HJ SHOK VDspan.
  { awr_ok_tac. }
  c_after K mdr msc HS.
  psrr_branch_tok RUN BR HS SHOK VDspan.
  + (* the value passed 4094: to the join, m_split fails *)
    assert (Hbig : 4094 < SegModel.dstep v d).
    { rewrite branch_ltu_U, U_lit, (c_U_v1 _ v d) in Hc by first [exact E21 | exact E13 | lia].
      apply Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
    { awr_ok_tac. }
    c_after K mdr msc HS.
    assert (Hsplit : SegModel.m_split name = None).
    { apply (s22_split_none_digits name di Hdi). apply (s22_digits_none_big tail t Ht). rewrite Hfold1. exact Hbig. }
    pmkst HS.
    refine (HJOIN cx ly S W (ms_regs msc) (ms_mem msc) mdr k acc c m tab mt HB Hfrm _ _ _ _ _).
    * exact (c_decl cx i Hi (proj1 Hdecl) Hsplit).
    * exact (c_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc (ms_regs msc) (ms_mem msc) mdr HINV HJ K
        ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE)).
    * c_kept HS EE regs. exact R16.
    * c_kept HS EE regs. exact R24.
    * unfold s22_rk. split; [|split; [|split]]; c_kept HS EE regs; assumption.
  + assert (Hle : SegModel.dstep v d <= 4094).
    { rewrite branch_ltu_U, U_lit, (c_U_v1 _ v d) in Hc by first [exact E21 | exact E13 | lia].
      apply Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    assert (Hv1 : 0 <= SegModel.dstep v d) by (unfold SegModel.dstep; lia).
    (* 0x85c00 .. 0x85c20: the trap a1 = -1 (decided by a1's range), check 32 (by the shadow entry), a1 += 1,
       a3 := the next byte, a2 += 1; bnez a3 *)
    paj_run_tok RUN HS HJ SHOK VDspan.
    { awr_ok_tac. }
    c_after K mdr msc HS.
    psrr_branch_tok RUN BR HS SHOK VDspan.
    * (* the next byte is not the NUL: back to S22_VD with one digit more *)
      assert (Hb0 : b <> 0).
      { rewrite branch_ne_U, (U_atom _ 32 b), U_lit in Hc by first [exact E32 | lia].
        apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
      clear Hc.
      assert (Ht1 : (Datatypes.S t < length tail)%nat).
      { destruct (Nat.lt_ge_cases (Datatypes.S t) (length tail)) as [H|H]; [exact H|].
        exfalso. apply Hb0. unfold b. apply nth_overflow. exact H. }
      paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_VD.
      { awr_ok_tac. }
      c_after K mdr msc HS.
      pmkst HS.
      refine (IH cx ly S W (ms_regs msc) (ms_mem msc) mdr k acc c m tab mt di (Datatypes.S t) (SegModel.dstep v d)
        _ HB Hfrm _ Hig Hdi Hdi0 Ht1 Hall1 (eq_sym Hfold1) ltac:(lia) _ _ _ _ _ _ _ _ _ _ _ _ _).
      all: try change (SegModel.ms_name (x_seg cx i)) with name.
      all: try change (skipn (Datatypes.S di) name) with tail.
      all: try change (seg_spec.mseg_addr m i) with base.
      -- lia.
      -- exact (c_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc (ms_regs msc) (ms_mem msc) mdr HINV HJ K
           ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE)).
      -- c_lit HS.
      -- c_lit HS.
      -- c_kept HS EE regs. exact R10.
      -- c_U HS. rewrite (U_atom_off _ 11 a 1) by first [exact E11 | lia]. lia.
      -- c_U HS. rewrite (U_atom_off _ 11 a 2) by first [exact E11 | lia]. lia.
      -- c_U HS. change (nth (Datatypes.S t) tail 0) with b. apply U_atom; [exact E32 | lia].
      -- c_lit HS.
      -- c_kept HS EE regs. exact R16.
      -- c_lit HS.
      -- c_kept HS EE regs. exact R19.
      -- c_U HS. apply (c_U_v1 _ v d); first [exact E21 | exact E13 | lia].
      -- c_kept HS EE regs. exact R24.
      -- unfold s22_rk. split; [|split; [|split]]; c_kept HS EE regs; assumption.
    * (* the NUL: the digits ran out *)
      assert (Hbz : b = 0).
      { rewrite branch_ne_U, (U_atom _ 32 b), U_lit in Hc by first [exact E32 | lia].
        apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
      clear Hc.
      assert (Hend : Datatypes.S t = length tail).
      { destruct (Nat.lt_ge_cases (Datatypes.S t) (length tail)) as [H|H]; [|lia].
        exfalso. apply (c_tail_nz name (Datatypes.S di) (Datatypes.S t) Hnf H). exact Hbz. }
      assert (Hft : firstn (Datatypes.S t) tail = tail) by (apply firstn_all2; lia).
      rewrite Hft in Hall1, Hfold1.
      assert (Hdg : SegModel.m_digits tail 0 = Some (SegModel.dstep v d)).
      { rewrite <- Hfold1. apply s22_digits_some; [exact Hall1 | rewrite Hfold1; exact Hle]. }
      (* 0x85c24, 0x85c3c: j; beqz s5 *)
      paj_run_tok RUN HS HJ SHOK VDspan.
      { awr_ok_tac. }
      c_after K mdr msc HS.
      psrr_branch_tok RUN BR HS SHOK VDspan.
      -- (* the value 0: to the join, m_split fails *)
         assert (Hz : SegModel.dstep v d = 0).
         { rewrite branch_eq_U, (c_U_v1 _ v d), U_lit in Hc by first [exact E21 | exact E13 | lia].
           apply Z.eqb_eq in Hc. exact Hc. }
         clear Hc.
         paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_JOIN.
         { awr_ok_tac. }
         c_after K mdr msc HS.
         assert (Hsplit : SegModel.m_split name = None).
         { apply (s22_split_none_zero name di Hdi). rewrite Hz in Hdg. exact Hdg. }
         pmkst HS.
         refine (HJOIN cx ly S W (ms_regs msc) (ms_mem msc) mdr k acc c m tab mt HB Hfrm _ _ _ _ _).
         ++ exact (c_decl cx i Hi (proj1 Hdecl) Hsplit).
         ++ exact (c_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc (ms_regs msc) (ms_mem msc) mdr HINV
              HJ K ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE)).
         ++ c_kept HS EE regs. exact R16.
         ++ c_kept HS EE regs. exact R24.
         ++ unfold s22_rk. split; [|split; [|split]]; c_kept HS EE regs; assumption.
      -- (* vid in [1, 4094]: to the parent loop at t = 0 *)
         assert (Hnz : SegModel.dstep v d <> 0).
         { rewrite branch_eq_U, (c_U_v1 _ v d), U_lit in Hc by first [exact E21 | exact E13 | lia].
           apply Z.eqb_neq in Hc. exact Hc. }
         clear Hc.
         (* 0x85c40 .. 0x85c54: a1 := 0, s7 := a0 - s3, a0 := a0 + s10, a2 := a0 + (a0 = 0), a3 := ~s3 *)
         paj_run_to_tok RUNTO HS HJ SHOK VDspan S22_VP.
         { awr_ok_tac. }
         c_after K mdr msc HS.
         pmkst HS.
         refine (HVP cx ly S W (ms_regs msc) (ms_mem msc) mdr k acc c m tab mt di 0%nat (SegModel.dstep v d) HB Hfrm _ Hig
           Hdi Hdi0 Hdg ltac:(lia) ltac:(lia) eq_refl _ _ _ _ _ _ _ _ _ _).
         all: try change (seg_spec.mseg_addr m i) with base.
         ++ exact (c_inv_kept cx i c m tab mt LFO_NV ly S W regs mem md k acc (ms_regs msc) (ms_mem msc) mdr HINV
              HJ K ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE) ltac:(c_keq HS EE)).
         ++ c_lit HS.
         ++ c_lit HS.
         ++ c_U HS. apply (c_U_a2 _ base (Z.of_nat di)); first [exact E10 | exact E26 | lia].
         ++ c_U HS. rewrite (YI08.U_not _ 19 base) by first [exact E19 | lia]. unfold lt_not. reflexivity.
         ++ c_kept HS EE regs. exact R16.
         ++ c_kept HS EE regs. exact R19.
         ++ c_U HS. apply (c_U_v1 _ v d); first [exact E21 | exact E13 | lia].
         ++ c_U HS. apply (c_U_s7 _ base (Z.of_nat di)); first [exact E10 | exact E19 | lia].
         ++ c_kept HS EE regs. exact R24.
         ++ unfold s22_rk. split; [|split; [|split]]; c_kept HS EE regs; assumption.
Qed.

Lemma s22_p3 : s22_p3_stmt B MT.
Proof.
intros i HJOIN HVP cx ly S W regs mem md k acc c m tab mt di t v.
exact (c_loop i HJOIN HVP _ cx ly S W regs mem md k acc c m tab mt di t v (le_n _)).
Qed.

End e.
End f.
End d.
