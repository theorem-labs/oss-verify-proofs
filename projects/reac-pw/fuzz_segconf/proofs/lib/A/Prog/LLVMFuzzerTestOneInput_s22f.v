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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 773 of its 811 lines of code are new or changed and 415 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): piece 6 of segment S14 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s22f: the continue
   join 0x859c4 .. 0x859f8, the statement s22_p6_stmt of LLVMFuzzerTestOneInput_s22k.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s42.v (two seeds inside one function,
   a run, a branch split, both arms closed at the next cut) and chain_words_s1.v (the class-3 frame's shadow as a
   PaLibF.fshadow_region), with _s10's LLVMFuzzerTestOneInput_s10k.v (the readers s10_reg_atom / s10_zs_ok and
   the image bundle s10_img / s10_lt_img_kept).

   The code (dis:806-819 of the neutral excerpt):
   - 0x859c4 .. 0x859cc, a PLAIN run (seed A): sb s7,4(s5); sb s7,5(s5); sb s7,6(s5) with s7 = -8, so the frame's
     shadow bytes 4, 5, 6 become 0xf8: lt_fsh LFO_NV -> lt_fsh LFO_N (v out of scope). The seed's one region is
     the frame's shadow, PaLibF.fshadow_region 21 3 4 7 [], whose write window lies INSIDE the shadow band, so
     the token runner's static check (YCbn.sh_static_ok, cells_safe_b) refuses it: the three stores are a plain
     run and the rest is a second, token seed with no write window at all.
   - 0x859d0 .. 0x859f4, a TOKEN run (seed B): a0 := 152(s1) = SH(m + 0x2000) (the chunk has match_x's shape),
     lb a0,0(a0) (the check of the 4-byte load of m->n, covered by the shadow entry mkSHE 16 0x2000 0x2008 of m's
     block, so the byte is the literal 0 and bnez a0 falls through), a0 := m->n through 184(s1) = m + 0x2000, the
     four latch adds (s9 += 1, s10 -= 256, s11 += 256, s6 += 256); the run stops at blt s9,a0 (0x859f4).
   - blt s9,a0 taken (i + 1 < m->n): LTA_K858f4 at turn S i; not taken (i + 1 = m->n): j 0x85bd0 and
     LTA_K85bd0, with the kit's s22_decl_all turning x_decl cx (S i) into SegModel.m_declared. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YI09 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s22k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the imported `lia` (lib/Lib/LiaTwx2.v) fails on some linear goals; the donor's fall-back to the plain one
   (plugin-hostd/fuzz_command lib/A/Prog/LLVMFuzzerTestOneInput_s24.v:38-40) *)
Local Ltac p6z := first [ lia | Zify.zify; xlia zchecker ].


(* ======================= the two symbolic states of the join ======================= *)
(* the shadow byte's address of m + 0x2000, as the code formed it into 152(s1) (YCbn.match_x's shape) *)
Definition p6_shw : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 16 seg_spec.MC_N) (SLit 3)) (SOff 15 0).
Definition p6_Bx : sv := SOff 15 0.
Definition p6_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* seed A (0x859c4): the frame's shadow, bytes [4, 7) writable; s7 pinned to its value -8 *)
Definition p6_regA : YP09.region := fshadow_region 21 LT_FCLS 4 7 [].
Definition ss_p6A0 : sstate := mkSS S22_JOIN sr_atoms [p6_regA] None (mkFacts [] [] []).
Definition ss_p6A : sstate :=
  mkSS S22_JOIN (sr_set sr_atoms 23%bv (SLit (-8))) [p6_regA] None (mkFacts [] [] []).
(* seed B (0x859d0): the two s1 slots the join reads and the 4 bytes of m->n; no write window *)
Definition p6_slots : YP09.region := YP09.mkRegion (Some 9%nat) 152 192 0 0
  [YP09.mkChunk 152 (CVal 8 p6_shw); YP09.mkChunk 184 (CVal 8 (SOff 16 seg_spec.MC_N))].
Definition p6_mn : YP09.region := YP09.mkRegion (Some 16%nat) seg_spec.MC_N (seg_spec.MC_N + 4) 0 0
  [YP09.mkChunk seg_spec.MC_N (CVal 4 (SOff 32 0))].
Definition p6_factsB : facts := mkFacts [(15%nat, mkAF SB SB 0); (16%nat, PTR 4); (32%nat, mkAF 0 32 0)] [] [].
Definition ss_p6B : sstate := mkSS 0xc9c sr_atoms [p6_slots; p6_mn] None p6_factsB.
Definition p6_SH : list shent := [mkSHE 16 seg_spec.MC_N (seg_spec.MC_N + 8)].

(* ======================= small arithmetic and list facts ======================= *)
Lemma p6_w64_off : forall x y, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + y) = Z_to_bv 64 (x + y).
Proof.
intros x y. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod, Zmod_mod, <- Zplus_mod. reflexivity.
Qed.

Lemma p6_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. assert (Hu : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit_small; lia).
first
[ (rewrite (bv_signed_small (Z_to_bv 64 z) ltac:(rewrite Hu; lia)); exact Hu)
| (rewrite signed_lit; unfold zcanon, M64; rewrite (Z.mod_small z (2 ^ 64)) by lia;
   apply bv_swrap_small; cbn; lia) ].
Qed.

Lemma p6_blt : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb.
replace (branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b))
  with (bv_signed (Z_to_bv 64 a) <? bv_signed (Z_to_bv 64 b)) by reflexivity.
rewrite (p6_sgn a Ha), (p6_sgn b Hb). reflexivity.
Qed.

Lemma p6_mseg_S : forall m i, seg_spec.mseg_addr m (Datatypes.S i) = seg_spec.mseg_addr m i + 256.
Proof. intros m i. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. Qed.

(* the three readers of a byte range: a reader that keeps the bytes keeps the fact *)
Lemma p6_sa_bytes_kept : forall (rd rd' : reader) a bs,
  sa_bytes rd a bs -> (forall j, (j < length bs)%nat -> rd' (a + Z.of_nat j) = rd (a + Z.of_nat j)) ->
  sa_bytes rd' a bs.
Proof. intros rd rd' a bs H HK j Hj. rewrite (HK j Hj). exact (H j Hj). Qed.
Lemma p6_sa_zs_kept : forall (rd rd' : reader) a l,
  sa_zs rd a l -> (forall j, (j < length l)%nat -> rd' (a + Z.of_nat j) = rd (a + Z.of_nat j)) ->
  sa_zs rd' a l.
Proof. intros rd rd' a l H HK j Hj. rewrite (HK j Hj). exact (H j Hj). Qed.
Lemma p6_sa_val_kept : forall (rd rd' : reader) a n v,
  sa_val rd a n v -> (forall j, (j < n)%nat -> rd' (a + Z.of_nat j) = rd (a + Z.of_nat j)) ->
  sa_val rd' a n v.
Proof. intros rd rd' a n v H HK j Hj. rewrite (HK j Hj). exact (H j Hj). Qed.

(* lt_fsh LFO_N and lt_fsh LFO_NV differ only in the three bytes 4, 5, 6 of v *)
Lemma p6_fsh_same : forall j, (j < 4)%nat \/ (7 <= j < 36)%nat ->
  nth j (lt_fsh LFO_N) 0 = nth j (lt_fsh LFO_NV) 0.
Proof.
intros j Hc. do 36 (destruct j as [|j]; [solve [reflexivity | exfalso; lia] |]). exfalso; lia.
Qed.
Lemma p6_fsh_f8 : forall j, (4 <= j < 7)%nat -> nth j (lt_fsh LFO_N) 0 = 248.
Proof. intros j Hc. do 7 (destruct j as [|j]; [solve [reflexivity | exfalso; lia] |]). exfalso; lia. Qed.

(* ======================= m->n through the reader (_s20's kit text) ======================= *)
Lemma p6_nth_firstn : forall {A} (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros n j d Hj; [destruct n; destruct j; reflexivity|].
destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma p6_nth_skipn : forall {A} (l : list A) off j d, nth j (skipn off l) d = nth (off + j) l d.
Proof.
intros A l off. revert l. induction off as [|off IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; [destruct j; reflexivity|]. exact (IH l j d).
Qed.
Lemma p6_nth_fld : forall (bs : list byte) off n j d, (j < n)%nat ->
  nth j (seg_spec.fld off n bs) d = nth (off + j) bs d.
Proof. intros bs off n j d Hj. unfold seg_spec.fld. rewrite p6_nth_firstn by exact Hj. apply p6_nth_skipn. Qed.
Lemma p6_le_nth : forall n z j, 0 <= z -> (j < n)%nat ->
  bv_unsigned (nth j (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat j) mod 256.
Proof.
induction n as [|n IH]; intros z j Hz Hj; [lia|].
cbn [Z_to_le_bytes]. destruct j as [|j].
- cbn [nth]. rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by (try apply Z.shiftr_nonneg; lia).
  rewrite Z.shiftr_shiftr by lia. rewrite Nat2Z.inj_succ. f_equal. f_equal. lia.
Qed.
Lemma p6_u32_byte : forall v f j, seg_spec.u32_enc v f -> (j < 4)%nat -> bv_unsigned (nth j f ZB0) = le_byte v 4 j.
Proof.
intros v f j [Hv ->] Hj. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
assert (H64 : 2 ^ 32 < bv_modulus 64) by (vm_compute; reflexivity).
rewrite Z_to_bv_unsigned, bv_wrap_small by lia.
rewrite p6_le_nth by lia. unfold le_byte.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
Lemma p6_mconf_n : forall rd m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\
  (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & HB & L & L32 & _ & HN & _). split; [|exact L32].
intros j Hj.
assert (Hq : (Z.to_nat seg_spec.MC_N + j < length bs)%nat)
  by (unfold seg_spec.SEG_M_SIZE in L; unfold seg_spec.MC_N; lia).
pose proof (HB _ Hq) as E.
replace (m + Z.of_nat (Z.to_nat seg_spec.MC_N + j)) with (m + seg_spec.MC_N + Z.of_nat j) in E
  by (unfold seg_spec.MC_N; lia).
rewrite E. f_equal.
rewrite <- (p6_nth_fld bs (Z.to_nat seg_spec.MC_N) (Z.to_nat 4) j ZB0)
  by (change (Z.to_nat 4) with 4%nat; exact Hj).
exact (p6_u32_byte _ _ j HN Hj).
Qed.

(* ======================= the walk ======================= *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition p6_EA (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition p6_EB (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).
Lemma p6_EA_lo : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p6_EA regs) n = getr regs r.
Proof.
intros regs n r Hr. pose proof (u5_range r) as R5. unfold p6_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma p6_EB_lo : forall regs v n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p6_EB regs v) n = getr regs r.
Proof.
intros regs v n r Hr. pose proof (u5_range r) as R5. unfold p6_EB. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma p6_EB_32 : forall regs v, ew (p6_EB regs v) 32 = Z_to_bv 64 v.
Proof. intros regs v. unfold p6_EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma p6_EA_agree : forall regs, env_agree 32 (Ereg regs []) (p6_EA regs).
Proof.
intros regs. split; [intros n Hn; unfold p6_EA; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
(* a register that holds an atom plus a literal offset *)
Lemma p6_reg_off : forall (H : word -> bool) E ss ms (r : bv 5) n z,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + z).
Proof.
intros H E ss ms r n z HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* a harness block of the state at ANY state with the same blocks: the shadow facts of sa_addr are the
   allocator's, so they are re-derived rather than carried *)
Lemma p6_hblk_at : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> a mod 16 = 0 ->
  lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Ha16.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hn).
unfold MALLOC_MAX in Hn.
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
split; [exact Hin|]. split; [lia|]. split; [exact Ha16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hpos).
Qed.

Theorem s22_p6 : s22_p6_stmt B MT.
Proof using All.
intros i HNX HBD0 cx ly S W regs mem md k acc c m tab mt HBASE HFRM HDECL HINV R15 R16 R20 R21 R24 HRK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRK as (R22 & R23 & R25 & R26 & R27).
destruct HINV as (Hi & Hdpos & HCORE & HBc & HBm & HBtab & HBmt & HSL & HCM & HTABS).
destruct HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & G2 & G3 & G4 & G8 & G9 & HSAVED & HD0 & HD8 & HD16 & HDFL & HDSB & HZS).
pose proof (proj1 HJ) as HAR.
pose proof HBASE as HB0. unfold lt_base in HB0.
destruct HB0 as (HPRE & HSTP & HRO & HIM & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstkd & Hpres0 & Hch0 & HQT0).
pose proof Hstkd as (Hal16 & Hsp00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
rewrite WS in Hslo0.
assert (Hsp0r : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (Hs1r : x_sp0 cx - 352 <= x_s1 cx <= x_sp0 cx - 320).
{ unfold x_s1. pose proof (Z.mod_pos_bound (x_sp0 cx - LT_FRAME) 32 ltac:(lia)). unfold LT_FRAME in *. lia. }
(* the frame and its shadow *)
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs, Hfr0. left; reflexivity. }
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ pose proof HJ as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold x_fr, frame_addr. rewrite HF. reflexivity. }
destruct (al_frames _ _ LAWS _ _ _ _ _ LT_FCLS (x_fpos cx) HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ LT_FCLS (x_fpos cx) HAR Hfin) as (HF4096 & HFceil & HFinapp).
rewrite HFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFinapp.
change (fs_frame_bytes LT_FCLS) with 512 in *. change (512 / 8) with 64 in HFSpres.
assert (Hshlo : 2147450880 <= x_sh cx).
{ pose proof (shadow_addr_bounds (x_fr cx) ltac:(unfold kHighMemEnd in *; lia)) as Hq.
  unfold kLowMemEnd, kHighShadowEnd in Hq. unfold x_sh. clear - Hq. lia. }
assert (Hshhi : x_sh cx + 64 < 17594333495296).
{ pose proof (shadow_addr_bounds (x_fr cx + 512) ltac:(unfold kHighMemEnd in *; lia)) as Hq.
  unfold kLowMemEnd, kHighShadowEnd in Hq.
  replace (x_fr cx + 512) with (x_fr cx + 8 * 64) in Hq by lia.
  change (shadow_addr (x_fr cx + 8 * 64)) with (shadow_of_addr SHADOW_OFF (x_fr cx + 8 * 64)) in Hq.
  rewrite (shadow_of_addr_add8 SHADOW_OFF (x_fr cx) 64) in Hq.
  change (shadow_of_addr SHADOW_OFF (x_fr cx)) with (x_sh cx) in Hq. clear - Hq. lia. }
(* an address of an in_app range, of the real stack, or of the image is not one of the three bytes *)
assert (OUTAPP : forall p len a, in_app p len -> p <= a < p + len -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros p len a Hia Ha. destruct Hia as (Hp & Hor).
  unfold kLowShadowBeg, kHighMemBeg in Hor.
  destruct Hor as [Hq | [Hq1 Hq2]]; lia. }
assert (OUTB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros p n a Hin Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _ & _ & _).
  exact (OUTAPP p (req_size n) a Happ Ha). }
assert (OUTF : forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros a Ha. exact (OUTAPP (x_fr cx) 512 a HFinapp Ha). }
assert (OUTS : forall a, x_s1 cx <= a < x_sp0 cx -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros a Ha. lia. }
assert (OUTI : forall a, in_img SEGS a -> ~ (x_sh cx + 4 <= a < x_sh cx + 7)).
{ intros a Ha. pose proof (pa_img_range a Ha) as HR. unfold kImgEnd in HR. lia. }
(* the blocks' ranges *)
pose proof HBc as (HIc & Hc4096 & Hc16 & HAc).
pose proof HBm as (HIm & Hm4096 & Hm16 & HAm).
pose proof HBtab as (HItab & Htab4096 & Htab16 & HAtab).
pose proof HBmt as (HImt & Hmt4096 & Hmt16 & HAmt).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HIm) as (_ & _ & Hmceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR HIc) as (_ & _ & Hcceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md tab (x_tabn cx) HAR HItab)
  as (_ & _ & Htabceil & _ & _ & _ & Htabn).
destruct (al_blocks _ _ LAWS ly S W mem md mt (x_mtn cx) HAR HImt)
  as (_ & _ & Hmtceil & _ & _ & _ & Hmtn).
unfold MALLOC_MAX in Htabn, Hmtn.
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hmreq].
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Hcreq].
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Htabreq].
pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Hmtreq].
(* the four blocks as plain numeric ranges, so that a later `lia` needs no unfolding *)
assert (Hmr : 0 <= m /\ m + 9236 <= alloc_ceiling)
  by (clear - Hm4096 Hmceil Hmreq; unfold seg_spec.SEG_M_SIZE in *; lia).
assert (Hcr : 0 <= c /\ c + 16616 <= alloc_ceiling)
  by (clear - Hc4096 Hcceil Hcreq; unfold seg_spec.SEG_C_SIZE in *; lia).
assert (Htabr : 0 <= tab /\ tab + x_tabn cx <= alloc_ceiling)
  by (clear - Htab4096 Htabceil Htabreq Htabn; lia).
assert (Hmtr : 0 <= mt /\ mt + x_mtn cx <= alloc_ceiling)
  by (clear - Hmt4096 Hmtceil Hmtreq Hmtn; lia).
(* the model's n *)
destruct (p6_mconf_n (rdW W mem) m (seg_spec.seg_mc (x_run cx)) (proj2 HCM)) as [HMN HN32].
set (nval := Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) in *.
assert (Hnval : 0 <= nval <= 32) by (unfold nval, x_mcF; lia).
assert (Hilt : Z.of_nat i < nval) by (unfold nval; lia).
(* the table bounds *)
pose proof HTABS as (Htcap & Htab0 & Hguard & Hfn & Hmtab & Hmtlen).
assert (Htabnn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Hmtnn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.

(* ---------------- seed A: the plain run of the three shadow stores ---------------- *)
assert (EA21 : bv_unsigned (ew (p6_EA regs) 21) = x_sh cx).
{ rewrite (p6_EA_lo regs 21%nat 21%bv eq_refl), R21. apply unsigned_lit_small. lia. }
assert (HEIA : img_env VAL A_LIM (p6_EA regs)) by (unfold p6_EA; apply Eimg_env).
assert (HSA0 : st_ok_pi SEGS VAL (p6_EA regs) ss_p6A0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_JOIN)) mem (seg_rom SEGS)))).
{ unfold ss_p6A0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold p6_EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, p6_regA, fshadow_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (fs_frame_bytes LT_FCLS / 8) with 64. rewrite EA21.
    split; [lia|]. split; [lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS).
    pose proof (proj1 (HFSpres o ltac:(lia))) as Hq. unfold shadow_addr, SHADOW_OFF in Hq.
    unfold x_sh, shadow_addr, SHADOW_OFF. exact Hq.
  - apply pairwise_disjoint_of_extents.
    cbn [map extent_of_region zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [exact I | split; [exact I | exact I]]. }
pose proof (st_ok_pi_pin_reg' (p6_EA regs) ss_p6A0 _ 23%bv (-8) HSA0 R23 eq_refl) as HS.
change (mkSS (ss_pc ss_p6A0) (sr_set (ss_regs ss_p6A0) 23%bv (SLit (-8))) (ss_mem ss_p6A0) (ss_resv ss_p6A0)
  (ss_facts ss_p6A0)) with ss_p6A in HS.
clear HSA0.
paj_run_sh RUNP HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact EA21 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
  right. rewrite HFA. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS / 8) with 64.
  unfold x_sh in Ha. lia. }
rename HF into HFA1, HFr into HFrA1, HG into HGA1, ms into msA, HJ into HJA.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdA := mm) in *; clearbody mdA end.
cbn [ms_mem mkst] in HFrA1.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
  rdW W (ms_mem msA) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs := SEGS) (p6_EA regs) (ss_mem ss_p6A) (w_H W) mem (ms_mem msA)
    (fun y => x_sh cx + 4 <= y < x_sh cx + 7) HFrA1); [| exact Ha | exact Hna].
  intros b wlo whi a' Hin Hr. vm_compute in Hin. cbn [In] in Hin.
  destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hr. rewrite EA21 in Hr. lia. }
pose proof (proj1 HJA) as HARA.
(* every register but s7 is still its own atom; s7 is the literal the pin gave it *)
assert (A2 : getr (ms_regs msA) 2 = getr regs 2).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 2%bv 2%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 2%nat 2%bv eq_refl). }
assert (A3 : getr (ms_regs msA) 3 = getr regs 3).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 3%bv 3%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 3%nat 3%bv eq_refl). }
assert (A4 : getr (ms_regs msA) 4 = getr regs 4).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 4%bv 4%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 4%nat 4%bv eq_refl). }
assert (A8 : getr (ms_regs msA) 8 = getr regs 8).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 8%bv 8%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 8%nat 8%bv eq_refl). }
assert (A9 : getr (ms_regs msA) 9 = getr regs 9).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 9%bv 9%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 9%nat 9%bv eq_refl). }
assert (A20 : getr (ms_regs msA) 20 = getr regs 20).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 20%bv 20%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 20%nat 20%bv eq_refl). }
assert (A21 : getr (ms_regs msA) 21 = getr regs 21).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 21%bv 21%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 21%nat 21%bv eq_refl). }
assert (A22 : getr (ms_regs msA) 22 = getr regs 22).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 22%bv 22%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 22%nat 22%bv eq_refl). }
assert (A24 : getr (ms_regs msA) 24 = getr regs 24).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 24%bv 24%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 24%nat 24%bv eq_refl). }
assert (A25 : getr (ms_regs msA) 25 = getr regs 25).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 25%bv 25%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 25%nat 25%bv eq_refl). }
assert (A26 : getr (ms_regs msA) 26 = getr regs 26).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 26%bv 26%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 26%nat 26%bv eq_refl). }
assert (A27 : getr (ms_regs msA) 27 = getr regs 27).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 27%bv 27%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 27%nat 27%bv eq_refl). }
assert (A15 : getr (ms_regs msA) 15 = getr regs 15).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 15%bv 15%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 15%nat 15%bv eq_refl). }
assert (A16 : getr (ms_regs msA) 16 = getr regs 16).
{ rewrite (s10_reg_atom (w_H W) (p6_EA regs) _ msA 16%bv 16%nat HS ltac:(vm_compute; reflexivity)).
  exact (p6_EA_lo regs 16%nat 16%bv eq_refl). }
assert (A23 : getr (ms_regs msA) 23 = getr regs 23).
{ pose proof (st_ok_pi_restrict_reg (w_H W) (p6_EA regs) _ msA 23%bv HS) as Hq.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    change (sr_get (ss_regs ssx) 23%bv) with (SLit (-8)) in Hq end.
  rewrite Hq, R23. first [reflexivity | cbn [sv_denot]; reflexivity]. }
(* the three shadow bytes, read back from the run's chunks *)
assert (HZS3 : sa_zs (rdW W (ms_mem msA)) (x_sh cx + 4) [248; 248; 248]).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth (p6_EA regs) ssx (restrict (w_H W) msA) 0%nat r0 HS
      ltac:(vm_compute; reflexivity)) as RSH end.
  destruct RSH as (_ & _ & _ & CSH).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH. rewrite EA21 in CSH.
  exact (s10_zs_ok (p6_EA regs) (w_H W) (ms_mem msA) (x_sh cx) _ [248; 248; 248] 4 CSH
    ltac:(vm_compute; reflexivity)). }
pmkst HS.
clear HS HFA1 HFrA1 HGA1.

(* ---------------- seed B: the token run to the latch ---------------- *)
set (EB := p6_EB (ms_regs msA) nval) in *.
assert (HEIB : img_env VAL A_LIM EB) by (unfold EB, p6_EB; apply Eimg_env).
assert (EB9 : bv_unsigned (ew EB 9) = x_s1 cx).
{ unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 9%nat 9%bv eq_refl), A9, G9.
  apply unsigned_lit_small. lia. }
assert (EB15 : ew EB 15 = Z_to_bv 64 SHADOW_OFF)
  by (unfold EB; rewrite (p6_EB_lo (ms_regs msA) nval 15%nat 15%bv eq_refl), A15; exact R15).
assert (EB16 : ew EB 16 = Z_to_bv 64 m)
  by (unfold EB; rewrite (p6_EB_lo (ms_regs msA) nval 16%nat 16%bv eq_refl), A16; exact R16).
assert (EB32 : ew EB 32 = Z_to_bv 64 nval) by (unfold EB; apply p6_EB_32).
assert (UB15 : bv_unsigned (ew EB 15) = SHADOW_OFF)
  by (rewrite EB15; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UB16 : bv_unsigned (ew EB 16) = m) by (rewrite EB16; apply unsigned_lit_small; lia).
assert (UB32 : bv_unsigned (ew EB 32) = nval) by (rewrite EB32; apply unsigned_lit_small; lia).
assert (EBD : forall n z, sv_denot EB (SOff n z) = Z_to_bv 64 (bv_unsigned (ew EB n) + z))
  by (intros; reflexivity).
assert (Hq8 : 0 <= (m + seg_spec.MC_N) / 8 <= m + seg_spec.MC_N).
{ split; [apply Z.div_pos; unfold seg_spec.MC_N; lia
        | apply Z.div_le_upper_bound; unfold seg_spec.MC_N; lia]. }
assert (Hshwr : 0 <= shadow_addr (m + seg_spec.MC_N) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. clear - Hq8 Hmr C1. unfold seg_spec.MC_N in *. lia. }
assert (HU1 : U EB (SAlu ALU_SRL (SOff 16 seg_spec.MC_N) (SLit 3)) = (m + seg_spec.MC_N) / 8).
{ rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off EB 16%nat m seg_spec.MC_N EB16 ltac:(clear - Hmr C1; lia)
    ltac:(clear - Hmr C1; unfold seg_spec.MC_N; lia)).
  rewrite (U_lit EB 3 ltac:(lia)). change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64. apply Z.mod_small. clear - Hq8 Hmr C1. unfold seg_spec.MC_N in *. lia. }
assert (HU2 : U EB p6_shw = shadow_addr (m + seg_spec.MC_N)).
{ unfold p6_shw. rewrite U_SAlu. cbn [zalu_raw]. rewrite HU1.
  rewrite (U_atom EB 15%nat SHADOW_OFF EB15 ltac:(unfold SHADOW_OFF; lia)).
  unfold shadow_addr. rewrite (Z.add_comm SHADOW_OFF ((m + seg_spec.MC_N) / 8)).
  unfold zcanon, M64, SHADOW_OFF. apply Z.mod_small.
  clear - Hq8 Hmr C1. unfold seg_spec.MC_N in *. lia. }
assert (HSHW : sv_denot EB p6_shw = Z_to_bv 64 (shadow_addr (m + seg_spec.MC_N))).
{ rewrite <- HU2. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hw152 : rdword (rdW W (ms_mem msA)) (x_s1 cx + 152) = Some (shadow_addr (m + seg_spec.MC_N))).
{ rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem msA)) (x_s1 cx + 152)
    ltac:(intros j Hj; apply KA; [lia | apply OUTS; lia])).
  apply HSL. unfold s22_L. apply in_or_app. right. cbn [In]. tauto. }
assert (Hw184 : rdword (rdW W (ms_mem msA)) (x_s1 cx + 184) = Some (m + seg_spec.MC_N)).
{ rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem msA)) (x_s1 cx + 184)
    ltac:(intros j Hj; apply KA; [lia | apply OUTS; lia])).
  apply HSL. unfold s22_L, LT_LV. apply in_or_app. left. cbn [In]. tauto. }
assert (HMNA : sa_val (rdW W (ms_mem msA)) (m + seg_spec.MC_N) 4 nval).
{ apply (p6_sa_val_kept (rdW W mem) (rdW W (ms_mem msA)) (m + seg_spec.MC_N) 4 nval HMN).
  intros j Hj. apply KA; [unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia|].
  apply (OUTB m seg_spec.SEG_M_SIZE); [exact HIm | unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia]. }
assert (HS : st_ok_pi SEGS VAL EB ss_p6B
  (restrict (w_H W) (mkst (ms_regs msA) (Z_to_bv 64 (BASE + 0xc9c)) (ms_mem msA) (seg_rom SEGS)))).
{ unfold ss_p6B. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold EB, p6_EB. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, p6_slots.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EB9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS EB _ (x_s1 cx) 152 8 p6_shw (shadow_addr (m + seg_spec.MC_N)));
        [ exact HSHW | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword SEGS (w_H W) (ms_mem msA) _ _ Hw152).
      * apply (chunk_ok_val SEGS EB _ (x_s1 cx) 184 8 (SOff 16 seg_spec.MC_N) (m + seg_spec.MC_N));
        [ cbn [sv_denot]; rewrite EB16, unsigned_lit_small by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia
        | lia |].
        exact (val_mem_of_rdword SEGS (w_H W) (ms_mem msA) _ _ Hw184).
    + unfold region_ok, p6_mn.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UB16. split; [unfold seg_spec.MC_N; lia|].
      split; [unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EB _ m seg_spec.MC_N 4 (SOff 32 0) nval);
      [ cbn [sv_denot]; rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
      change (N.to_nat 4) with 4%nat.
      exact (val_mem_of_rd32 SEGS (w_H W) (ms_mem msA) (m + seg_spec.MC_N) nval HMNA).
  - apply pairwise_disjoint_of_extents.
    unfold p6_slots, p6_mn, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    cbn [base_val]. rewrite EB9, UB16. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split. right.
    unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. lia.
  - split; [|split; [exact I | exact I]].
    cbn [p6_factsB f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite UB15, UB16, UB32. unfold SB. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
    unfold SHADOW_OFF, seg_spec.SEG_M_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; first [exact Hm16 | lia]. }
assert (SHOK : sh_ok SEGS p6_Bx p6_SH EB (mrestrict (w_H W) (ms_mem msA))).
{ unfold sh_ok, p6_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem msA) EB p6_Bx 16%nat m (req_size seg_spec.SEG_M_SIZE) m
    seg_spec.MC_N (seg_spec.MC_N + 8)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdA m seg_spec.SEG_M_SIZE m
      (req_size seg_spec.SEG_M_SIZE) HARA HIm ltac:(lia) ltac:(lia)).
  - unfold p6_Bx. exact (U_atom EB 15%nat SHADOW_OFF EB15 ltac:(unfold SHADOW_OFF; lia)).
  - exact (U_atom EB 16%nat m EB16 ltac:(lia)).
  - unfold seg_spec.MC_N. lia.
  - unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *. lia.
  - intros x Hx. change (Z.min seg_spec.MC_N (seg_spec.MC_N + 8)) with seg_spec.MC_N in Hx.
    change (Z.max seg_spec.MC_N (seg_spec.MC_N + 8)) with (seg_spec.MC_N + 8) in Hx.
    destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HIm) as (_ & _ & _ & (Hp & Hor) & _).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, seg_spec.MC_N, seg_spec.SEG_M_SIZE in *.
    destruct Hor as [Hq | [Hq1 Hq2]]; lia. }
paj_run_tok RUN HS HJA SHOK p6_span.
{ awr_ok_tac. }
rename HF into HFB1, HFr into HFrB1, HG into HGB1, ms into msB, HJA into HJB.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdB := mm) in *; clearbody mdB end.
cbn [ms_mem mkst] in HFrB1.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msB) a = rdW W (ms_mem msA) a).
{ intros a Ha.
  apply (kept_of_frame (segs := SEGS) EB (ss_mem ss_p6B) (w_H W) (ms_mem msA) (ms_mem msB)
    (fun _ : Z => False) HFrB1); [| exact Ha | intros []].
  intros b wlo whi a' Hin Hr. vm_compute in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
  destruct Hin. }
assert (EB25 : bv_unsigned (ew EB 25) = Z.of_nat i).
{ unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 25%nat 25%bv eq_refl), A25, R25.
  apply unsigned_lit_small. lia. }
psrr_branch_tok RUN BR HS SHOK p6_span.
rewrite !EBD, EB25, UB32, Z.add_0_r in Hc.
rewrite (p6_blt (Z.of_nat i + 1) nval ltac:(lia) ltac:(lia)) in Hc.

- (* blt taken: i + 1 < m->n, on to turn S i at 0x858f4 *)
  assert (HiS : (Datatypes.S i < length (SegModel.mc_seg (x_mcF cx)))%nat).
  { apply Z.ltb_lt in Hc. unfold nval in Hc. lia. }
  paj_run_to_tok RUNTO HS HJB SHOK p6_span LO_K858f4.
  { awr_ok_tac. }
  rename HF into HFC, HFr into HFrC, HG into HGC, ms into msK, HJB into HJK.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdK := mm) in *; clearbody mdK end.
  cbn [ms_mem mkst] in HFrC.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msK) a = rdW W (ms_mem msB) a).
  { intros a Ha.
    lazymatch type of HFrC with frame_of _ ?rsx _ _ =>
      apply (kept_of_frame (segs := SEGS) EB rsx (w_H W) (ms_mem msB) (ms_mem msK)
        (fun _ : Z => False) HFrC); [| exact Ha | intros []] end.
    intros b wlo whi a' Hin Hr. vm_compute in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
    destruct Hin. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem msK) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (KC a Ha), (KB a Ha); exact (KA a Ha Hna)).
  assert (KW : forall a v, (forall j, 0 <= j < 8 -> ~ (x_sh cx + 4 <= a + j < x_sh cx + 7)) ->
    0 <= a -> a + 8 <= 2 ^ 64 -> rdword (rdW W mem) a = Some v ->
    rdword (rdW W (ms_mem msK)) a = Some v).
  { intros a v Hw Ha Ha8 H.
    rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem msK)) a
      ltac:(intros j Hj; apply KALL; [lia | apply Hw; lia])). exact H. }
  pose proof (proj1 HJK) as HARK.
  (* the registers at the cut *)
  assert (F2 : getr (ms_regs msK) 2 = w64 (x_s1 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 2%bv 2%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 2%nat 2%bv eq_refl), A2. exact G2. }
  assert (F3 : getr (ms_regs msK) 3 = getr (x_regs cx) 3).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 3%bv 3%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 3%nat 3%bv eq_refl), A3. exact G3. }
  assert (F4 : getr (ms_regs msK) 4 = getr (x_regs cx) 4).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 4%bv 4%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 4%nat 4%bv eq_refl), A4. exact G4. }
  assert (F8 : getr (ms_regs msK) 8 = w64 (x_sp0 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 8%bv 8%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 8%nat 8%bv eq_refl), A8. exact G8. }
  assert (F9 : getr (ms_regs msK) 9 = w64 (x_s1 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 9%bv 9%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 9%nat 9%bv eq_refl), A9. exact G9. }
  assert (F15 : getr (ms_regs msK) 15 = w64 SHADOW_OFF).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 15%bv 15%nat HS ltac:(vm_compute; reflexivity)). exact EB15. }
  assert (F16 : getr (ms_regs msK) 16 = w64 m).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 16%bv 16%nat HS ltac:(vm_compute; reflexivity)). exact EB16. }
  assert (F20 : getr (ms_regs msK) 20 = w64 4).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 20%bv 20%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 20%nat 20%bv eq_refl), A20. exact R20. }
  assert (F21 : getr (ms_regs msK) 21 = w64 (x_sh cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 21%bv 21%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 21%nat 21%bv eq_refl), A21. exact R21. }
  assert (F23 : getr (ms_regs msK) 23 = w64 (-8)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 23%bv 23%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 23%nat 23%bv eq_refl), A23. exact R23. }
  assert (F24 : getr (ms_regs msK) 24 = w64 tab).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 24%bv 24%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 24%nat 24%bv eq_refl), A24. exact R24. }
  assert (F22 : getr (ms_regs msK) 22 = w64 (seg_spec.mseg_addr m (Datatypes.S i))).
  { rewrite (p6_reg_off (w_H W) EB _ msK 22%bv 22%nat 256 HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 22%nat 22%bv eq_refl), A22, R22.
    unfold w64. rewrite p6_w64_off, (p6_mseg_S m i). reflexivity. }
  assert (F27 : getr (ms_regs msK) 27 = w64 (seg_spec.mseg_addr m (Datatypes.S i))).
  { rewrite (p6_reg_off (w_H W) EB _ msK 27%bv 27%nat 256 HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 27%nat 27%bv eq_refl), A27, R27.
    unfold w64. rewrite p6_w64_off, (p6_mseg_S m i). reflexivity. }
  assert (F25 : getr (ms_regs msK) 25 = w64 (Z.of_nat (Datatypes.S i))).
  { rewrite (p6_reg_off (w_H W) EB _ msK 25%bv 25%nat 1 HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 25%nat 25%bv eq_refl), A25, R25.
    unfold w64. rewrite p6_w64_off. f_equal. lia. }
  assert (F26 : getr (ms_regs msK) 26 = w64 (- seg_spec.mseg_addr m (Datatypes.S i))).
  { rewrite (p6_reg_off (w_H W) EB _ msK 26%bv 26%nat (-256) HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 26%nat 26%bv eq_refl), A26, R26.
    unfold w64. rewrite p6_w64_off, (p6_mseg_S m i). f_equal. lia. }
  (* the context at the cut *)
  assert (HSAVED' : lt_saved cx (rdW W (ms_mem msK))).
  { intros j r Hj.
    assert (Hj13 : (j < 13)%nat)
      by (pose proof (proj1 (nth_error_Some LT_SAVED j) ltac:(rewrite Hj; discriminate)) as Hq;
          cbn [LT_SAVED length] in Hq; lia).
    apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia |]. exact (HSAVED j r Hj). }
  assert (HIMG' : lt_img B cx (rdW W (ms_mem msK))).
  { apply (s10_lt_img_kept B IMGS BSYM cx W (ms_mem msK) (rdW W mem) HARK); [|exact HIMG].
    intros a Ha _ _. apply KALL; [pose proof (pa_img_range a Ha); unfold kImgEnd in *; lia | exact (OUTI a Ha)]. }
  assert (HSL' : lt_slots cx (rdW W (ms_mem msK)) (s22_L cx i c m mt)).
  { intros o v Hin.
    assert (Ho : 0 <= o /\ o <= 184).
    { unfold s22_L in Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; unfold LT_LV in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq; intros; subst; lia |]); destruct Hin. }
    apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia |]. exact (HSL o v Hin). }
  assert (HCM' : lt_cm (rdW W (ms_mem msK)) c m (x_run cx)).
  { destruct HCM as [(bsc & HBc1 & HEc) (bsm & HBm1 & HEm)]. split.
    - exists bsc. split; [|exact HEc].
      apply (p6_sa_bytes_kept (rdW W mem) _ c bsc HBc1). intros j Hj.
      pose proof (proj1 HEc) as Hlc.
      apply KALL; [unfold seg_spec.SEG_C_SIZE in *; lia|].
      apply (OUTB c seg_spec.SEG_C_SIZE); [exact HIc | unfold seg_spec.SEG_C_SIZE in *; lia].
    - exists bsm. split; [|exact HEm].
      apply (p6_sa_bytes_kept (rdW W mem) _ m bsm HBm1). intros j Hj.
      pose proof (proj1 HEm) as Hlm.
      apply KALL; [unfold seg_spec.SEG_M_SIZE in *; lia|].
      apply (OUTB m seg_spec.SEG_M_SIZE); [exact HIm | unfold seg_spec.SEG_M_SIZE in *; lia]. }
  assert (HTABS' : lt_tabs cx (rdW W (ms_mem msK)) tab mt (snd (x_decl cx i))).
  { split; [exact Htcap|]. split; [|split; [|split; [|split]]].
    - destruct Htab0 as (bst & HBt1 & HEt). exists bst. split; [|exact HEt].
      apply (p6_sa_bytes_kept (rdW W mem) _ tab bst HBt1). intros j Hj.
      pose proof (proj1 HEt) as Hlt.
      apply KALL; [lia|]. apply (OUTB tab (x_tabn cx)); [exact HItab | lia].
    - unfold sa_guardtab in Hguard |- *.
      apply (p6_sa_bytes_kept (rdW W mem) _ _ _ Hguard). intros j Hj.
      change (length seg_spec.GUARD_BYTES) with 18%nat in Hj.
      apply KALL; [unfold seg_spec.RVLAN_SIZE in *; lia|].
      apply (OUTB tab (x_tabn cx)); [exact HItab | unfold seg_spec.RVLAN_SIZE in *; lia].
    - apply (p6_sa_val_kept (rdW W mem) _ _ _ _ Hfn). intros j Hj.
      apply KALL; [unfold FO_N in *; lia|]. apply OUTF. unfold FO_N. lia.
    - destruct Hmtab as (bsm & HBm1 & HEm). exists bsm. split; [|exact HEm].
      apply (p6_sa_bytes_kept (rdW W mem) _ mt bsm HBm1). intros j Hj.
      pose proof (proj1 HEm) as Hlm.
      apply KALL; [lia|]. apply (OUTB mt (x_mtn cx)); [exact HImt | lia].
    - exact Hmtlen. }
  assert (HZSK : sa_zs (rdW W (ms_mem msK)) (x_sh cx) (lt_fsh LFO_N)).
  { intros j Hj. rewrite lt_fsh_len in Hj.
    destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
    - rewrite (p6_fsh_same j ltac:(left; lia)). rewrite KALL by lia. exact (HZS j ltac:(rewrite lt_fsh_len; lia)).
    - destruct (Nat.lt_ge_cases j 7) as [Hj7 | Hj7].
      + rewrite (p6_fsh_f8 j ltac:(lia)).
        rewrite KC by lia. rewrite KB by lia.
        replace (x_sh cx + Z.of_nat j) with (x_sh cx + 4 + Z.of_nat (j - 4)) by lia.
        rewrite (HZS3 (j - 4)%nat ltac:(cbn [length]; lia)).
        f_equal. destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn [Nat.sub nth]; try reflexivity; lia.
      + rewrite (p6_fsh_same j ltac:(right; lia)). rewrite KALL by lia.
        exact (HZS j ltac:(rewrite lt_fsh_len; lia)). }
  assert (HCORE' : lt_core B MT cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]).
  { split; [|split; [exact HIMG' | split; [exact HBL | exact HBUD]]].
    unfold lt_frame.
    split; [exact HJK|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
    split; [exact F8|]. split; [exact F9|]. split; [exact HSAVED'|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD0]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD8]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD16]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; unfold LT_FLAGW; lia | unfold LT_FLAGW; lia
                      | unfold LT_FLAGW; lia | exact HDFL]|].
    split; [apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia | exact HDSB]|].
    exact HZSK. }
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K858f4) (ms_regs msK) (ms_mem msK) mdK) (lt_post B MT cx)).
  apply (HNX fx cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc c m tab mt HBASE HFRM HiS HCORE').
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK c seg_spec.SEG_C_SIZE HARK HIc Hc16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK m seg_spec.SEG_M_SIZE HARK HIm Hm16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK tab (x_tabn cx) HARK HItab Htab16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK mt (x_mtn cx) HARK HImt Hmt16).
  + exact F15.
  + exact F16.
  + exact F20.
  + exact F21.
  + exact F22.
  + exact F23.
  + exact F24.
  + exact F25.
  + exact F26.
  + exact F27.
  + rewrite HDECL. exact Hdpos.
  + unfold s22_L in HSL'. rewrite HDECL. exact HSL'.
  + exact HCM'.
  + rewrite HDECL. exact HTABS'.

- (* blt not taken: i + 1 = m->n, past the loop at 0x85bd0 *)
  rewrite !EBD, EB25, UB32, Z.add_0_r in Hc.
  rewrite (p6_blt (Z.of_nat i + 1) nval ltac:(lia) ltac:(lia)) in Hc.
  assert (HSeq : (Datatypes.S i = length (SegModel.mc_seg (x_mcF cx)))%nat).
  { apply Z.ltb_ge in Hc.
    assert (Hq1 : Z.of_nat (length (SegModel.mc_seg (x_mcF cx))) <= Z.of_nat i + 1) by exact Hc.
    assert (Hq2 : Z.of_nat i < Z.of_nat (length (SegModel.mc_seg (x_mcF cx)))) by exact Hilt.
    apply Nat2Z.inj. rewrite Nat2Z.inj_succ. clear - Hq1 Hq2. lia. }
  assert (HMD : SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx) = x_decl cx i).
  { rewrite <- (s22_decl_all (x_mcF cx) (x_tab0 cx) (x_cap cx) (Datatypes.S i) HSeq).
    exact HDECL. }
  assert (Hdb : fst (x_decl cx i) <= 32).
  { unfold x_decl.
    pose proof (s22_decl_bound (firstn i (SegModel.mc_seg (x_mcF cx))) (x_tab0 cx) (x_cap cx) 0
      ltac:(lia) ltac:(unfold x_decl in Hdpos; exact Hdpos)) as Hq.
    rewrite length_firstn in Hq. unfold x_mcF in *. lia. }
  assert (Hmodid : fst (x_decl cx i) mod 2 ^ 64 = fst (x_decl cx i)) by (apply Z.mod_small; lia).
  paj_run_to_tok RUNTO HS HJB SHOK p6_span LO_K85bd0.
  { awr_ok_tac. }
  rename HF into HFC, HFr into HFrC, HG into HGC, ms into msK, HJB into HJK.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (mdK := mm) in *; clearbody mdK end.
  cbn [ms_mem mkst] in HFrC.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msK) a = rdW W (ms_mem msB) a).
  { intros a Ha.
    lazymatch type of HFrC with frame_of _ ?rsx _ _ =>
      apply (kept_of_frame (segs := SEGS) EB rsx (w_H W) (ms_mem msB) (ms_mem msK)
        (fun _ : Z => False) HFrC); [| exact Ha | intros []] end.
    intros b wlo whi a' Hin Hr. vm_compute in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; exfalso; lia|]).
    destruct Hin. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem msK) a = rdW W mem a)
    by (intros a Ha Hna; rewrite (KC a Ha), (KB a Ha); exact (KA a Ha Hna)).
  assert (KW : forall a v, (forall j, 0 <= j < 8 -> ~ (x_sh cx + 4 <= a + j < x_sh cx + 7)) ->
    0 <= a -> a + 8 <= 2 ^ 64 -> rdword (rdW W mem) a = Some v ->
    rdword (rdW W (ms_mem msK)) a = Some v).
  { intros a v Hw Ha Ha8 H.
    rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem msK)) a
      ltac:(intros j Hj; apply KALL; [lia | apply Hw; lia])). exact H. }
  pose proof (proj1 HJK) as HARK.
  assert (F2 : getr (ms_regs msK) 2 = w64 (x_s1 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 2%bv 2%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 2%nat 2%bv eq_refl), A2. exact G2. }
  assert (F3 : getr (ms_regs msK) 3 = getr (x_regs cx) 3).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 3%bv 3%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 3%nat 3%bv eq_refl), A3. exact G3. }
  assert (F4 : getr (ms_regs msK) 4 = getr (x_regs cx) 4).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 4%bv 4%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 4%nat 4%bv eq_refl), A4. exact G4. }
  assert (F8 : getr (ms_regs msK) 8 = w64 (x_sp0 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 8%bv 8%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 8%nat 8%bv eq_refl), A8. exact G8. }
  assert (F9 : getr (ms_regs msK) 9 = w64 (x_s1 cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 9%bv 9%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 9%nat 9%bv eq_refl), A9. exact G9. }
  assert (F16 : getr (ms_regs msK) 16 = w64 m).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 16%bv 16%nat HS ltac:(vm_compute; reflexivity)). exact EB16. }
  assert (F21 : getr (ms_regs msK) 21 = w64 (x_sh cx)).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 21%bv 21%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 21%nat 21%bv eq_refl), A21. exact R21. }
  assert (F24 : getr (ms_regs msK) 24 = w64 tab).
  { rewrite (s10_reg_atom (w_H W) EB _ msK 24%bv 24%nat HS ltac:(vm_compute; reflexivity)).
    unfold EB. rewrite (p6_EB_lo (ms_regs msA) nval 24%nat 24%bv eq_refl), A24. exact R24. }
  assert (HSAVED' : lt_saved cx (rdW W (ms_mem msK))).
  { intros j r Hj.
    assert (Hj13 : (j < 13)%nat)
      by (pose proof (proj1 (nth_error_Some LT_SAVED j) ltac:(rewrite Hj; discriminate)) as Hq;
          cbn [LT_SAVED length] in Hq; lia).
    apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia |]. exact (HSAVED j r Hj). }
  assert (HIMG' : lt_img B cx (rdW W (ms_mem msK))).
  { apply (s10_lt_img_kept B IMGS BSYM cx W (ms_mem msK) (rdW W mem) HARK); [|exact HIMG].
    intros a Ha _ _. apply KALL; [pose proof (pa_img_range a Ha); unfold kImgEnd in *; lia | exact (OUTI a Ha)]. }
  assert (HSL' : lt_slots cx (rdW W (ms_mem msK)) (s22_L cx i c m mt)).
  { intros o v Hin.
    assert (Ho : 0 <= o /\ o <= 184).
    { unfold s22_L in Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; unfold LT_LV in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq; intros; subst; lia |]); destruct Hin. }
    apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia |]. exact (HSL o v Hin). }
  assert (HCM' : lt_cm (rdW W (ms_mem msK)) c m (x_run cx)).
  { destruct HCM as [(bsc & HBc1 & HEc) (bsm & HBm1 & HEm)]. split.
    - exists bsc. split; [|exact HEc].
      apply (p6_sa_bytes_kept (rdW W mem) _ c bsc HBc1). intros j Hj.
      pose proof (proj1 HEc) as Hlc.
      apply KALL; [unfold seg_spec.SEG_C_SIZE in *; lia|].
      apply (OUTB c seg_spec.SEG_C_SIZE); [exact HIc | unfold seg_spec.SEG_C_SIZE in *; lia].
    - exists bsm. split; [|exact HEm].
      apply (p6_sa_bytes_kept (rdW W mem) _ m bsm HBm1). intros j Hj.
      pose proof (proj1 HEm) as Hlm.
      apply KALL; [unfold seg_spec.SEG_M_SIZE in *; lia|].
      apply (OUTB m seg_spec.SEG_M_SIZE); [exact HIm | unfold seg_spec.SEG_M_SIZE in *; lia]. }
  assert (HTABS' : lt_tabs cx (rdW W (ms_mem msK)) tab mt (snd (x_decl cx i))).
  { split; [exact Htcap|]. split; [|split; [|split; [|split]]].
    - destruct Htab0 as (bst & HBt1 & HEt). exists bst. split; [|exact HEt].
      apply (p6_sa_bytes_kept (rdW W mem) _ tab bst HBt1). intros j Hj.
      pose proof (proj1 HEt) as Hlt.
      apply KALL; [lia|]. apply (OUTB tab (x_tabn cx)); [exact HItab | lia].
    - unfold sa_guardtab in Hguard |- *.
      apply (p6_sa_bytes_kept (rdW W mem) _ _ _ Hguard). intros j Hj.
      change (length seg_spec.GUARD_BYTES) with 18%nat in Hj.
      apply KALL; [unfold seg_spec.RVLAN_SIZE in *; lia|].
      apply (OUTB tab (x_tabn cx)); [exact HItab | unfold seg_spec.RVLAN_SIZE in *; lia].
    - apply (p6_sa_val_kept (rdW W mem) _ _ _ _ Hfn). intros j Hj.
      apply KALL; [unfold FO_N in *; lia|]. apply OUTF. unfold FO_N. lia.
    - destruct Hmtab as (bsm & HBm1 & HEm). exists bsm. split; [|exact HEm].
      apply (p6_sa_bytes_kept (rdW W mem) _ mt bsm HBm1). intros j Hj.
      pose proof (proj1 HEm) as Hlm.
      apply KALL; [lia|]. apply (OUTB mt (x_mtn cx)); [exact HImt | lia].
    - exact Hmtlen. }
  assert (HZSK : sa_zs (rdW W (ms_mem msK)) (x_sh cx) (lt_fsh LFO_N)).
  { intros j Hj. rewrite lt_fsh_len in Hj.
    destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
    - rewrite (p6_fsh_same j ltac:(left; lia)). rewrite KALL by lia. exact (HZS j ltac:(rewrite lt_fsh_len; lia)).
    - destruct (Nat.lt_ge_cases j 7) as [Hj7 | Hj7].
      + rewrite (p6_fsh_f8 j ltac:(lia)).
        rewrite KC by lia. rewrite KB by lia.
        replace (x_sh cx + Z.of_nat j) with (x_sh cx + 4 + Z.of_nat (j - 4)) by lia.
        rewrite (HZS3 (j - 4)%nat ltac:(cbn [length]; lia)).
        f_equal. destruct j as [|[|[|[|[|[|[|j]]]]]]]; cbn [Nat.sub nth]; try reflexivity; lia.
      + rewrite (p6_fsh_same j ltac:(right; lia)). rewrite KALL by lia.
        exact (HZS j ltac:(rewrite lt_fsh_len; lia)). }
  assert (HCORE' : lt_core B MT cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]).
  { split; [|split; [exact HIMG' | split; [exact HBL | exact HBUD]]].
    unfold lt_frame.
    split; [exact HJK|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
    split; [exact F8|]. split; [exact F9|]. split; [exact HSAVED'|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD0]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD8]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; lia | lia | lia | exact HD16]|].
    split; [apply KW; [intros j0 Hj0; apply OUTF; unfold LT_FLAGW; lia | unfold LT_FLAGW; lia
                      | unfold LT_FLAGW; lia | exact HDFL]|].
    split; [apply KW; [intros j0 Hj0; apply OUTS; lia | lia | lia | exact HDSB]|].
    exact HZSK. }
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K85bd0) (ms_regs msK) (ms_mem msK) mdK) (lt_post B MT cx)).
  apply (HBD0 fx cx ly S W (ms_regs msK) (ms_mem msK) mdK k acc c m tab mt HBASE HFRM HCORE').
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK c seg_spec.SEG_C_SIZE HARK HIc Hc16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK m seg_spec.SEG_M_SIZE HARK HIm Hm16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK tab (x_tabn cx) HARK HItab Htab16).
  + exact (p6_hblk_at ly S W (ms_mem msK) mdK mt (x_mtn cx) HARK HImt Hmt16).
  + exact F16.
  + exact F21.
  + exact F24.
  + rewrite HMD, Hmodid. intros o v Hin. apply HSL'. unfold s22_L, LT_LV.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [ rewrite <- Hq; apply in_or_app; first [left; cbn [In]; tauto | right; cbn [In]; tauto] |]).
    destruct Hin.
  + exact HCM'.
  + rewrite HMD. exact HTABS'.
Qed.

End e.
End f.
End d.
Check s22_p6.
Print Assumptions s22_p6.
