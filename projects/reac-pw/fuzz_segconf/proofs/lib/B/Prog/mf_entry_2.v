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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 512 of its 559 lines of code are new or changed and 406 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the second half of the
   segment S_MF_ENTRY, from the cut MFE_RET_SNP 0x862ac (the snprintf return, lib/B/Prog/mf_entry_d.v) to HEAD
   0x86378 (the text is not empty) or EXIT 0x86da0 (it is), = MFE_MID_F. A walk lane and a sub-lane of the image-B m_file-family owner's
   G2B. 65 instructions: 0x862ac-0x86374 (51) and the three slow paths 0x86e88-0x86ebc (14).

   WHAT THE CODE DOES (B.s; listing line = (pc - 0x86140) / 4 + 2), in order:
     0x862ac  `ld s6,128(s1)`   the reload of c + 0x2000, which the snprintf call clobbered
     0x862b0  `addi a0,s6,944`  &c->gen = c + 0x23b0;  0x862b4-0x862b8 its shadow address (a0 >> 3) + s2,
     0x862bc  `sd a1,104(s1)`   kept in 104(s1)
     0x862c0  `lb a2,0(a1)` / 0x862c4 `bnez a2` : the instrumented check of the 4-byte load (a load of the shadow
              byte at (a >> 3) + the shadow base and a compare). Its slow path 0x86e88-0x86e90 and the error path
              0x86e94 (a call of errpath_load4) are not reached: the token run turns the check into the obligation
              `c->gen is addressable', which mf_core's sa_addr of the block gives (m_file_sd.v mf_she_blk).
     0x862c8  `sd a0,56(s1)`, 0x862cc `lw a1,0(a0)` : gen
     0x862d0  `addiw a0,a1,1` / 0x862d4 `blt a0,a1 -> 0x86e84 unimp` : the UBSan trap of `c->gen++` (the signed
              overflow of gen + 1). NOT TAKEN: the executor decides it from the seeded fact
              `0 <= gen <= 2 ^ 31 - 2`, which m_file_pre's `mc_gen mc + 1 < 2 ^ 31` and sa_mconf's
              `0 <= mc_gen mc` (mf_entry_m.v mf_mconf_gen) give. The trap instruction 0x86e84 is never executed.
     0x862d8-0x862e0  the check of the 4-byte store (slow path 0x86e98-0x86ea8, error path errpath_store4 0x86eac,
              not reached: the same obligation), 0x862e4 `sw a0,944(s6)` : c->gen = gen + 1
     0x862e8-0x862f4  the check of the 1-byte load of *text (slow path 0x86eb0-0x86eb8, error path errpath_load1
              0x86ebc, not reached: mf_loop's sa_addr of the text), 0x862f8 `lbu a0,0(s10)`
     0x862fc  `beqz a0,0x86da0` : the empty text goes to EXIT; otherwise
     0x86300-0x86374  the set-up (the image-B m_file cut map table C.1): s5 = 0, 136(s1) = 0, 144(s1) = FB + 32, 48(s1) =
              c + 0x23ac, 16(s1) = ~c, 24(s1) = c + 0x2004, s4 = 511, 80(s1) = m_key.words and 72(s1) its shadow,
              s3 = 0x100002200, 32(s1) = c + 0x238c, 40(s1) = ~(c + 0x238c), 96(s1) = s7, 88(s1) = s8,
              112(s1) = s9; the fall-through to HEAD 0x86378.

   THE FORM (the walk-form survey 2.1-2.3, 2.9; the closest released shape is lib/A/Prog/m_file_s_exit.v of
   commit fdafeb0f1e0f and lib/B/Prog/mf_tail.v of a working branch): the state at
   0x862ac is m_file_sd.v's mf_seed with cells = false (the cells are what this half writes), hnp = false, the two
   cells 64(s1) and 128(s1) the first half left as the caller's chunks slx, and the gen and the text's first byte as
   the extra values xs (atoms 52, 53). The mconf block's gen field and the text's byte are added as regions
   (st_ok_pi_add_region), the two checked ranges as shadow entries (mf_she_blk / mf_she_at), and the walk is one
   token run per arm. The branch 0x862fc is decided by the executor: with the text empty its byte is the literal 0
   (taken), otherwise the byte's atom is in [1, 255], which is range-disjoint from 0 (not taken). The cut facts at
   the stop are rebuilt with lib/B/Prog/m_file_k.v's keep lemmas and the cells are read back from the run's own
   final region. The block's model goes from mfe_c0 v to mfe_c1 v by lib/B/Prog/mf_entry_m.v's mfe_bump_gen. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k mf_entry_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require mf_entry_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the state's form, computed *)
Ltac mfe_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* ===================== the expressions the set-up leaves in the frame cells ===================== *)
(* `not rd,rs` is `xori rd,rs,-1`: the complement of atom n + k *)
Lemma mfe_lxor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (HL : Z.land x (2 ^ 64 - 1) = x).
{ replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx. }
pose proof (Z.add_lxor_2land x (2 ^ 64 - 1)) as H. rewrite HL in H. lia.
Qed.
Lemma mfe_d_off : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof.
intros E n x k Hn Hx Hxk. rewrite denot_lit_U. f_equal.
rewrite U_SOff, Hn, (unsigned_lit_small x) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma mfe_d_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z Hz. rewrite denot_lit_U. f_equal. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.
Lemma mfe_d_xor : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n k) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - (x + k)).
Proof.
intros E n x k Hn Hx Hxk. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SLit, U_SOff, Hn. rewrite (unsigned_lit_small x) by lia.
rewrite (zcanon_id (x + k)) by (unfold M64; lia).
replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
cbn [zalu_raw]. rewrite mfe_lxor_m1 by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the shadow address with the two operands of the add the other way round (0x86350-0x86358, 72(s1)) *)
Lemma mfe_d_sh2 : forall E (n : nat) x, ew E n = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= x < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) = Z_to_bv 64 (SHADOW_OFF + x / 8).
Proof.
intros E n x Hn H32 Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_srl3, !U_SOff, Hn, H32.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite !Z.add_0_r. rewrite (zcanon_id x) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
cbn [zalu_raw].
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
rewrite zcanon_id; [lia|]. unfold M64, SHADOW_OFF. lia.
Qed.

(* the caller's chunks the first half left in the frame cells: 64(s1) = &c->reading, 128(s1) = c + 0x2000 *)
Definition mfe_slx : list YP09.chunk :=
  [YP09.mkChunk 64 (CVal 8 (SOff 33 seg_spec.MC_READING)); YP09.mkChunk 128 (CVal 8 (SOff 33 seg_spec.MC_N))].
(* the four bytes of c->gen, at the mconf block's atom: what 0x862cc reads and 0x862e4 writes *)
Definition mfe_r_gen : YP09.region :=
  YP09.mkRegion (Some 33%nat) seg_spec.MC_GEN (seg_spec.MC_GEN + 4) seg_spec.MC_GEN (seg_spec.MC_GEN + 4)
    [YP09.mkChunk seg_spec.MC_GEN (CVal 4 (SOff 52 0))].
(* the text's first byte, read-only, at the cursor's atom 26 (s10) *)
Definition mfe_txt_cs : list YP09.chunk := [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
(* the two checked ranges: the mconf block (0x862c0, 0x862dc) and the text (0x862f0) *)
Definition mfe_SH : list shent := [mkSHE 33 0 seg_spec.SEG_M_SIZE; mkSHE 26 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* SegABase's sa_val and the chunk library's val_mem, over an ASan reader *)
Lemma mfe_val_of_sa : forall (H : word -> bool) (m : word -> option byte) a n x,
  sa_val (aview SEGS H m) a n x -> val_mem SEGS (mrestrict H m) a n x.
Proof.
intros H m a n x Hv k Hk. pose proof (Hv k Hk) as Hb.
destruct (aview_byte SEGS H m (a + Z.of_nat k) _ Hb) as (b & Hm & Hbv & Hr).
rewrite Hm. f_equal. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- Hbv. exact (Z.mod_small _ _ Hr).
Qed.
Lemma mfe_sa_of_val : forall (H : word -> bool) (m : word -> option byte) a n x,
  val_mem SEGS (mrestrict H m) a n x -> sa_val (aview SEGS H m) a n x.
Proof.
intros H m a n x Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
exact (Z.mod_small _ 256 (Z.mod_pos_bound (Z.shiftr (x mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) 256 ltac:(lia))).
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis HEAD : forall n, MF_HEAD_F B n.
Hypothesis EXIT : MF_EXIT_F B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* S_MF_ENTRY's second half at one FP state *)
Lemma mfe_mid_at : MFE_MID_stmt B.
Proof.
unfold MFE_MID_stmt. intros v lyc Sc Wc regs1 memc mdc pos CX FRM MID.
destruct MID as (LS & CORE & LOOP & SL64 & SL128 & RX & R25 & R26).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & Ht64 & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & _ & _ & _ & Hgen1 & _ & _ & _ & _ & Hslen & _ & (Ht0 & _) & _ & Hdisj & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HTL).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mfe_c0 v) CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mbc 1 pos HAR Hbc Hin) as Hsepc.
change (fs_frame_bytes 1) with 128 in Hsepc. unfold zdisjoint in Hsepc. cbn [fst snd] in Hsepc.
unfold seg_spec.SEG_M_SIZE in Hbc2.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mfe_c0 v) (mfe_c0 v) None 0 (mv_t v) (mv_s v) CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
destruct (mf_s1_facts B v CX) as (Hs1a & Hs1m & _).
pose proof RX as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24).
pose proof (mf_regs_base_of_ex B v lyc pos regs1 RX) as RB.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
destruct (mf_entry_m.mf_mconf_gen _ _ _ HMC) as (HGV & HGR).
change (mc_gen (mfe_c0 v)) with (mc_gen (mv_mc v)) in HGV, HGR.
destruct (mf_loop_hd v Wc memc (mfe_c0 v) None 0 (mv_t v) (mv_s v) LOOP) as (Hhd & Hhd0).
destruct (aview_byte SEGS (w_H Wc) memc (mv_t v) (hd0 (mv_s v)) Hhd) as (bh & _ & _ & Hh256).
pose proof LOOP as (_ & _ & _ & _ & LADDR & _).
set (G := mc_gen (mv_mc v)) in *. set (h := hd0 (mv_s v)) in *.
(* ============================ the seed at 0x862ac ============================ *)
set (E := mfE regs1 v lyc pos None 0 [G; h]).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None 0 [G; h]) (Z_to_bv 64 0))
  by (intros; apply mfE_extra; assumption).
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36.
assert (E52 : ew E 52 = Z_to_bv 64 G) by exact (mfE_xs regs1 v lyc pos None 0 [G; h] 0 ltac:(unfold A_TEXT; lia)).
assert (E53 : ew E 53 = Z_to_bv 64 h) by exact (mfE_xs regs1 v lyc pos None 0 [G; h] 1 ltac:(unfold A_TEXT; lia)).
assert (E26 : ew E 26 = Z_to_bv 64 (mv_t v)) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstB.wordsA).
{ unfold E. rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia).
  rewrite (mf_words_obj VOBJS). reflexivity. }
assert (HWv : SegInstB.wordsA = 0xa2040) by (vm_compute; reflexivity).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) None < 2 ^ 64) by (cbn [mf_cur_ptr]; lia).
assert (FSLX : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) mfe_slx).
{ unfold mfe_slx. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (mf_chunk_atom E _ (mf_s1 (mv_sp v)) 64 33 seg_spec.MC_READING (mv_c v) E33);
      [lia | unfold seg_spec.MC_READING; lia | exact SL64].
  - apply (mf_chunk_atom E _ (mf_s1 (mv_sp v)) 128 33 seg_spec.MC_N (mv_c v) E33);
      [lia | unfold seg_spec.MC_N; lia | exact SL128]. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mfe_c0 v) None 0 [G; h] MFE_RET_SNP
  false false mfe_slx false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) Hcur
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_OFF; lia) FSLX (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
(* the text's one-byte region: its chunk differs per arm, the rest does not *)
assert (TXT : forall (cs : list YP09.chunk),
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (mv_t v)) cs ->
  region_ok SEGS E (mrestrict (w_H Wc) memc) (YP09.mkRegion (Some 26%nat) 0 1 0 0 cs) /\
  all_disjoint E (YP09.mkRegion (Some 26%nat) 0 1 0 0 cs)
    (mf_regions false false mfe_slx false false [] false MF_LOW_OFF) /\
  afact_ok E 26 (mkAF 4096 (2 ^ 47 - 8) 0)).
{ intros cs HCS.
  exact (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mfe_c0 v) None 0 [G; h] 26 (mv_t v) 1 cs
    0 (mv_t v) (mv_s v) false false mfe_slx false false [] false CX CORE RB LOOP E26 ltac:(lia) ltac:(lia)
    ltac:(lia) HCS). }
destruct (TXT mfe_txt_cs) as (_ & _ & TF).
{ unfold mfe_txt_cs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_t v) 0 1 (SOff 53 0) h);
    [cbn [sv_denot]; rewrite E53, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc (mv_t v) h Hhd). }
(* the registers the cut names, as the seed's atoms: s7 = FB, s8 = shadow(FB), s9 = c *)
apply (ast_ok_pi_set_reg_fp E _ _ (23%bv : bv 5) (SOff 34 0)) in HS0;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E34; cbn [ms_regs restrict mkst];
     rewrite R23; reflexivity].
apply (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff 36 0)) in HS0;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36; cbn [ms_regs restrict mkst];
     rewrite R24; reflexivity].
apply (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SOff 33 0)) in HS0;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E33; cbn [ms_regs restrict mkst];
     rewrite R25; reflexivity].
(* THE UBSAN TRAP 0x862d4: gen is in [0, 2 ^ 31 - 2], so gen + 1 does not overflow and the branch is not taken *)
apply (st_ok_pi_add_fact E _ _ 52 (mkAF 0 (2 ^ 31 - 2) 0)) in HS0;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E52, unsigned_lit_small by lia; change (2 ^ 0) with 1;
     rewrite Z.mod_1_r; lia].
apply (st_ok_pi_add_fact E _ _ 26 (mkAF 4096 (2 ^ 47 - 8) 0)) in HS0; [| exact TF].
mfe_norm HS0.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (U26 : bv_unsigned (ew E 26) = mv_t v) by (rewrite E26; apply unsigned_lit_small; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by exact U2.
assert (B8 : base_val E (Some 8%nat) = mv_sp v) by exact U8.
assert (B33 : base_val E (Some 33%nat) = mv_c v) by exact U33.
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by exact U34.
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8) by exact U36.
assert (B26 : base_val E (Some 26%nat) = mv_t v) by exact U26.
assert (Hspan : Z.of_nat (length (mv_s v)) + 1 <= seg_spec.cstr_span (mv_t v) (mv_s v)).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (mv_t v + Z.of_nat (length (mv_s v)) + 1)) 8 ltac:(lia)). lia. }
unfold sa_disj in Hdisj.
(* the four bytes of c->gen *)
assert (GOK : region_ok SEGS E (mrestrict (w_H Wc) memc) mfe_r_gen).
{ unfold region_ok, mfe_r_gen. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 9136 4 (SOff 52 0) G);
      [cbn [sv_denot]; rewrite E52, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply mfe_val_of_sa. exact HGV. }
assert (GDIS : forall cs, all_disjoint E mfe_r_gen (YP09.mkRegion (Some 26%nat) 0 1 0 0 cs ::
  mf_regions false false mfe_slx false false [] false MF_LOW_OFF)).
{ intros cs. apply all_disjoint_of_extents. unfold mfe_r_gen, mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low,
    mf_r_ft, mf_r_fs, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B26, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, mf_s1 in *.
  rewrite HSB in *.
  repeat split; lia. }
(* THE THREE INSTRUMENTED CHECKS 0x862c0 / 0x862dc / 0x862f0: the shadow entries of the two ranges *)
assert (SHOK : sh_ok SEGS (SOff 32 0) mfe_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, mfe_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mfe_c0 v) None 0 [G; h] seg_spec.SEG_M_SIZE CX CORE
      ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
  - apply (mf_she_at E Wc memc 26 (mv_t v) 1 (mfE_U32 regs1 v lyc pos None 0 [G; h]) E26 ltac:(lia) ltac:(lia)).
    + destruct (mf_addr_sub _ (mv_t v) (Z.of_nat (length (mv_s v)) + 1) (mv_t v) 1 LADDR ltac:(lia) ltac:(lia)
        ltac:(lia)) as (_ & _ & _ & HRA & _). exact HRA.
    + intros x Hx. apply (mf_txt_app B v Wc memc (mfe_c0 v) None 0 (mv_t v) (mv_s v) CX LOOP). lia. }
(* the bytes the run writes: c->gen and the frame cells *)
pose (RW := fun a => (mv_c v + 9136 <= a < mv_c v + 9140) \/
  (mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216)).
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a [Ha | Ha]; unfold mf_rw; [right; left; unfold seg_spec.SEG_M_SIZE; lia
  | right; right; right; right; right; lia]. }
unfold mf_at.
destruct (Z.eq_dec h 0) as [Hh0 | Hh0].
- (* ===================== the empty text: 0x862fc is taken, EXIT ===================== *)
  assert (Hhd' : rdW Wc memc (mv_t v) = Some 0) by (rewrite Hhd, Hh0; reflexivity).
  destruct (TXT [YP09.mkChunk 0 (CVal 1 (SLit 0))]) as (TOK0 & TDIS0 & _).
  { apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_t v) 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc (mv_t v) 0 Hhd'). }
  pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
    HS0 eq_refl TOK0 TDIS0) as HS1.
  pose proof (st_ok_pi_add_region E _ _ mfe_r_gen HS1 eq_refl GOK (GDIS _)) as HS2.
  clear HS1. mfe_norm HS2.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_EXIT.
  { (* every byte the run writes is the function's: c->gen is in its footprint and in the block, the frame cells
       are in its own stack window *)
    lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
      let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
      - exists (mv_c v + seg_spec.MC_NKEPT, mv_c v + seg_spec.MC_READING + 96).
        split; [cbn [In]; repeat (first [left; reflexivity | right])|].
        cbn [fst snd]. unfold seg_spec.MC_NKEPT, seg_spec.MC_READING. lia.
      - exists bc, mbc. split; [exact Hbc | lia]. }
    do 2 (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v))); [reflexivity | exact U2 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. rewrite HSTK. unfold mf_s1 in *. lia. }
    do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  (* the bytes outside RW are the ones the cut facts read *)
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha Hn; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha Hn);
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr;
         rewrite ?U33, ?U2, ?U8, ?U26, ?U34, ?U36 in Hr; unfold RW; lia |]);
      destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  (* low.i's 8 shadow bytes and 120(s1) at the new memory *)
  assert (VSH' : forall i, 4 <= i < 12 ->
    val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
  { intros i Hi. apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
      [rewrite HSB; lia | change (Z.of_nat 1) with 1; rewrite HSB; lia | | exact (VSH i Hi)].
    intros k Hk [Hbad | Hbad]; change (Z.of_nat 1) with 1 in Hk;
      unfold in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, mf_s1 in *; rewrite HSB in *; lia. }
  lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = mf_s1 (mv_sp v)) by (rewrite ?ew_ewset_other by lia; exact U2);
    assert (X33u : bv_unsigned (ew Ex 33) = mv_c v) by (rewrite ?ew_ewset_other by lia; exact U33);
    assert (X32 : ew Ex 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (X33 : ew Ex 33 = Z_to_bv 64 (mv_c v)) by (rewrite ?ew_ewset_other by lia; exact E33);
    assert (X34 : ew Ex 34 = Z_to_bv 64 (frame_addr lyc 1 pos)) by (rewrite ?ew_ewset_other by lia; exact E34);
    assert (X36 : ew Ex 36 = Z_to_bv 64 (SHADOW_OFF + frame_addr lyc 1 pos / 8))
      by (rewrite ?ew_ewset_other by lia; exact E36);
    assert (X52 : ew Ex 52 = Z_to_bv 64 G) by (rewrite ?ew_ewset_other by lia; exact E52);
    assert (XW : ew Ex (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstB.wordsA)
      by (rewrite ?ew_ewset_other by (unfold A_OBJ, MF_WORDS_OBJ; lia); exact EW)
  end.
  pose proof (st_ok_region_nth _ _ _ 3 _ HS2 eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
  assert (V120' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos)).
  { pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 120 8%N (SOff 34 0) (frame_addr lyc 1 pos) HRS X2
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite (mfe_d_off _ 34 (frame_addr lyc 1 pos) 0 X34 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV.
    change (N.to_nat 8) with 8%nat in VV. exact VV. }
  (* the block holds mfe_c1: only c->gen changed, and it holds gen + 1 *)
  pose proof (st_ok_region_nth _ _ _ 0 _ HS2 eq_refl) as HRG. cbn [restrict ms_mem] in HRG.
  assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) (mfe_c1 v)).
  { refine (mf_entry_m.mfe_bump_gen (rdW Wc memc) (rdW Wc (ms_mem ms)) (mv_c v) (mfe_c0 v) (G + 1) HMC _ _ _).
    - intros a Ha Hg. apply K; [unfold seg_spec.SEG_M_SIZE in *; lia|].
      unfold RW, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, mf_s1 in *. lia.
    - apply mfe_sa_of_val.
      pose proof (field_of_region _ _ 33%nat _ _ seg_spec.MC_GEN (seg_spec.MC_GEN + 4) seg_spec.MC_GEN
        (seg_spec.MC_GEN + 4) seg_spec.MC_GEN 4%N (SOff 52 1) (G + 1) HRG X33u
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (mfe_d_off _ 52 G 1 X52 ltac:(lia) ltac:(lia)); reflexivity)
        ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as VV.
      change (N.to_nat 4) with 4%nat in VV. exact VV.
    - lia. }
  destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mfe_c0 v) (ms_mem ms) mdw RW MF_LOW_OFF (mfe_c1 v)
    CX CORE HJ K RWok VSH' V120' MC') as (CORE' & _).
  rewrite <- (mf_file_nil v (proj2 Hhd0 Hh0)) in CORE'.
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  assert (RX' : mf_regs_ex B v lyc pos (ms_regs ms)).
  { apply (mf_regs_ex_of B v lyc pos regs1 (ms_regs ms) RX).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q23, E34, R23. reflexivity.
    - rewrite Q24, E36, R24. reflexivity. }
  pmkst HS2.
  exact (EXIT fx v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos CX LS CORE' RX').
- (* ===================== the nonempty text: 0x862fc is not taken, the set-up, HEAD ===================== *)
  destruct (TXT mfe_txt_cs) as (TOK1 & TDIS1 & _).
  { unfold mfe_txt_cs. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_t v) 0 1 (SOff 53 0) h);
      [cbn [sv_denot]; rewrite E53, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc (mv_t v) h Hhd). }
  pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 26%nat) 0 1 0 0 mfe_txt_cs) HS0 eq_refl TOK1 TDIS1) as HS1.
  pose proof (st_ok_pi_add_region E _ _ mfe_r_gen HS1 eq_refl GOK (GDIS _)) as HS2.
  clear HS1.
  apply (st_ok_pi_add_fact E _ _ 53 (mkAF 1 255 0)) in HS2;
    [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E53, unsigned_lit_small by lia; change (2 ^ 0) with 1;
       rewrite Z.mod_1_r; lia].
  mfe_norm HS2.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_HEAD.
  { lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
      let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
      - exists (mv_c v + seg_spec.MC_NKEPT, mv_c v + seg_spec.MC_READING + 96).
        split; [cbn [In]; repeat (first [left; reflexivity | right])|].
        cbn [fst snd]. unfold seg_spec.MC_NKEPT, seg_spec.MC_READING. lia.
      - exists bc, mbc. split; [exact Hbc | lia]. }
    do 2 (apply awr_ok_cons_ro; [cbn; lia|]).
    eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v))); [reflexivity | exact U2 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. rewrite HSTK. unfold mf_s1 in *. lia. }
    do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha Hn; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha Hn);
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr;
         rewrite ?U33, ?U2, ?U8, ?U26, ?U34, ?U36 in Hr; unfold RW; lia |]);
      destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  assert (VSH' : forall i, 4 <= i < 12 ->
    val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
  { intros i Hi. apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
      [rewrite HSB; lia | change (Z.of_nat 1) with 1; rewrite HSB; lia | | exact (VSH i Hi)].
    intros k Hk [Hbad | Hbad]; change (Z.of_nat 1) with 1 in Hk;
      unfold in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, mf_s1 in *; rewrite HSB in *; lia. }
  lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ =>
    assert (X2 : bv_unsigned (ew Ex 2) = mf_s1 (mv_sp v)) by (rewrite ?ew_ewset_other by lia; exact U2);
    assert (X33u : bv_unsigned (ew Ex 33) = mv_c v) by (rewrite ?ew_ewset_other by lia; exact U33);
    assert (X32 : ew Ex 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (X33 : ew Ex 33 = Z_to_bv 64 (mv_c v)) by (rewrite ?ew_ewset_other by lia; exact E33);
    assert (X34 : ew Ex 34 = Z_to_bv 64 (frame_addr lyc 1 pos)) by (rewrite ?ew_ewset_other by lia; exact E34);
    assert (X36 : ew Ex 36 = Z_to_bv 64 (SHADOW_OFF + frame_addr lyc 1 pos / 8))
      by (rewrite ?ew_ewset_other by lia; exact E36);
    assert (X52 : ew Ex 52 = Z_to_bv 64 G) by (rewrite ?ew_ewset_other by lia; exact E52);
    assert (XW : ew Ex (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstB.wordsA)
      by (rewrite ?ew_ewset_other by (unfold A_OBJ, MF_WORDS_OBJ; lia); exact EW)
  end.
  pose proof (st_ok_region_nth _ _ _ 3 _ HS2 eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
  pose proof (st_ok_region_nth _ _ _ 0 _ HS2 eq_refl) as HRG. cbn [restrict ms_mem] in HRG.
  (* the sixteen frame cells, read back from the run's own region *)
  assert (CELLS' : mf_cells v lyc pos (ms_mem ms) Wc None).
  { unfold mf_cells, mf_cur_ptr.
    repeat split;
    lazymatch goal with
    | |- val_mem _ _ (_ + ?off) 8 _ =>
      let VV := fresh "VV" in
      lazymatch off with
      | 16 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 16 8%N
          (SAlu ALU_XOR (SOff 33 0) (SLit (-1))) (2 ^ 64 - 1 - mv_c v) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(rewrite (mfe_d_xor _ 33 (mv_c v) 0 X33 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity)
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV
      | 24 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 24 8%N (SOff 33 8196)
          (mv_c v + seg_spec.MC_OVERFLOW) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 8196 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_OVERFLOW; lia) ltac:(cbn; lia)) as VV
      | 32 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 32 8%N (SOff 33 9100)
          (mv_c v + seg_spec.MC_KNOCK) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 9100 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_KNOCK; lia) ltac:(cbn; lia)) as VV
      | 40 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 40 8%N
          (SAlu ALU_XOR (SOff 33 9100) (SLit (-1))) (2 ^ 64 - 1 - (mv_c v + seg_spec.MC_KNOCK)) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_xor _ 33 (mv_c v) 9100 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_KNOCK; lia) ltac:(cbn; lia)) as VV
      | 48 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 48 8%N (SOff 33 9132)
          (mv_c v + seg_spec.MC_NKEPT) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 9132 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_NKEPT; lia) ltac:(cbn; lia)) as VV
      | 56 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 56 8%N (SOff 33 9136)
          (mv_c v + seg_spec.MC_GEN) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 9136 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_GEN; lia) ltac:(cbn; lia)) as VV
      | 64 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 64 8%N (SOff 33 9140)
          (mv_c v + seg_spec.MC_READING) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 9140 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_READING; lia) ltac:(cbn; lia)) as VV
      | 72 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 72 8%N
          (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff (A_OBJ MF_WORDS_OBJ) 0) (SLit 3)))
          (SHADOW_OFF + SegInstB.wordsA / 8) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_sh2 _ (A_OBJ MF_WORDS_OBJ) SegInstB.wordsA XW X32 ltac:(rewrite HWv; lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite HSB, HWv; vm_compute; split; [discriminate | reflexivity])
          ltac:(cbn; lia)) as VV
      | 80 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 80 8%N (SOff (A_OBJ MF_WORDS_OBJ) 0)
          SegInstB.wordsA HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(rewrite (mfe_d_off _ (A_OBJ MF_WORDS_OBJ) SegInstB.wordsA 0 XW ltac:(rewrite HWv; lia)
                  ltac:(rewrite HWv; lia)), Z.add_0_r; reflexivity)
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite HWv; lia) ltac:(cbn; lia)) as VV
      | 88 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 88 8%N (SOff 36 0)
          (SHADOW_OFF + frame_addr lyc 1 pos / 8) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(rewrite (mfe_d_off _ 36 (SHADOW_OFF + frame_addr lyc 1 pos / 8) 0 X36 ltac:(rewrite HSB; lia)
                  ltac:(rewrite HSB; lia)), Z.add_0_r; reflexivity)
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite HSB; lia) ltac:(cbn; lia)) as VV
      | 96 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 96 8%N (SOff 34 0)
          (frame_addr lyc 1 pos) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(rewrite (mfe_d_off _ 34 (frame_addr lyc 1 pos) 0 X34 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity)
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV
      | 104 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 104 8%N (mf_shx 33 9136)
          (SHADOW_OFF + (mv_c v + seg_spec.MC_GEN) / 8) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mf_denot_shx _ 33 (mv_c v) 9136 X33 X32 ltac:(lia) ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_GEN;
                pose proof (Z.div_pos (mv_c v + 9136) 8 ltac:(lia) ltac:(lia));
                pose proof (Z.div_le_upper_bound (mv_c v + 9136) 8 (2 ^ 47) ltac:(lia) ltac:(lia));
                rewrite HSB; lia)
          ltac:(cbn; lia)) as VV
      | 112 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 112 8%N (SOff 33 0) (mv_c v) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(rewrite (mfe_d_off _ 33 (mv_c v) 0 X33 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity)
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV
      | 128 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 128 8%N (SOff 33 8192)
          (mv_c v + seg_spec.MC_N) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 33 (mv_c v) 8192 X33 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N; lia) ltac:(cbn; lia)) as VV
      | 136 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 136 8%N (SLit 0) 0 HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_lit _ 0 ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV
      | 144 => pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 144 8%N (SOff 34 32)
          (frame_addr lyc 1 pos + 32) HRS X2
          ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
          ltac:(exact (mfe_d_off _ 34 (frame_addr lyc 1 pos) 32 X34 ltac:(lia) ltac:(lia)))
          ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV
      end;
      change (N.to_nat 8) with 8%nat in VV; exact VV
    end. }
  assert (V120' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos)).
  { pose proof (field_of_region _ _ 2%nat _ _ 16 216 16 216 120 8%N (SOff 34 0) (frame_addr lyc 1 pos) HRS X2
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(rewrite (mfe_d_off _ 34 (frame_addr lyc 1 pos) 0 X34 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as VV.
    change (N.to_nat 8) with 8%nat in VV. exact VV. }
  assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) (mfe_c1 v)).
  { refine (mf_entry_m.mfe_bump_gen (rdW Wc memc) (rdW Wc (ms_mem ms)) (mv_c v) (mfe_c0 v) (G + 1) HMC _ _ _).
    - intros a Ha Hg. apply K; [unfold seg_spec.SEG_M_SIZE in *; lia|].
      unfold RW, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, mf_s1 in *. lia.
    - apply mfe_sa_of_val.
      pose proof (field_of_region _ _ 33%nat _ _ seg_spec.MC_GEN (seg_spec.MC_GEN + 4) seg_spec.MC_GEN
        (seg_spec.MC_GEN + 4) seg_spec.MC_GEN 4%N (SOff 52 1) (G + 1) HRG X33u
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
        ltac:(rewrite (mfe_d_off _ 52 G 1 X52 ltac:(lia) ltac:(lia)); reflexivity)
        ltac:(change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia) ltac:(cbn; lia)) as VV.
      change (N.to_nat 4) with 4%nat in VV. exact VV.
    - lia. }
  destruct (mf_keep_run B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mfe_c0 v) (ms_mem ms) mdw RW MF_LOW_OFF (mfe_c1 v)
    CX CORE HJ K RWok VSH' V120' MC') as (CORE' & LOOPK).
  assert (LOOP' : mf_loop v Wc (ms_mem ms) (mfe_c1 v) None 0 (mv_t v) (mv_s v))
    by exact (LOOPK (mfe_c0 v) None 0 (mv_t v) (mv_s v) LOOP).
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (23%bv : bv 5) Q23. prreg HS2 (24%bv : bv 5) Q24.
  prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (22%bv : bv 5) Q22. prreg HS2 (25%bv : bv 5) Q25.
  prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (20%bv : bv 5) Q20.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { split; [|split; [|split]].
    - apply (mf_regs_ex_of B v lyc pos regs1 (ms_regs ms) RX).
      + rewrite Q2. apply EE. reflexivity.
      + rewrite Q3. apply EE. reflexivity.
      + rewrite Q4. apply EE. reflexivity.
      + rewrite Q8. apply EE. reflexivity.
      + rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
      + rewrite Q18, E32, R18. reflexivity.
      + rewrite Q23, E34, R23. reflexivity.
      + rewrite Q24, E36, R24. reflexivity.
    - rewrite Q19. reflexivity.
    - rewrite Q22, E33, unsigned_lit_small by lia. reflexivity.
    - rewrite Q25. exact E33. }
  pmkst HS2.
  refine (HEAD (S (length (mv_s v))) fx v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos (mfe_c1 v) None 0 (mv_t v)
    (mv_s v) CX LS FRM CORE' CELLS' RA' ltac:(lia) _ LOOP' (eq_sym (mf_file_lines v)) _ _ _).
  + intros Hc. apply Hh0. apply Hhd0. exact Hc.
  + rewrite Q26, E26. reflexivity.
  + rewrite Q21. reflexivity.
  + rewrite Q20. reflexivity.
Qed.
(* inside the Sections: the half's hypotheses as its assumptions *)
About mfe_mid_at. Print Assumptions mfe_mid_at.
End e.
End f.
End d.

(* the half at every FP state: the snprintf wrapper returns at its own (mf_entry_d.v MFE_MID_F) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis HEAD : forall n, MF_HEAD_F B n.
Hypothesis EXIT : MF_EXIT_F B.
Lemma mfe_mid_F : MFE_MID_F (rc := rc) (SK := SK) (PI := PI) B.
Proof. intros fx0. exact (mfe_mid_at (fx := fx0) B VOBJS HEAD EXIT). Qed.
About mfe_mid_F. Print Assumptions mfe_mid_F.
End i.
End h.
End g.
About mfe_mid_F. Print Assumptions mfe_mid_F.
