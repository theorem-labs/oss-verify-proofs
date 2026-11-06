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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 83 of its 130 lines of code are new or changed and 406 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT: the glue every piece of the segment uses -- the text
   left at the head as the pieces read it (fr_text_facts), and the head's facts carried across a run that stores
   nothing (fr_ctx_run). The FRONT segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers a FRONT run leaves as they were and the head's facts name (s3 = ' ' is pinned to the literal in the
   pieces' states, so it is checked apart) *)
Definition FR_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 21; 24; 25; 26]%bv.

(* a run whose regions are all read-only keeps every byte (mix_call.v:298-303 at 501c0d516c69) *)
Lemma fr_frame_ro : forall E rs (m m' : word -> option byte),
frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' Hf Hw x. apply Hf. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hw r Hr) as H. apply Z.leb_le in H. lia.
Qed.
(* an atom of the environment, offset by k *)
Lemma fr_U_atom_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
U E (SOff n k) = v + k.
Proof.
intros E n v k Hn Hv Hvk. rewrite U_SOff, Hn, unsigned_lit_small by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte the reader sees is a byte (mix_call.v:64-69 at 501c0d516c69) *)
Lemma fr_aview_byte : forall H mem a z, aview SEGS H mem a = Some z -> 0 <= z < 256.
Proof.
intros H mem a z Ha. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Ha. injection Ha as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.
Lemma fr_mbyte_of_aview : forall H mem a z, aview SEGS H mem a = Some z -> 0 <= z < 256 ->
mbyte SEGS (mrestrict H mem) a = Some (Z_to_bv 8 z).
Proof.
intros H mem a z Ha Hz. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma fr_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
(* one byte of the reader as the one-byte val_mem a region chunk asks *)
Lemma fr_val_mem1 : forall H mem a z, aview SEGS H mem a = Some z -> val_mem SEGS (mrestrict H mem) a 1 z.
Proof.
intros H mem a z Ha k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
pose proof (fr_aview_byte H mem a z Ha) as Hz. rewrite fr_le_byte1 by exact Hz.
apply fr_mbyte_of_aview; [exact Ha | exact Hz].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the text left at the head: inside a live heap block, the line's bytes as the reader sees them, and the text with
   its NUL addressable *)
Lemma fr_text_facts : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
4096 <= p /\ p + Z.of_nat (length rest) + 1 <= alloc_ceiling /\
(forall k, (k < length (mf_line rest))%nat -> rdW Wc memc (p + Z.of_nat k) = Some (nth k (mf_line rest) 0)) /\
(forall k, (k < length (mf_line rest))%nat -> 0 <= nth k (mf_line rest) 0 < 256) /\
range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length rest) + 1).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
destruct CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MP & _).
destruct MP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & TSTR & TLEN & (b & m & Hin & Hb & Hm) & _).
destruct CORE as (HJ & HPERM & _).
pose proof (proj1 HJ) as HAR.
assert (Hin2 : In (b, m) (ablocks B lyc Sc)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hin2) as (Hb16 & Hb4096 & Hbceil & _).
destruct LOOP as (Hlr & Hrest & Hp & STR & ADDR & _).
destruct STR as ((ZS & NZ) & TAIL).
destruct ADDR as (_ & _ & _ & RA0 & _).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof (fr_line_len rest) as HLL.
assert (BY : forall k, (k < length (mf_line rest))%nat -> rdW Wc memc (p + Z.of_nat k) = Some (nth k (mf_line rest) 0)).
{ intros k Hk. rewrite <- (fr_line_nth rest k Hk). rewrite (ZS k) by (rewrite length_app; cbn [length]; lia).
  rewrite app_nth1 by lia. reflexivity. }
split; [lia|]. split; [lia|]. split; [exact BY|]. split; [|exact RA0].
intros k Hk. exact (fr_aview_byte _ _ _ _ (BY k Hk)).
Qed.

(* a run whose regions are all read-only keeps the reader (mix_call.v:304-309 at 501c0d516c69) *)
Lemma fr_aview_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hw a. unfold aview, mbyte. rewrite (fr_frame_ro E rs _ _ Hf Hw). reflexivity.
Qed.
Lemma fr_ra_eq : forall (rd rd' : reader) Bx a n, (forall x, rd' x = rd x) ->
range_addressable rd Bx a n -> range_addressable rd' Bx a n.
Proof. intros rd rd' Bx a n Hk H x Hx. rewrite Hk. exact (H x Hx). Qed.

(* the head's facts across a run that stores nothing: the journal is the run's, the reader is the same byte for
   byte, and the registers the facts name are kept *)
Lemma fr_ctx_run : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2,
fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
(forall a, rdW Wc mem2 a = rdW Wc memc a) ->
(forall r, In r FR_KEPT -> getr regs2 r = getr regs1 r) -> getr regs2 19 = w64 0x20 ->
fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n regs2 mem2 md2 CTX HJ2 KM K R19'.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 CX CORE CELLS HJ2 (fun a _ => KM a))
  as (C1 & C2 & _ & C4).
pose proof RA as (_ & _ & _ & _ & _ & _ & R19 & _).
refine (conj CX (conj LS (conj FRM (conj C1 (conj C2 (conj _ (conj _ (conj Hn (conj Hne
  (conj (C4 _ _ _ _ _ LOOP) (conj EQ _))))))))))).
- apply (mf_regs_at_of B v lyc pos regs1 regs2 RA); try (apply K; cbv; tauto). rewrite R19', R19. reflexivity.
- rewrite (K 24%bv ltac:(cbv; tauto)). exact R24.
- rewrite (K 21%bv ltac:(cbv; tauto)). exact R21.
Qed.
End e.
End f.
End d.
