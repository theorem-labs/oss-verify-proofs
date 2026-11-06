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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 542 of its 600 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB: the join and the
   three short returns, each a run of a few instructions with no call in it, from an inner cut of mf_hdrb_2.v to the
   next cut. A walk lane of the image-B m_file-family owner's G2B (a piece agent). ADAPTED from image A's
   lib/A/Prog/m_file_s_hdrb_5.v (the image-A m_file-family lane) at image B's pcs, registers and frame cells. Each
   lemma is `<the next statement's _F> -> <this statement's _F>`; no piece changes the FP state, so each is proved at
   one FP state fx0 and the next statement is taken there.
     hb5_join  : MF_TAIL_F n  -> MFB_JOIN_F n    JOIN  0x86ba0 .. 0x86bd8, 0x867e4 `ld s10,152(s1)`, 0x867e8 `j` TAIL
     hb5_rref1 : MFB_JOIN_F n -> MFB_RREF1_F n   RREF1 0x86618 `j 0x86ba0`
     hb5_rmcpy : MFB_JOIN_F n -> MFB_RMCPY_F n   RMCPY 0x86b9c `li s4,511`, into 0x86ba0
     hb5_rref2 : MF_TAIL_F n  -> MFB_RREF2_F n   RREF2 0x86b4c `sd zero,136(s1)`, 0x86b50 `j 0x867e4`,
                                                       0x867e4 `ld s10,152(s1)`, 0x867e8 `j` TAIL
   THE JOIN (the neutral listing of m_file in image B lines 666-680, 427-428): 0x86ba0 `andi a0,s5,3`, 0x86ba4
   `bnez a0` to the `unimp` 0x86e84 (the UBSan alignment trap of g->gen; s5 = g = c + 256 i with c mod 16 = 0: s5 is
   the extra atom 52, which carries the fact HPTR 4 (16-aligned), and the token executor decides the branch not
   taken); the instrumented check of the 4-byte load of c->gen (0x86ba8-0x86bb0: a load of the shadow byte whose
   address 104(s1) holds, (c + 0x23b0 >> 3) + the shadow base, and a compare; its slow path 0x86d00-0x86d10 and the
   error path 0x86f24-0x86f28, a call of an errpath_* entry, which the proof shows is not reached); 0x86bb4 `sd
   s5,136(s1)` (cur = g); a0 = g + 252 and the check of the 4-byte store there (0x86bb8-0x86bd0: the shadow byte at
   (a0 >> 3) + s2 and a compare; slow path 0x86d14-0x86d20, error path 0x86f2c, not reached); `ld a1,56(s1)`, `lw
   a1,0(a1)` (c->gen); 0x86bd4 `sw a1,0(a0)` (g->gen = c->gen); 0x86bd8 `j 0x867e4`.
   THE SYMBOLIC STATE (m_file_sd.v's mf_seed, atoms there): the JOIN seeds xs = [g; mc_gen mcc] (atoms 52, 53), pins
   s5 to atom 52 with the fact HPTR 4, and adds two regions: the gen cell of the block (atom 33, [0x23b0, 0x23b4),
   read-only, its chunk atom 53) and the entry's gen field (atom 52, [252, 256), written, no chunk). Its two shadow
   entries are mkSHE 33 0 9144 (mf_she_blk: c->gen's granule ends at c + 0x23b8) and mkSHE 52 0 260 (mf_she_at: the
   token executor's `covered x 8` asks 252 + 8 <= she_hi of the entry at atom 52; [g, g + 260) is inside the block
   because i < 32). The frame cells' region is writable only on [136, 144) (cur), so the run's written set is cur and
   g->gen. RREF1 and RMCPY run the seed with every region read-only. RREF2 runs the seed with cells = false (only
   120(s1) and 152(s1) as chunks): the statement bounds the head's cursor cur0 only through mf_loop's mf_cur_ok of the
   start model mc0, so the seed does not state 136(s1); it is written with 0 and read off the final region.
   AFTER THE RUN: the bytes outside the run's write windows are kept (kept_of_frame); m_file_k.v's mf_keep_run_s
   (JOIN, RREF2) or mf_carry_eq (RREF1, RMCPY) carries mf_core, mf_cells and mf_loop; the JOIN's block holds
   m_upd mcc i (ms_with_gen (mc_gen mcc)) (mf_hdrb_1.v's mconf_enc_seg / mseg_enc_gen through hb_bytes_upd, the
   stored word read off the final entry region). At the tail the line loop's facts step to the next line: the text
   half from m_file_k.v's mf_loop_next at the start model, the model half from mf_hdrb_4.v's hb4_tail_model.
   Section hypothesis: VOBJS (the seed's literal bridge) only. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m m_file_mdl
  m_file_sd m_file_k mf_hdrb_1 mf_hdrb_2 mf_hdrb_3 mf_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the JOIN's regions ===================================== *)
(* the gen cell of the block (atom 33): c->gen, read by `lw a1,0(a1)` (0x86bcc), its value atom 53 = mc_gen mcc *)
Definition hb5_r33 : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x23b0 0x23b4 0 0 [YP09.mkChunk 0x23b0 (CVal 4 (SOff 53 0))].
(* the gen field of the entry g = &c->seg[i] (atom 52): g->gen, written by `sw a1,0(a0)` (0x86bd4) *)
Definition hb5_rg : YP09.region := YP09.mkRegion (Some 52%nat) 252 256 252 256 [].
(* the two checks' shadow entries: the block up to c + 9144 (c->gen's granule), the entry up to g + 260 *)
Definition hb5_SH : list shent := [mkSHE 33 0 9144; mkSHE 52 0 260].

(* the value chunk at offset off of a concrete chunk list (SLit 0 if there is none) *)
Fixpoint hb5_find (off : Z) (cs : list YP09.chunk) : sv :=
  match cs with
  | [] => SLit 0
  | YP09.mkChunk o (CVal _ e) :: r => if Z.eqb o off then e else hb5_find off r
  | _ :: r => hb5_find off r
  end.

(* membership of a concrete chunk in a concrete chunk list *)
Ltac hb5_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the state's form, computed *)
Ltac hb5_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
(* the awr_ok goal with its region list computed *)
Ltac hb5_awr_norm :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
(* every region of the state is read-only *)
Ltac hb5_awr_ro := hb5_awr_norm; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the 8-byte (w-byte) field at offset off of a final region HR whose base atom U names *)
Ltac hb5_field HR U off w V :=
  lazymatch type of HR with region_ok _ ?E _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    let e := eval vm_compute in (hb5_find off cs) in
    pose proof (field_of_region_any E _ n _ cs lo hi wlo whi off w e HR U ltac:(hb5_in) ltac:(cbn; lia)) as V
  end.

(* ===================================== byte-level helpers ===================================== *)
(* a value read through the ASan reader is a value of the restricted memory, and back *)
Lemma hb5_val_of_sa : forall segs H mem a n z, sa_val (aview segs H mem) a n z -> val_mem segs (mrestrict H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hv. symmetry.
lazymatch goal with |- bv_wrap 8 ?x = ?y => replace y with x by reflexivity end.
apply bv_wrap_small. change (bv_modulus 8) with 256.
lazymatch goal with |- 0 <= ?f _ _ _ < 256 => unfold f end.
apply Z.mod_pos_bound. lia.
Qed.
Lemma hb5_sa_of_val : forall segs H mem a n z, val_mem segs (mrestrict H mem) a n z -> sa_val (aview segs H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned.
lazymatch goal with |- bv_wrap 8 ?x = ?y => replace y with x by reflexivity end.
apply bv_wrap_small. change (bv_modulus 8) with 256.
lazymatch goal with |- 0 <= ?f _ _ _ < 256 => unfold f end.
apply Z.mod_pos_bound. lia.
Qed.
(* the low word of a sign-extended 32-bit value *)
Lemma hb5_sext32_low : forall x, 0 <= x < 2 ^ 32 -> (zcanon (bv_swrap 32 (x mod 2 ^ 32))) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* an atom holding x, as a symbolic value *)
Lemma hb5_atom_val : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k Hn Hx. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hx. reflexivity. Qed.
(* the stored word of the JOIN: the low 4 bytes of the sign-extended load of c->gen *)
Lemma hb5_sext_val : forall E (n : nat) g, ew E n = Z_to_bv 64 g -> 0 <= g < 2 ^ 32 ->
bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_N 4) = g.
Proof.
intros E n g Hn Hg. change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, (U_atom E n g Hn ltac:(lia)). change (Z.of_N 32) with 32. change (8 * Z.of_N 4) with 32.
apply hb5_sext32_low. exact Hg.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* the numbers every piece reads: the block below the ceiling, the stack above it, the frame *)
Lemma hb5_geo : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= alloc_ceiling /\ mv_c v mod 16 = 0 /\
alloc_ceiling + 8592 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\
mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320 /\
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
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S3, P1.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
repeat split; try lia.
Qed.

(* the line loop's facts at the next line: the text half from mf_loop_next at the start model mc0, the model half
   from hb4_tail_model *)
Lemma hb5_loop_tail : forall v Wc memc mc0 cur0 mcc cur line p rest,
mf_loop v Wc memc mc0 cur0 line p rest -> hb_mod (mv_k0 v) mc0 mcc cur -> rest <> [] ->
mf_loop v Wc memc mcc cur (line + 1) (mf_next p rest) (mf_rest rest).
Proof.
intros v Wc memc mc0 cur0 mcc cur line p rest LP HM Hne.
pose proof LP as (_ & _ & _ & _ & _ & Hc0 & _).
destruct (mf_loop_next v Wc memc mc0 cur0 line p rest mc0 cur0 LP Hne ltac:(lia) ltac:(lia) ltac:(lia) Hc0)
  as (T1 & T2 & T3 & T4 & T5 & _).
destruct (hb4_tail_model v Wc memc mc0 mcc cur0 cur line p rest LP HM Hne) as (M1 & M2 & M3 & M4 & M5 & M6).
unfold mf_loop. exact (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj M1 (conj M2 (conj M3 (conj M4 (conj M5 M6)))))))))).
Qed.

(* ===================================== the four pieces at one FP state ===================================== *)
(* RREF1 0x86618: `j 0x86ba0`, a run that writes nothing, then the join *)
Lemma hb5_rref1_at : forall n, MFB_JOIN_stmt B n -> MFB_RREF1_stmt B n.
Proof.
intros n HJn. unfold MFB_RREF1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA Hlen Hne LP HM Hi FIN R21 R20 R27 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof HM as (Hc0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur0 CX CORE Hc0) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
pose proof CORE as (HJ & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur0 (mf_next p rest) [] MFB_RREF1
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur0 (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur0 (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. hb5_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MFB_JOIN.
{ hb5_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) _ pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE HJ K0 LP)
  as (CORE' & LOOP' & CELLSf & NPf).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (27%bv : bv 5) Q27.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pmkst HS1.
apply (HJn v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mc0 mcc cur0 line p rest i CX LS FRM CORE' (CELLSf cur0 CELLS)
  RA' Hlen Hne LOOP' HM Hi FIN).
+ rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
+ rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ exact (NPf _ NP).
Qed.

(* RMCPY 0x86b9c: `li s4,511`, a run that writes nothing, then the join *)
Lemma hb5_rmcpy_at : forall n, MFB_JOIN_stmt B n -> MFB_RMCPY_stmt B n.
Proof.
intros n HJn. unfold MFB_RMCPY_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA Hlen Hne LP HM Hi FIN R21 R27 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof HM as (Hc0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur0 CX CORE Hc0) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
pose proof CORE as (HJ & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur0 (mf_next p rest) [] MFB_RMCPY
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur0 (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur0 (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. hb5_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MFB_JOIN.
{ hb5_awr_ro. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) _ pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE HJ K0 LP)
  as (CORE' & LOOP' & CELLSf & NPf).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (27%bv : bv 5) Q27.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pmkst HS1.
apply (HJn v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mc0 mcc cur0 line p rest i CX LS FRM CORE' (CELLSf cur0 CELLS)
  RA' Hlen Hne LOOP' HM Hi FIN).
+ rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
+ rewrite Q20. first [reflexivity | vm_compute; reflexivity].
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ exact (NPf _ NP).
Qed.

(* RREF2 0x86b4c: 136(s1) := 0 (cur = NULL), `j 0x867e4`, s10 := 152(s1), `j` TAIL *)
Lemma hb5_rref2_at : forall n, MF_TAIL_stmt B n -> MFB_RREF2_stmt B n.
Proof.
intros n HT. unfold MFB_RREF2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest
  CX LS FRM CORE CELLS RA Hlen Hne LP HM FIN R20 R27 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc None (mf_next p rest) [] MFB_RREF2
  false true [] false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia)
  (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos None (mf_next p rest) []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None (mf_next p rest) []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E38.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply mf_w64_u; lia).
(* the frame cells writable only on [136, 144): the cur cell *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 136 144) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 136 144 HR1
      ltac:(intros o Ho; apply (proj1 (proj2 (proj2 HR1))); cbn; lia))) as HS1 end.
clear HS0 HR1. hb5_norm HS1.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
paj_run_to_tok RUNTO HS1 HJ SHOK Bspan MF_TAIL.
{ hb5_awr_norm.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite ?HSTK; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the bytes outside the cur cell are kept *)
set (RW := fun x => mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; unfold RW; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U2 in Hr; lia] |]);
    destruct Hinw | ] end.
(* 136(s1) holds 0 = mf_cur_ptr c None *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 1%nat _ HS1 eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
hb5_field HRS U2 136 8%N V136.
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) None)).
{ cbn [mf_cur_ptr]. lazymatch type of V136 with val_mem _ _ _ _ ?x => replace x with 0 in V136 by (vm_compute; reflexivity) end.
  change (N.to_nat 8) with 8%nat in V136. exact V136. }
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj. pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44 - 2 ^ 20) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH j Hj)].
  intros k Hk HR. unfold RW, SHADOW_OFF in HR. lia. }
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) RW _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE; lia | intros a Ha HR; unfold RW in HR; unfold seg_spec.SEG_M_SIZE in Ha; lia
    | exact Hmc]. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold RW in Ha; unfold mf_rw; right; right; right; right; right; lia).
assert (RWS : mf_rws v RW) by (intros a Ha _; unfold RW in Ha; left; exact Ha).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur0 (ms_mem ms) _ RW MF_LOW_OFF None mcc
  CX CORE CELLS HJ K RWok RWS VSH' V136' MC') as (CORE' & CELLS' & LOOPK).
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (27%bv : bv 5) Q27. prreg HS1 (20%bv : bv 5) Q20.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pose proof (hb_mf_rest_lt rest Hne) as Hrl.
pmkst HS1.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc None (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA').
+ lia.
+ exact (hb5_loop_tail v Wc (ms_mem ms) mc0 cur0 mcc None line p rest (LOOPK _ _ _ _ _ LP) HM Hne).
+ exact FIN.
+ rewrite Q26, E38. reflexivity.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.

(* JOIN 0x86ba0: the trap 0x86ba4, the check of c->gen, cur = g, the check of g->gen, g->gen := c->gen, `j 0x867e4`,
   s10 := 152(s1), `j` TAIL *)
Lemma hb5_join_at : forall n, MF_TAIL_stmt B n -> MFB_JOIN_stmt B n.
Proof.
intros n HT. unfold MFB_JOIN_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest i
  CX LS FRM CORE CELLS RA Hlen Hne LP HM Hi FIN R21 R20 R27 NP.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof HM as (Hc0 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur0 CX CORE Hc0) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mc0 cur0 line p rest CX CORE LP) as Hnp.
destruct (hb5_geo v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold seg_spec.SEG_M_SIZE in G2.
pose proof CORE as (HJ & HPerm & _ & VSH & _ & _ & Hmc & Hac & _).
destruct (hb_mconf_bounds _ _ _ Hmc) as (Bn & _ & Bg & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (Hi32 : (i < 32)%nat) by lia.
(* the entry is one of the final model's *)
assert (Hfin : (i < length (mc_seg (mf_final v)))%nat).
{ rewrite <- FIN.
  assert (Hc : mf_cur_ok (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i)).
  { unfold mf_cur_ok. rewrite (proj1 (m_upd_sizes mcc i _)), upd_nth_length. exact Hi. }
  destruct (hb_fin_grows (m_upd mcc i (ms_with_gen (mc_gen mcc)), Some i) line rest Hc) as [G _].
  cbn [fst] in G. rewrite (proj1 (m_upd_sizes mcc i _)), upd_nth_length in G. lia. }
set (g := seg_spec.mseg_addr (mv_c v) i) in *.
assert (Hg : g = mv_c v + 256 * Z.of_nat i) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mbc 1 pos HAR Hbc Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
unfold in_app in Hbapp. unfold seg_spec.SEG_M_SIZE in Hbc2.
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
(* the seed, at the head's cursor cur0, with xs = [g; mc_gen mcc] *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur0 (mf_next p rest) [g; mc_gen mcc] MFB_JOIN
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
(* the shadow entries of the two checks *)
assert (SHOK : sh_ok SEGS (SOff 32 0) hb5_SH (mfE regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc])
  (mrestrict (w_H Wc) memc)).
{ unfold hb5_SH, sh_ok. apply Forall_cons.
  { exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur0 (mf_next p rest) [g; mc_gen mcc] 9144 CX CORE
      ltac:(unfold seg_spec.SEG_M_SIZE; lia)). }
  apply Forall_cons; [|apply Forall_nil].
  apply (mf_she_at _ Wc memc 52 g 260 (mfE_U32 regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc])
    (mfE_xs regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc] 0 ltac:(unfold A_TEXT; lia)) ltac:(lia) ltac:(lia)).
  - destruct (mf_addr_sub _ (mv_c v) 9236 g 260 Hac ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & HRA & _). exact HRA.
  - intros x Hx. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE. lia. }
remember (mfE regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc]) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc]) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (E52 : ew E 52 = Z_to_bv 64 g)
  by (subst E; exact (mfE_xs regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc] 0 ltac:(unfold A_TEXT; lia))).
assert (E53 : ew E 53 = Z_to_bv 64 (mc_gen mcc))
  by (subst E; exact (mfE_xs regs1 v lyc pos cur0 (mf_next p rest) [g; mc_gen mcc] 1 ltac:(unfold A_TEXT; lia))).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36, E38.
set (F := frame_addr lyc 1 pos) in *.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8u : F / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply mf_w64_u; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply mf_w64_u; lia).
assert (U52 : bv_unsigned (ew E 52) = g) by (rewrite E52; apply unsigned_lit_small; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by (cbn [base_val]; exact U2).
assert (B8 : base_val E (Some 8%nat) = mv_sp v) by (cbn [base_val]; exact U8).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
assert (B34 : base_val E (Some 34%nat) = F) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B52 : base_val E (Some 52%nat) = g) by (cbn [base_val]; exact U52).
(* s5 pinned to atom 52 (g) *)
apply (ast_ok_pi_set_reg_fp E _ _ (21%bv : bv 5) (SOff 52 0)) in HS0;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E52; cbn [ms_regs restrict mkst];
     rewrite R21; reflexivity].
(* the gen cell of the block *)
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) hb5_r33).
{ unfold region_ok, hb5_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (mv_c v) 0x23b0 4 (SOff 53 0) (mc_gen mcc));
    [ rewrite (hb5_atom_val E 53 (mc_gen mcc) 0 E53 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  change (N.to_nat 4) with 4%nat. apply hb5_val_of_sa. exact (hb_rd_gen _ _ _ Hmc). }
assert (R33dis : all_disjoint E hb5_r33 (mf_regions true true [] false false [] false MF_LOW_OFF)).
{ apply all_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region, hb5_r33.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ hb5_r33 HS0 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS1.
(* the gen field of the entry *)
assert (Rgok : region_ok SEGS E (mrestrict (w_H Wc) memc) hb5_rg).
{ unfold region_ok, hb5_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B52.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbpres (g + o) ltac:(lia))). }
assert (Rgdis : all_disjoint E hb5_rg (hb5_r33 :: mf_regions true true [] false false [] false MF_LOW_OFF)).
{ apply all_disjoint_of_extents. unfold mf_regions, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs,
    extent_of_region, hb5_r33, hb5_rg.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B52, B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. rewrite HSB in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ hb5_rg HS1 ltac:(vm_compute; reflexivity) Rgok Rgdis) as HS2.
(* the fact on atom 52: g is 16-aligned (c mod 16 = 0), which decides the trap 0x86ba4 *)
assert (F52 : afact_ok E 52 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E52, unsigned_lit_small by lia.
  split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. rewrite Hg.
  replace (mv_c v + 256 * Z.of_nat i) with ((mv_c v / 16 + 16 * Z.of_nat i) * 16)
    by (pose proof (Z.div_mod (mv_c v) 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
pose proof (st_ok_pi_add_fact E _ _ 52 (HPTR 4) HS2 F52) as HS3.
(* the frame cells writable only on [136, 144): the cur cell *)
pose proof (st_ok_pi_region_nth E _ _ 3 _ HS3 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 3 r (set_window r 136 144) HS3 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 136 144 HR1
      ltac:(intros o Ho; apply (proj1 (proj2 (proj2 HR1))); cbn; lia))) as HS end.
clear HS0 HS1 HS2 HS3 HR1. hb5_norm HS.
unfold mf_at.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_TAIL.
{ hb5_awr_norm.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 52%nat g); [reflexivity | exact U52 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    exact (proj1 (hb3_entry_wr B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc i a CX CORE Hfin Hi32 ltac:(unfold g in Ha; lia))). }
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite ?HSTK; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the bytes outside the cur cell and the entry's gen field are kept *)
set (RW := fun x => (mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144) \/ (g + 252 <= x < g + 256)).
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; unfold RW; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr;
       first [lia | rewrite U2 in Hr; left; lia | rewrite U52 in Hr; right; lia] |]);
    destruct Hinw | ] end.
(* the stored word: c->gen *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 0%nat _ HS eq_refl) as HRG. cbn [restrict ms_mem] in HRG.
hb5_field HRG U52 252 4%N V252.
rewrite (hb5_sext_val E 53 (mc_gen mcc) E53 Bg) in V252. change (N.to_nat 4) with 4%nat in V252.
(* 136(s1) holds g = mf_cur_ptr c (Some i) *)
pose proof (st_ok_pi_region_nth E _ (restrict (w_H Wc) ms) 3%nat _ HS eq_refl) as HRS. cbn [restrict ms_mem] in HRS.
hb5_field HRS U2 136 8%N V136.
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) (Some i))).
{ cbn [mf_cur_ptr]. fold g.
  rewrite (hb5_atom_val E 52 g 0 E52 ltac:(lia)), Z.add_0_r, unsigned_lit_small in V136 by lia.
  change (8 * Z.of_N 8) with 64 in V136. rewrite Z.mod_small in V136 by lia.
  change (N.to_nat 8) with 8%nat in V136. exact V136. }
assert (VSH' : forall j, 4 <= j < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + F / 8 + j) 1 MF_LOW_OFF).
{ intros j Hj.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH j Hj)].
  intros k Hk [HR | HR]; [unfold SHADOW_OFF in HR; lia|].
  apply (mf_blk_app B v CX (SHADOW_OFF + F / 8 + j + k));
    [unfold seg_spec.SEG_M_SIZE; lia | unfold SHADOW_OFF; lia]. }
(* the block holds the model with g->gen = c->gen *)
assert (MC' : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) (m_upd mcc i (ms_with_gen (mc_gen mcc)))).
{ destruct Hmc as (bs & Hbs & Henc).
  destruct (mconf_enc_bounds _ _ _ Henc) as (Hlbs & _).
  assert (H9 : Z.of_nat (length bs) = 9236) by (rewrite Hlbs; reflexivity).
  exists (Mem.upd_bytes bs (256 * i + Z.to_nat seg_spec.MS_GEN) (Mem.le4 (Z_to_bv 64 (mc_gen mcc)))).
  split.
  - apply (hb_bytes_upd (rdW Wc memc) (rdW Wc (ms_mem ms)) (mv_c v) bs (256 * i + Z.to_nat seg_spec.MS_GEN)
      (Mem.le4 (Z_to_bv 64 (mc_gen mcc))) Hbs).
    + replace (mv_c v + Z.of_nat (256 * i + Z.to_nat seg_spec.MS_GEN)) with (g + 252)
        by (rewrite Hg; unfold seg_spec.MS_GEN; lia).
      apply hb_bytes_of_val; [exact Bg|]. apply hb5_sa_of_val. exact V252.
    + rewrite Mem.length_le4. change (Z.to_nat seg_spec.MS_GEN) with 252%nat. lia.
    + intros a Ha Hna. rewrite H9 in Ha. rewrite Mem.length_le4 in Hna.
      change (Z.to_nat seg_spec.MS_GEN) with 252%nat in Hna.
      apply K; [lia|]. intros [HR | HR]; [lia|]. apply Hna. rewrite Hg in HR. lia.
  - apply (mconf_enc_seg false mcc bs i (ms_with_gen (mc_gen mcc)) (Z.to_nat seg_spec.MS_GEN)
      (Mem.le4 (Z_to_bv 64 (mc_gen mcc))) Henc Hi).
    + rewrite Mem.length_le4. change (Z.to_nat seg_spec.MS_GEN) with 252%nat. lia.
    + intros fb Hfb. apply mseg_enc_gen; [exact Hfb | exact Bg]. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a Ha. unfold RW in Ha. unfold mf_rw. destruct Ha as [Ha | Ha];
    [right; right; right; right; right; lia | right; left; unfold seg_spec.SEG_M_SIZE; lia]. }
assert (RWS : mf_rws v RW).
{ intros a Ha Hs. unfold RW in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha | exfalso; lia]. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur0 (ms_mem ms) _ RW MF_LOW_OFF (Some i)
  (m_upd mcc i (ms_with_gen (mc_gen mcc))) CX CORE CELLS HJ K RWok RWS VSH' V136' MC') as (CORE' & CELLS' & LOOPK).
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27. prreg HS (20%bv : bv 5) Q20.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q23. apply EE. reflexivity.
  - rewrite Q24. apply EE. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q22. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity. }
pose proof (hb_mf_rest_lt rest Hne) as Hrl.
pmkst HS.
apply (HT v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i) (line + 1)
  (mf_next p rest) (mf_rest rest) CX LS FRM CORE' CELLS' RA').
+ lia.
+ exact (hb5_loop_tail v Wc (ms_mem ms) mc0 cur0 (m_upd mcc i (ms_with_gen (mc_gen mcc))) (Some i) line p rest
    (LOOPK _ _ _ _ _ LP) (hb4_mod_upd (mv_k0 v) mc0 mcc i (ms_with_gen (mc_gen mcc)) (hb4_mod_cur (mv_k0 v) mc0 mcc cur0 (Some i) HM Hi)) Hne).
+ exact FIN.
+ rewrite Q26, E38. reflexivity.
+ rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
+ rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
Qed.

End e.
End f.
End d.

(* ============================ the four pieces at every FP state (the _F forms) ============================ *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Lemma hb5_join : forall n, MF_TAIL_F B n -> MFB_JOIN_F B n.
Proof. intros n HT fx0. exact (hb5_join_at (fx := fx0) B VOBJS n (HT fx0)). Qed.
Lemma hb5_rref1 : forall n, MFB_JOIN_F B n -> MFB_RREF1_F B n.
Proof. intros n HJn fx0. exact (hb5_rref1_at (fx := fx0) B VOBJS n (HJn fx0)). Qed.
Lemma hb5_rmcpy : forall n, MFB_JOIN_F B n -> MFB_RMCPY_F B n.
Proof. intros n HJn fx0. exact (hb5_rmcpy_at (fx := fx0) B VOBJS n (HJn fx0)). Qed.
Lemma hb5_rref2 : forall n, MF_TAIL_F B n -> MFB_RREF2_F B n.
Proof. intros n HT fx0. exact (hb5_rref2_at (fx := fx0) B VOBJS n (HT fx0)). Qed.
(* inside the Sections: the pieces' hypotheses as their assumptions *)
Print Assumptions hb5_join. Print Assumptions hb5_rref1. Print Assumptions hb5_rmcpy. Print Assumptions hb5_rref2.
End i.
End h.
End g.
About hb5_join.
About hb5_rref1.
About hb5_rmcpy.
About hb5_rref2.
Print Assumptions hb5_join.
Print Assumptions hb5_rref1.
Print Assumptions hb5_rmcpy.
Print Assumptions hb5_rref2.
