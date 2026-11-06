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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 1370 of its 1422 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): segment S_MF_KKNOCKP, part 4: the knock line
   (KK_R1 0x86a90 with a0 = 1 -> the m_refuse call 0x86afc -> 0x86b00 -> KDONE). A walk lane of the image-B m_file-family owner's
   G2B. proves no function (kind: segment lemmas of m_file's walk).

   THE CODE: 0x86a94 `ld a0,48(s1)` (c + 0x23ac); the instrumented check 0x86aa0 (a load of the shadow byte at
   ((c + 0x23ac) >> 3) + the shadow base and a compare; its slow path 0x86cf0 and the error path 0x86f20, a call of
   errpath_load4, are not reached: m_file_sd.v's mf_she_blk makes the byte 0); `li s4,511`; `lw a0,0(a0)` (n_kept);
   `blt 7,n_kept` -> 0x86af4 (n_kept = 8); the UBSan trap branches 0x86abc `bltu 7,n_kept` and 0x86ac8
   `bltu ~(c + 0x238c),4 n_kept` to the `unimp` 0x86e84, not taken; the check 0x86adc of the 4-byte store at
   c + 0x238c + 4 n_kept (slow path 0x86d48, error path 0x86f3c errpath_store4, not reached); `sw 1` there; `ld
   s9,112(s1)` (c); `li s4,511`; 0x86af4 `mv a0,s9`, `mv a1,s11`; 0x86afc `jal m_refuse`.
   THE PROOF: the seed at KK_R1 with a0 = 1, the frame cells read-only, and one region of the block (atom 33,
   kk_r33): [c + 0x238c, c + 0x23b0), n_kept's word at c + 0x23ac holding the literal n_kept, writable on
   kept_knock[n_kept] only. n_kept is a literal in each run (one lemma per value 0 .. 7, kk_hit_0 .. kk_hit_7, and
   kk_hit_8): the executor then decides both UBSan traps (the literal against 7, and the interval of
   (-1) - (c + 0x238c), atom 33 a heap pointer, against 4 n_kept) and the store's address c + 0x238c + 4 n_kept is
   the region's. After the store the block holds mconf_encp true mcc (mf_kknockp_1.v's kk_encp_store; n_kept = 8:
   kk_encp8), every other byte kept (kept_of_frame), so the cut facts hold with m_file_k.v's mf_corek true
   (kk_keep_blk, image A's mf_keep_winx_k with the target's knock flag a parameter: m_file_k.v states only the
   knock-false target). Then m_file_rf.v's mf_refuse_step with knock = true and part 3's kk_after at 0x86b00.
   Section hypotheses: VOBJS (the seed), SIGP, SSP, RELRO, M_REFUSE (mf_refuse_step's). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegGlob SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_refuse_c m_file_m m_file_mdl m_file_sd m_file_k m_file_rf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kknockp_1 mf_kknockp_3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the block's region of the knock run: kept_knock[0 .. 8) and n_kept (atom 33 = c), n_kept's word holding nz,
   writable on kept_knock[nz] when w *)
Definition kk_r33 (nz : Z) (w : bool) : YP09.region :=
  YP09.mkRegion (Some 33%nat) seg_spec.MC_KNOCK (seg_spec.MC_NKEPT + 4)
    (if w then seg_spec.MC_KNOCK + 4 * nz else 0) (if w then seg_spec.MC_KNOCK + 4 * nz + 4 else 0)
    [YP09.mkChunk seg_spec.MC_NKEPT (CVal 4 (SLit nz))].

(* image A's m_file_s_hdrb_5.v hb5_val_of_sa / hb5_sa_of_val (a working branch), restated *)
Lemma kk_val_of_sa : forall segs H mem a n z, sa_val (aview segs H mem) a n z -> val_mem segs (mrestrict H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hv. unfold le_byte.
symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Lemma kk_sa_of_val : forall segs H mem a n z, val_mem segs (mrestrict H mem) a n z -> sa_val (aview segs H mem) a n z.
Proof.
intros segs H mem a n z Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold le_byte. apply bv_wrap_small. change (bv_modulus 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.

(* the state's form, computed *)
Ltac kk_norm HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
(* a register's value at a run's final state: its symbolic value computed *)
Ltac kk_regv HS r :=
  rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS);
  lazymatch goal with |- sv_denot _ (sr_get ?R ?rr) = _ =>
    let e := eval vm_compute in (sr_get R rr) in change (sr_get R rr) with e end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* the geometry of a cut state (image A's m_file_k.v mf_geo, with B named) *)
Ltac kk_geo B v lyc Sc pos CX0 CORE rc :=
  pose proof CORE as (HJg & _); pose proof HJg as (HAR & _ & _ & _ & _ & Hfrs & _);
  assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity);
  destruct (mf_frame_facts B _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6);
  destruct (mf_sp0 B v CX0) as (Sp1 & Sp2 & Sp3);
  destruct (mf_blk_c_k B _ _ _ _ _ _ _ _ _ _ CX0 CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2);
  destruct (al_blocks _ B (YG0q.AR_laws_ok _ B) _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & Bk3 & Bk4 & _ & Bk6);
  pose proof (sep_block_frame _ B (YG0q.AR_laws_ok _ B) _ _ _ _ _ bc mbc 1 pos HAR Hbc Hin) as Hsep;
  change (fs_frame_bytes 1) with 128 in Hsep; unfold zdisjoint in Hsep; cbn [fst snd] in Hsep;
  assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity); rewrite HSTK in Sp1;
  pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32;
  pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8;
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8;
  pose proof (@YG0f.ASAN_CEIL_range rc) as ((CRlo & CRhi) & CRal); unfold YG0f.ASAN_CEIL in CRlo, CRhi, CRal.

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
Hypothesis VOBJS : seg_val_objs.
Let RUNTO := paj_run_to B LAWS.
#[local] Notation JE v pos ly S W mem md :=
  (ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] ly S W mem md 0).

(* m_file_k.v's mf_keep_k with the target's knock flag knock' a parameter (its own target is knock = false) *)
Lemma kk_keep_k : forall knock knock' v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) lowsh' mcc',
mf_cx B v -> mf_corek B knock v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc S2 W2 mem2 md2 ->
Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H W2) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos) ->
sa_mconfp knock' (rdW W2 mem2) (mv_c v) mcc' ->
mf_corek B knock' v lyc S2 W2 mem2 md2 pos lowsh' mcc'.
Proof.
intros knock knock' v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW lowsh' mcc' CX0 CORE HJ2 HP2 K RWok VSH' V120'
  MC'.
pose proof CORE as (_ & HPerm & VFL & VSH & VSV & V120 & Hmc & Hac & Htl).
kk_geo B v lyc Sc pos CX0 CORE rc.
pose proof HJ2 as (HAR2 & _).
assert (Hbc' : In (bc, mbc) (ablocks B lyc S2)) by (apply (Permutation_in _ (Permutation_sym HP2)); exact Hbc).
split; [exact HJ2|]. split; [exact (perm_trans HP2 HPerm)|]. split.
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
split; [exact V120'|].
split; [exact MC'|].
split.
{ destruct Hac as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc'); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc'); unfold seg_spec.SEG_M_SIZE in *; lia. }
apply (mf_tail_keep_k B knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW _ CX0 CORE HJ2 K RWok); [| | exact Htl].
- unfold seg_spec.SEG_M_SIZE in *. lia.
- intros x Hx. lia.
Qed.

(* a run whose reader changed only bytes RW of the mconf block, which now holds mcc' with the pending flag knock':
   every cut fact at the new memory (m_file_k.v's mf_keep_winx_k with an empty window, target knock') *)
Lemma kk_keep_blk : forall knock' v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur mem2 md2 (RW : Z -> Prop) mcc',
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) ->
sa_mconfp knock' (rdW Wc mem2) (mv_c v) mcc' ->
mf_corek B knock' v lyc Sc Wc mem2 md2 pos lowsh mcc' /\ mf_cells v lyc pos mem2 Wc cur /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 Wc np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros knock' v lyc Sc Wc memc mdc pos lowsh mcc cur mem2 md2 RW mcc' CX0 CORE CELLS HJ2 K HE MC'.
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos lowsh mcc CORE) as COREk.
pose proof CORE as (_ & _ & _ & VSH & _ & V120 & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
kk_geo B v lyc Sc pos CX0 COREk rc.
assert (RWok : forall a, RW a -> mf_rw v lyc pos a) by (intros a Ha; unfold mf_rw; right; left; exact (HE a Ha)).
assert (NE : forall a, a < alloc_ceiling -> ~ (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) -> ~ RW a)
  by (intros a H1 H2 HR; exact (H2 (HE a HR))).
assert (NB : forall a, mf_s1 (mv_sp v) + 16 <= a -> ~ RW a)
  by (intros a H1 HR; pose proof (HE a HR); unfold seg_spec.SEG_M_SIZE in *; unfold mf_s1 in *; lia).
assert (RWS : mf_rws v RW) by (intros a HR Ha; exfalso; exact (NB a ltac:(lia) HR)).
split.
{ apply (kk_keep_k false knock' v lyc Sc Wc memc mdc pos lowsh mcc Sc Wc mem2 md2 RW lowsh mcc' CX0 COREk HJ2
    (Permutation_refl _) K RWok); [| |exact MC'].
  - intros i Hi. apply (mf_val_keep Wc Wc memc mem2 RW _ 1 _ K);
      [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
    intros k Hk. change (Z.of_nat 1) with 1 in Hk. apply NE.
    + unfold SHADOW_OFF. lia.
    + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, seg_spec.SEG_M_SIZE in *. lia.
  - exact (mf_slot_keep B v Wc Wc memc mem2 RW 120 _ CX0 K RWS ltac:(lia) ltac:(lia) V120). }
split.
{ apply (mf_keep_cells B v lyc pos Wc Wc memc mem2 RW cur cur CX0 K RWS CELLS).
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply NB. lia. }
split.
{ intros np V. unfold mf_np, mf_slot in V |- *.
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply NB. lia. }
intros mc0 cur0 line p rest LOOP.
exact (mf_loop_keep_k B false v lyc Sc Wc memc mdc pos lowsh mcc Sc Wc mem2 md2 RW mc0 cur0 line p rest CX0 COREk HJ2
  (Permutation_refl _) K RWok LOOP).
Qed.

(* 0x86afc, the knock line's `jal m_refuse`: the block holds mcc with kept_knock[n_kept] pending (mf_corek true),
   a0 = c, a1 = s11 = line + 1, s4 = 511 *)
Definition KK_RH_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_corek B true v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 (mv_c v) -> getr regs1 11 = w64 (line + 1) -> getr regs1 20 = w64 511 ->
mf_at B v Wc regs1 memc mdc KK_RHIT.

(* KK_R1 with a0 = 1 and the literal n_kept nz *)
Definition KK_HIT_AT (n : nat) (nz : Z) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
getr regs1 10 = w64 1 -> Z.of_nat (length (mc_kept mcc)) = nz ->
mf_at B v Wc regs1 memc mdc KK_R1.

(* after the store run (n_kept < 8): the block re-encoded, the cut facts with mf_corek true, then KK_RH *)
Lemma kk_hit_post : forall n, KK_RH_stmt n ->
  forall v lyc Sc Wc memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (rr : bvmap 5 word) mem2 md2,
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  (length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
  mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v -> mf_np v memc Wc (mf_next p rest) ->
  (length (mc_kept mcc) < 8)%nat ->
  JE v pos lyc Sc Wc mem2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 ->
   ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
      mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc mem2 a = rdW Wc memc a) ->
  val_mem SEGS (mrestrict (w_H Wc) mem2) (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1 ->
  mf_regs_at B v lyc pos rr -> getr rr 27 = w64 (line + 1) -> getr rr 10 = w64 (mv_c v) ->
  getr rr 11 = w64 (line + 1) -> getr rr 20 = w64 511 ->
  mf_at B v Wc rr mem2 md2 KK_RHIT.
Proof.
intros n RH v lyc Sc Wc memc mdc pos mcc gi line p rest rr mem2 md2 CX LS FRM CORE CELLS Hn Hne LOOP FIN NP Hlt HJ2 K1
  VK RA2 R27 R10 R11 R20.
pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & HB & HE) & (A0 & A1 & _) & _).
pose proof HE as (HLz & _).
set (k := (Z.to_nat seg_spec.MC_KNOCK + 4 * length (mc_kept mcc))%nat).
assert (Hk : Z.of_nat k = seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc))) by (unfold k, seg_spec.MC_KNOCK; lia).
assert (HX : sa_bytes (rdW Wc mem2) (mv_c v + Z.of_nat k) (le4 (Z_to_bv 64 1))).
{ rewrite Hk. apply kk_bytes_of_val; [lia|]. apply kk_sa_of_val. exact VK. }
assert (HB2 : sa_bytes (rdW Wc mem2) (mv_c v) (upd_bytes bs k (le4 (Z_to_bv 64 1)))).
{ apply (kk_bytes_upd (rdW Wc memc) (rdW Wc mem2) (mv_c v) bs k _ HB HX).
  - rewrite length_le4. apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Hk, HLz. change (Z.of_nat 4) with 4.
    unfold seg_spec.MC_KNOCK, seg_spec.SEG_M_SIZE. lia.
  - intros a Ha Hn'. rewrite length_le4 in Hn'. change (Z.of_nat 4) with 4 in Hn'. rewrite HLz in Ha.
    apply K1; [unfold seg_spec.SEG_M_SIZE in *; lia | lia]. }
assert (MCt : sa_mconfp true (rdW Wc mem2) (mv_c v) mcc).
{ exists (upd_bytes bs k (le4 (Z_to_bv 64 1))). split; [exact HB2 | exact (kk_encp_store mcc bs Hlt HE)]. }
assert (HRW : forall a, mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
  mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4 -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE).
{ intros a Ha. clear - Hlt Ha. unfold seg_spec.MC_KNOCK, seg_spec.SEG_M_SIZE in *. lia. }
destruct (kk_keep_blk true v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) mem2 md2
  (fun a => mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
            mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) mcc CX CORE CELLS HJ2 K1
  HRW MCt) as (COREt & CELLS2 & NPk & LPk).
exact (RH v lyc Sc Wc rr mem2 md2 pos mcc gi line p rest CX LS FRM COREt CELLS2 RA2 Hn Hne (LPk _ _ _ _ _ LOOP) FIN R27
  (NPk _ NP) R10 R11 R20).
Qed.

(* n_kept = 0: the store kept_knock[0] = 1 *)
Lemma kk_hit_0 : forall n, KK_RH_stmt n -> KK_HIT_AT n 0.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 0 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 0 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 0 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 0 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 0 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 0) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 1: the store kept_knock[1] = 1 *)
Lemma kk_hit_1 : forall n, KK_RH_stmt n -> KK_HIT_AT n 1.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 1 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 1 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 1 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 1 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 1 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 1) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 2: the store kept_knock[2] = 1 *)
Lemma kk_hit_2 : forall n, KK_RH_stmt n -> KK_HIT_AT n 2.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 2 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 2) 2); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 2 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 2 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 2 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 2 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 2) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 3: the store kept_knock[3] = 1 *)
Lemma kk_hit_3 : forall n, KK_RH_stmt n -> KK_HIT_AT n 3.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 3 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 3) 3); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 3 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 3 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 3 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 3 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 3) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 4: the store kept_knock[4] = 1 *)
Lemma kk_hit_4 : forall n, KK_RH_stmt n -> KK_HIT_AT n 4.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 4 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 4) 4); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 4 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 4 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 4 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 4 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 4) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 5: the store kept_knock[5] = 1 *)
Lemma kk_hit_5 : forall n, KK_RH_stmt n -> KK_HIT_AT n 5.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 5 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 5) 5); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 5 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 5 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 5 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 5 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 5) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 6: the store kept_knock[6] = 1 *)
Lemma kk_hit_6 : forall n, KK_RH_stmt n -> KK_HIT_AT n 6.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 6 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 6) 6); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 6 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 6 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 6 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 6 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 6) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 7: the store kept_knock[7] = 1 *)
Lemma kk_hit_7 : forall n, KK_RH_stmt n -> KK_HIT_AT n 7.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 7 true)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 7) 7); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 7 true) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 7 true) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 33%nat (mv_c v)); [reflexivity | exact U33 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (kk_fp_knock (mv_c v) (mv_k0 v) (mf_final v) (length (mc_kept mcc)) a);
        [exact Hk0 | apply HKF; lia | unfold seg_spec.MC_KNOCK; lia].
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
(* the run wrote kept_knock[n_kept] only *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) <= a <
     mv_c v + seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)) + 4) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha HnC. rewrite ENZ in HnC.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => mv_c v + seg_spec.MC_KNOCK + 4 * 7 <= x < mv_c v + seg_spec.MC_KNOCK + 4 * 7 + 4) HFr _ a Ha HnC).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U33 in Hr; unfold seg_spec.MC_KNOCK; lia] |]).
  destruct Hinw. }
(* kept_knock[n_kept] = 1 *)
assert (VK : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms))
  (mv_c v + (seg_spec.MC_KNOCK + 4 * Z.of_nat (length (mc_kept mcc)))) 4 1).
{ rewrite ENZ.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS3 eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
  lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wl ?wh ?cs) =>
    pose proof (field_of_region_any E _ 33 (mv_c v) cs lo hi wl wh (seg_spec.MC_KNOCK + 4 * 7) 4%N (SLit 1) HR0 U33
      ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V;
    change (N.to_nat 4) with 4%nat in V;
    assert (Hd : bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity);
    rewrite Hd in V; exact V end. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)) by (kk_regv HS3 (10%bv : bv 5); exact E33).
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25) by (kk_regv HS3 (25%bv : bv 5); rewrite E33, R25; reflexivity).
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (kk_hit_post n RH v lyc Sc Wc memc mdc pos mcc gi line p rest (ms_regs ms) (ms_mem ms) mdq CX LS FRM CORE CELLS
  Hn Hne LOOP FIN NP ltac:(lia) HJ K1 VK RA2 R27' R10' R11' R20').
Qed.

(* n_kept = 8: `blt 7,8` taken to 0x86af4, no store; the pending flag has no slot, so the block holds mcc with it *)
Lemma kk_hit_8 : forall n, KK_RH_stmt n -> KK_HIT_AT n 8.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 ENZ.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HAD & _).
destruct (kk_nkept_val false _ _ _ HMC) as (VNK & HK8).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE LCUR) as Hcur.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np []).
pose proof (mf_corek_of_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as COREk.
kk_geo B v lyc Sc pos CX COREk rc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HAD as (HA0 & HA1 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 1 ltac:(unfold A_TEXT; lia)) as E33.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) np [] 4 ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36. fold E in E32, E33, E34, E36.
assert (U33 : bv_unsigned (ew E 33) = mv_c v) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B33 : base_val E (Some 33%nat) = mv_c v) by (cbn [base_val]; exact U33).
assert (B34 : base_val E (Some 34%nat) = frame_addr lyc 1 pos) by (cbn [base_val]; rewrite E34; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= frame_addr lyc 1 pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B36 : base_val E (Some 36%nat) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (cbn [base_val]; rewrite E36; apply unsigned_lit_small; rewrite HSB; lia).
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v))
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 2 2%bv eq_refl), R2;
      apply mf_w64_u; unfold mf_s1 in *; lia).
assert (B8 : base_val E (Some 8%nat) = mv_sp v)
  by (cbn [base_val]; unfold E; rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 8 8%bv eq_refl), R8;
      apply mf_w64_u; lia).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] KK_R1 true true [] false false
  [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
fold E in HS0.
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS0 A0 eq_refl) as HS1. clear HS0. kk_norm HS1.
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o' Ho'; lia))) as HS2 end.
clear HS1 HR1. kk_norm HS2.
assert (R33ok : region_ok SEGS E (mrestrict (w_H Wc) memc) (kk_r33 8 false)).
{ unfold region_ok, kk_r33. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B33.
  unfold seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Bk4 (mv_c v + o) ltac:(lia))).
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (mv_c v) 0x23ac 4 (SLit 8) 8); [reflexivity | cbn; lia | cbn; lia |].
    change (N.to_nat 4) with 4%nat. apply kk_val_of_sa. rewrite ENZ in VNK. exact VNK. }
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 _ =>
  assert (R33dis : all_disjoint E (kk_r33 8 false) (ss_mem ss2)) end.
{ apply all_disjoint_of_extents. unfold extent_of_region, kk_r33.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B33, B2, B8, B34, B36.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.SEG_M_SIZE in *.
  rewrite HSB in *. pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq]. unfold mf_s1 in *.
  repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ (kk_r33 8 false) HS2 ltac:(vm_compute; reflexivity) R33ok R33dis) as HS3.
clear HS2. kk_norm HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 33 0 9236] E (mrestrict (w_H Wc) memc))
  by (constructor; [exact (mf_she_blk B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [] 9236 CX CORE
       ltac:(unfold seg_spec.SEG_M_SIZE; lia)) | constructor]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HKF : (length (mc_kept mcc) < 8)%nat -> (length (mc_kept mcc) < length (mc_kept (mf_final v)))%nat).
{ intros Hlt. pose proof (kk_refuse_kept mcc (line + 1) true Hlt) as Hkr.
  pose proof (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN) as Hle. lia. }
paj_run_to_tok RUNTO HS3 HJ SHOK Bspan KK_RHIT.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros b0 wlo whi x Hinw Hr. vm_compute in Hinw.
  repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia |]).
  destruct Hinw. }
assert (GR : forall r : Z, In r [2; 3; 4; 8; 9; 18; 23; 24; 19; 22; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ apply (kk_pres_l E _ regs1 v lyc pos (Some gi) np [] (ms_regs ms) _ eq_refl RB
    (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS3)). vm_compute. reflexivity. }
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ rewrite <- R27. exact (GR 27 ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (R20' : getr (ms_regs ms) 20 = w64 511) by (kk_regv HS3 (20%bv : bv 5); reflexivity).
assert (R11' : getr (ms_regs ms) 11 = w64 (line + 1)).
{ kk_regv HS3 (11%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 27 (Z_to_bv 5 27) eq_refl).
  exact R27. }
assert (R10' : getr (ms_regs ms) 10 = w64 (mv_c v)).
{ kk_regv HS3 (10%bv : bv 5). unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np [] 25 (Z_to_bv 5 25) eq_refl).
  exact R25. }
assert (R25' : getr (ms_regs ms) 25 = getr regs1 25).
{ kk_regv HS3 (25%bv : bv 5). unfold E. exact (mfE_reg regs1 v lyc pos (Some gi) np [] 25 (Z_to_bv 5 25) eq_refl). }
assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA);
    lazymatch goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      first [ exact R25' | exact (GR z ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) ] end. }
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
assert (H8 : length (mc_kept mcc) = 8%nat) by lia.
assert (COREt : mf_corek B true v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc).
{ destruct CORE' as (J & P & Fl & Sh & Sv & C & (bs & HB & HE) & Ad & Tl).
  refine (conj J (conj P (conj Fl (conj Sh (conj Sv (conj C (conj _ (conj Ad Tl)))))))).
  exists bs. split; [exact HB | exact (kk_encp8 mcc bs H8 HE)]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with KK_RHIT by (unfold KK_RHIT, AF_m_file; reflexivity) end.
exact (RH v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest CX LS FRM COREt CELLS' RA2 Hn Hne
  (LPk _ _ _ _ _ LOOP) FIN R27' (NPk _ NP) R10' R11' R20').
Qed.

(* KK_R1 with a0 = 1: the knock line, for every n_kept the block encodes (at most 8) *)
Lemma kk_r1_hit : forall n, KK_RH_stmt n ->
  forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z),
  mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 ->
  (length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
  mf_fin (m_refuse mcc (line + 1) true, Some gi) line rest = mf_final v ->
  getr regs1 27 = w64 (line + 1) -> mf_np v memc Wc (mf_next p rest) ->
  getr regs1 10 = w64 1 ->
  mf_at B v Wc regs1 memc mdc KK_R1.
Proof.
intros n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0.
pose proof CORE as (_ & _ & _ & _ & _ & _ & HMC & _).
destruct (kk_nkept_val false _ _ _ HMC) as (_ & HK8).
assert (H : Z.of_nat (length (mc_kept mcc)) = 0 \/ Z.of_nat (length (mc_kept mcc)) = 1 \/
  Z.of_nat (length (mc_kept mcc)) = 2 \/ Z.of_nat (length (mc_kept mcc)) = 3 \/
  Z.of_nat (length (mc_kept mcc)) = 4 \/ Z.of_nat (length (mc_kept mcc)) = 5 \/
  Z.of_nat (length (mc_kept mcc)) = 6 \/ Z.of_nat (length (mc_kept mcc)) = 7 \/
  Z.of_nat (length (mc_kept mcc)) = 8) by lia.
destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]].
- exact (kk_hit_0 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_1 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_2 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_3 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_4 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_5 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_6 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_7 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
- exact (kk_hit_8 n RH v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP A0 H).
Qed.
End e.

Section e2.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis M_REFUSE : forall fx0 : YK11.FPState, m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse)
  SegInstB.STK_m_refuse SegInstB.RLO_A SegInstB.RHI_A SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA.

(* 0x86afc: m_refuse(c, line + 1) with the knock flag pending, back at 0x86b00, then KDONE *)
Lemma kk_s_rhit : forall n, (forall fx0 : YK11.FPState, MF_KDONE_stmt (fx := fx0) B n) -> KK_RH_stmt B n.
Proof.
intros n KD. unfold KK_RH_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest CX LS FRM CORE CELLS RA Hn Hne LOOP FIN R27 NP R10 R11 R20.
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & Hk0 & _).
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (HKEPT : (length (mc_kept (m_refuse mcc (line + 1) true)) <= length (mc_kept (mf_final v)))%nat)
  by exact (mf_kept_le_refuse mcc (line + 1) true (Some gi) (line + 1) (lines (mf_rest rest)) (mf_final v)
    (mf_cur_ok_refuse mcc (Some gi) (line + 1) true LCUR) FIN).
apply (mf_refuse_step B SIGP SSP RELRO M_REFUSE v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc mcc true (Some gi) line p
  rest (mf_next p rest) KK_RHIT CX LS FRM CORE CELLS NP R2 R3 R4 R8 LOOP Hne eq_refl Hk0 ltac:(vm_compute; reflexivity)
  ltac:(unfold KK_RHIT, AF_m_file; lia) R10 R11 HKEPT).
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfx LS2 CORE2 CELLS2 NP2 LOOP2 HPr.
assert (Ely : ly2 = lyc) by (destruct LS as [E1 _]; destruct LS2 as [E2 _]; congruence). subst ly2.
assert (RA2 : mf_regs_at B v lyc pos regs2) by exact (mf_regs_keep B v lyc pos regs1 regs2 RA HPr).
replace (KK_RHIT + 4) with KK_AHIT by (unfold KK_RHIT, KK_AHIT; lia).
apply (kk_after (fx := fx1) B VOBJS n KK_AHIT (or_intror eq_refl) (KD fx1) v lyc S2 W2 regs2 mem2 md2 pos mcc gi
  line p rest true CX LS2 (fxrel_frm0 fx fx1 FRM Hfx) CORE2 CELLS2 RA2 Hn Hne LOOP2 FIN).
- transitivity (getr regs1 27); [exact (HPr 27 ltac:(unfold acallee_saved; lia)) | exact R27].
- exact NP2.
- intros _. transitivity (getr regs1 20); [exact (HPr 20 ltac:(unfold acallee_saved; lia)) | exact R20].
Qed.
End e2.
End f.
End d.
