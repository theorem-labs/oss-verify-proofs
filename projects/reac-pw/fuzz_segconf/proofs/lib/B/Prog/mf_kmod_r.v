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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 352 of its 416 lines of code are new or changed and 389 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD, piece r: from the inner
   cut MK_RRET 0x86880 (fuzz_catalogue_row's return, lib/B/Prog/mf_kmod_m.v) to MK_REFUSE 0x86c08 (no catalogue row)
   or MK_CRET 0x868a4 (checked_memcpy's return). A walk lane of the image-B m_file-family owner's G2B (a piece agent).
   proves no function (kind: segment lemma of m_file's image-B walk, S_MF_KMOD piece r).
   Adapted from image A's lib/A/Prog/m_file_s_kmod_b.v (the branch on the row pointer) and m_file_s_kmod_c.v
   (mkc_cpy_pre, the checked memcpy of low.i into g->model), commit c1e1a58468c5, and from image
   B's lib/B/Prog/mf_hdrb_6.v (the checked memcpy call at image B, commit b2fdc8b4e0d0) and
   mf_krole_d.v (the pinned `beqz`, commit 49f97829985c), at image B's numbers.

   THE CODE (the neutral listing of m_file in image B lines 466-474):
     0x86880 `beqz a0,0x86c08`      a0 = cat_ptr catA (cat_row (h_fold v 24)): 0 goes to MK_REFUSE
     0x86884 `ld a0,136(s1)`        a0 = cur = g = &c->seg[gi] (the cell 136(s1), atom 37 of the seed)
     0x86888 `andi a0,a0,3`
     0x8688c `bnez a0,0x86e84`      the UBSan trap (alignment of cur)
     0x86890 `ld s4,136(s1)`        s4 = g
     0x86894 `addi a0,s4,36`        a0 = g + 36 = &g->model
     0x86898 `addi a2,s5,1`         a2 = ln + 1 (s5 = ln = |h_fold v 24|)
     0x8689c `ld a1,144(s1)`        a1 = low = FB + 32 (the cell 144(s1), atom 34 + 32)
     0x868a0 `jal 0x5596c`          the checked memcpy entry: memcpy(g->model, low, ln + 1); back at MK_CRET 0x868a4
   THE BRANCH 0x86880, by the row: None (a0 = 0): a0 is pinned to the literal 0 (st_ok_pi_pin_reg'), one token run to
     MK_REFUSE (the `beqz` taken), every cut fact kept (m_file_k.v mf_keep_run0: the run writes no byte), MK_REFUSE_stmt
     with the model mk_mod's None arm, m_refuse mcc (line + 1) false. Some r (a0 = catA + 0x128 r): atom 10 (a0) is
     given the fact catA <= a0 <= catA + 0x128 * 10 (mf_kmod_t.v mkt_cat_row_lt: r < 11; catA = 0xa20a0 > 0), so the
     token executor decides the `beqz` not taken.
   THE TRAP EDGE (never stepped over): 0x8688c `bnez a0`, a0 = cur & 3: decided by the token executor from the fact
     HPTR 4 (16-aligned) of atom 37 = 136(s1) = mf_cur_ptr c (Some gi) = c + 256 gi, which holds since c mod 16 = 0
     (mf_cx's m_file_pre); the taken edge to the `unimp` 0x86e84 is never a successor of the run.
   No instrumented check in these instructions (the checked memcpy entry does the checking; the run's three loads
   read the frame cells 136(s1) and 144(s1) at s1, which carry no check).
   THE CALL: the Some run stops at the entry SIGMA SS___asan_memcpy with ra = BASE + MK_CRET; it is stepped by
     PaCall.v aj_intrin_atS under AMEMCPY (lib/B/YG0d.v aintrin_realizes OCpy). Destination [g + 36, g + 36 + ln + 1)
     (mkr_cpy_pre): inside entry gi of the mconf block (ln <= 23), in M_FILE_FP (mf_kmod_t.v mkt_mk_fp_seg with gi <
     |mc_seg (mf_final v)|: mkt_mf_fin_segs_mono and mkt_mk_model_segs on the model equation), present in the block's
     heap block (writable), addressable and its shadow hull visible (the block's AR laws), below the callee window
     under s1. Source low.i = [FB + 32, FB + 32 + ln + 1): its bytes are h_fold v 24 ++ [0] (MK_RRET's sa_zs), it lies
     in the side-stack frame (1, pos) (sa_fframe; shadow 0 since MF_LOW_ON: m_file_sd.v mf_low_addr), apart from the
     block (sep_block_frame). After the call the block holds m_upd mcc gi (mkt_set_model low) (mf_kmod_t.v
     mkt_sa_mconf_set_model), every cut fact is carried by m_file_k.v mf_keep_art (window [s1 - ESTACK, s1), E = the
     destination, inside the block), and MK_CRET_stmt is applied with low = h_fold v 24 (|low| < 24: mkt_hfold_len;
     ~ In 0 low: mkt_hfold_nul; bytes: mkt_hfold_range), s4 = g (callee-saved). The checked memcpy keeps the FP
     state: the lemma is proved at the Section's fx.
   Section hypotheses: VOBJS (m_file_sd.v's seed), AMEMCPY (the call). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_t mf_kmod_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the line loop's facts name the model only through its entry count, its kept list and its two counters, which the
   copy of the model's bytes into entry gi (mkt_set_model) leaves *)
Lemma mkr_loop_set : forall v (Wc : world SEGS) memc mcc gi low cur line p rest,
  mf_loop v Wc memc mcc cur line p rest -> mf_loop v Wc memc (m_upd mcc gi (mkt_set_model low)) cur line p rest.
Proof.
intros v Wc memc mcc gi low cur line p rest (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
destruct (mkt_set_model_counters mcc gi low) as (M1 & M2 & M3 & M4).
unfold mf_loop. rewrite M1, M2, M3.
refine (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj _ (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))).
destruct cur as [i|]; cbn [mf_cur_ok] in L6 |- *; [rewrite M4; exact L6 | exact I].
Qed.

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED (mf_krole_d.v
   kd_pres) *)
Lemma mkr_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* the seed at a K cut's pc with its regions dropped (a run that touches no memory; mf_krole_d.v kd_seed0) *)
Lemma mkr_seed0 : forall v lyc Sc Wc regs1 memc mdc pos mcc pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_regs_at B v lyc pos regs1 ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos None 0 []) (mkSS pc sr_mf [] None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc pc CX CORE RA.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc None 0 [] pc false false [] false false []
  false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia) ltac:(intros Hf; discriminate Hf)
  ltac:(lia) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
exact (st_ok_pi_submem _ (ss_mf pc false false [] false false [] false MF_LOW_ON) _ [] HS0 (submem_nil _) eq_refl).
Qed.

(* the premises of the checked memcpy at 0x868a0 (PaCall.v aj_intrin_atS, OCpy): the destination g->model =
   [g + 36, g + 36 + |low| + 1) lies in entry gi of the mconf block, in the footprint, present, addressable, below the
   callee window under s1; the source low.i = [FB + 32, FB + 32 + |low| + 1) is in the walk's own side-stack frame,
   its bytes read, their shadow 0 (low.i in scope); the two are apart (block / frame). Image A's mkc_cpy_pre
   (m_file_s_kmod_c.v) at image B's frame and stack numbers. *)
Lemma mkr_cpy_pre : forall v lyc Sc Wc memT mdT pos mcc gi (low : list Z) (regsT : bvmap 5 word),
mf_cx B v -> mf_core B v lyc Sc Wc memT mdT pos MF_LOW_ON mcc ->
(gi < length (mc_seg mcc))%nat -> (gi < length (mc_seg (mf_final v)))%nat -> (length low < 24)%nat ->
sa_zs (rdW Wc memT) (frame_addr lyc 1 pos + 32) (low ++ [0]) ->
spZ regsT = mf_s1 (mv_sp v) ->
0 <= Z.of_nat (length low) + 1 < 2 ^ 32 /\
0 <= seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL /\
seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1) <= 2 ^ 63 /\
(forall a, seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL <= a <
    seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1) ->
  awr_byte SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a /\
  ~ (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - ESTACK <= a < mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))) /\
(forall a, seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL <= a <
    seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1) ->
  inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ mv_sp v <= a < ly_top lyc ->
  writable_at SEGS (mrestrict (w_H Wc) memT) a) /\
amem_range (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (Z.of_nat (length low) + 1) /\
range_addressable (rdW Wc memT) SHADOW_OFF (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL)
  (Z.of_nat (length low) + 1) /\
(0 < Z.of_nat (length low) + 1 ->
  shadow_hull_vis (rdW Wc memT) (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (Z.of_nat (length low) + 1)) /\
(0 <= frame_addr lyc 1 pos + 32 /\ frame_addr lyc 1 pos + 32 + (Z.of_nat (length low) + 1) <= 2 ^ 63 /\
 src_ok SEGS Wc regsT memT (frame_addr lyc 1 pos + 32) (Z.of_nat (length low) + 1) /\
 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1) <= frame_addr lyc 1 pos + 32 \/
  frame_addr lyc 1 pos + 32 + (Z.of_nat (length low) + 1) <= seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) /\
 amem_range (frame_addr lyc 1 pos + 32) (Z.of_nat (length low) + 1) /\
 range_addressable (rdW Wc memT) SHADOW_OFF (frame_addr lyc 1 pos + 32) (Z.of_nat (length low) + 1) /\
 (0 < Z.of_nat (length low) + 1 ->
   shadow_hull_vis (rdW Wc memT) (frame_addr lyc 1 pos + 32) (Z.of_nat (length low) + 1))).
Proof.
intros v lyc Sc Wc memT mdT pos mcc gi low regsT CX CORE Hgi Hgif Hlow HZT Hsp.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (mf_low_addr B v lyc Sc Wc memT mdT pos mcc (Z.of_nat (length low) + 1) CORE ltac:(lia)) as (LRA & _).
pose proof CORE as (_ & _ & _ & _ & _ & _ & HMC & _).
pose proof HMC as (bs & _ & (HL & HL32 & _)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mf_blk_c B v lyc Sc Wc memT mdT pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mbc 1 pos HAR Hbc Hfin) as Hsep.
change (fs_frame_bytes 1) with 128 in HFceil, HFapp, Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hg : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
unfold seg_spec.SEG_M_SIZE in Hbc2.
unfold seg_spec.MS_MODEL. rewrite Hg.
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|unfold ESTACK; lia].
  right; left. split.
  - apply (mkt_mk_fp_seg (mv_c v) (mv_k0 v) (mf_final v) gi a Hgif). rewrite Hg. unfold seg_spec.MSEG_SIZE. lia.
  - exists bc, mbc. split; [exact Hbc | lia]. }
split.
{ intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (Hbpres a ltac:(lia))). }
split; [apply (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mbc _ _ HAR Hbc); lia|].
split; [apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mbc _ _ HAR Hbc); lia|].
split; [intros Hn0; apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mbc _ _ HAR Hbc); lia|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha. split; [|rewrite Hsp; unfold ESTACK; lia].
  replace a with (frame_addr lyc 1 pos + 32 + Z.of_nat (Z.to_nat (a - (frame_addr lyc 1 pos + 32)))) by lia.
  rewrite HZT; [discriminate|]. rewrite length_app. cbn [length]. lia. }
split; [lia|].
split; [apply (amem_range_sub_app (frame_addr lyc 1 pos) 128 _ _ HFapp HFceil); lia|].
split; [exact LRA|].
intros Hn0. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memT mdT 1 pos _ _ HAR Hfin);
  change (fs_frame_bytes 1) with 128; lia.
Qed.

(* the None arm: a0 = 0, the `beqz` 0x86880 goes to MK_REFUSE with the cut's state *)
Lemma mkr_none : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (vv : list Z),
MK_REFUSE_stmt B n ->
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
cat_row (h_fold vv 24) = None ->
getr regs1 10 = w64 (seg_spec.cat_ptr SegInstB.catA (cat_row (h_fold vv 24))) ->
mf_at B v Wc regs1 memc mdc MK_RRET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv REF BS HFIN ECR A0.
pose proof BS as (CX & LS & FRM & CORE & CELLS & RA & LEN & NE & LOOP & NP & R27).
assert (HFIN' : mf_fin (m_refuse mcc (line + 1) false, Some gi) line rest = mf_final v).
{ unfold mk_mod in HFIN. rewrite ECR in HFIN. exact HFIN. }
assert (A0' : getr regs1 10 = Z_to_bv 64 0) by (rewrite A0, ECR; reflexivity).
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mkr_seed0 v lyc Sc Wc regs1 memc mdc pos mcc MK_RRET CX CORE RA) as HS1.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0' eq_refl) as HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
clear HS1.
(* 0x86880: the `beqz` taken (a0 = 0); the run stops at MK_REFUSE 0x86c08 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_REFUSE.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (mkr_pres E _ regs1 v lyc pos None 0 [] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
assert (R27' : getr (ms_regs ms) 27 = w64 (line + 1)).
{ transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with MK_REFUSE by (unfold MK_REFUSE, AF_m_file; reflexivity) end.
change (mf_at B v Wc (ms_regs ms) (ms_mem ms) mdq MK_REFUSE).
apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest); [|exact HFIN'].
exact (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc)
  (conj LEN (conj NE (conj (LPk mcc (Some gi) line p rest LOOP) (conj (NPk _ NP) R27')))))))))).
Qed.

(* the Some arm: a0 = catA + 0x128 r, the `beqz` falls through; the trap 0x8688c not taken (cur 16-aligned); the
   checked memcpy of low ++ [0] into g->model; MK_CRET *)
Lemma mkr_some : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (vv : list Z) (r : nat),
MK_CRET_stmt B n ->
mk_base B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
~ In 0 vv -> Forall (fun b => 0 <= b < 256) vv ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
getr regs1 21 = w64 (Z.of_nat (length (h_fold vv 24))) ->
getr regs1 10 = w64 (seg_spec.cat_ptr SegInstB.catA (cat_row (h_fold vv 24))) ->
cat_row (h_fold vv 24) = Some r ->
mf_at B v Wc regs1 memc mdc MK_RRET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv r CRET BS HFIN Hn0 Hvr HZS R21 A0 ECR.
pose proof BS as (CX & LS & FRM & CORE & CELLS & RA & LEN & NE & LOOP & NP & R27).
(* the final model's entries, before low is named *)
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _). unfold mf_cur_ok in LCUR.
assert (Hgif : (gi < length (mc_seg (mf_final v)))%nat).
{ rewrite <- HFIN. pose proof (mkt_mf_fin_segs_mono (mk_mod mcc gi vv (line + 1), Some gi) line rest) as M.
  cbn [fst] in M. rewrite mkt_mk_model_segs in M. lia. }
pose proof (mkt_hfold_len vv) as HFL.
pose proof (mkt_hfold_nul vv Hn0) as Hnul.
pose proof (mkt_hfold_range vv Hvr) as Hrng.
set (low := h_fold vv 24) in *.
assert (HFIN' : mf_fin (m_upd mcc gi (ms_with_model low), Some gi) line rest = mf_final v).
{ unfold mk_mod in HFIN. fold low in HFIN. rewrite ECR in HFIN. exact HFIN. }
assert (Hlow24 : (length low < 24)%nat) by lia.
(* where things lie: the mconf block, the frame, the stack *)
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & HMC & HMA & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HMC as (bs & _ & (HL & HL32 & _)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hg : seg_spec.mseg_addr (mv_c v) gi = mv_c v + 256 * Z.of_nat gi)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hgi32 : (gi < 32)%nat) by lia.
unfold seg_spec.SEG_M_SIZE in Hbc2.
(* the seed at MK_RRET: cur = Some gi in 136(s1), low = FB + 32 in 144(s1), the next line's address in 152(s1) *)
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64) by (cbn [mf_cur_ptr]; rewrite Hg; lia).
assert (Hnp : 0 <= mf_next p rest < 2 ^ 64)
  by exact (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] MK_RRET
  true true [] false false [] false CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia)
  (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (mfE_extra regs1 v lyc pos (Some gi) (mf_next p rest) [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos (Some gi) (mf_next p rest) [] 2 ltac:(unfold A_TEXT; lia)) as E34.
pose proof (mfE_extra regs1 v lyc pos (Some gi) (mf_next p rest) [] 5 ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app mf_cur_ptr] in E32, E34, E37.
set (E := mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) in HS0, E32, E34, E37.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r0 : bv 5), Z.of_nat k = bv_unsigned r0 -> ew E k = getr regs1 r0)
  by (intros; apply mfE_reg; assumption).
clearbody E.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)).
{ rewrite (EE 2%nat 2%bv eq_refl), (proj1 (proj1 RA)). unfold w64. apply unsigned_lit_small. lia. }
(* the frame cells read-only: the run writes no byte *)
pose proof (st_ok_pi_region_nth E _ _ 1 (mf_r_slots true true []) HS0 eq_refl) as ROK0.
assert (ROK : region_ok SEGS E
  (ms_mem (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MK_RRET)) memc (seg_rom SEGS))))
  (set_window (mf_r_slots true true []) 0 0)).
{ apply region_ok_rewindow; [exact ROK0|]. intros o0 Ho0. lia. }
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0)
  HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity) ROK) as HS1.
clear HS0 ROK ROK0.
(* the facts: atom 37 = cur = c + 256 gi is 16-aligned (the trap 0x8688c), atom 10 = a0 = catA + 0x128 r lies in
   [catA, catA + 0x128 * 10] (the `beqz` 0x86880) *)
assert (Hg16 : seg_spec.mseg_addr (mv_c v) gi mod 16 = 0).
{ rewrite Hg. replace (mv_c v + 256 * Z.of_nat gi) with (mv_c v + 16 * Z.of_nat gi * 16) by ring.
  rewrite Z_mod_plus_full. exact Hc16. }
assert (F37 : afact_ok E 37 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E37, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hg16|]. lia. }
assert (Hrlt : (r < pin_spec.CAT_N)%nat) by exact (mkt_cat_row_lt _ _ ECR).
assert (U10 : bv_unsigned (ew E 10) = SegInstB.catA + pin_spec.CAT_ROW * Z.of_nat r).
{ rewrite (EE 10%nat 10%bv eq_refl), A0, ECR. cbn [seg_spec.cat_ptr]. unfold w64. apply unsigned_lit_small.
  unfold SegInstB.catA, pin_spec.CAT_ROW, pin_spec.CAT_N in *. lia. }
assert (F10 : afact_ok E 10 (mkAF SegInstB.catA (SegInstB.catA + 296 * 10) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold SegInstB.catA, pin_spec.CAT_ROW, pin_spec.CAT_N in *. lia. }
pose proof (st_ok_pi_add_fact E _ _ 10 _ (st_ok_pi_add_fact E _ _ 37 _ HS1 F37) F10) as HS.
clear HS1.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let s := eval vm_compute in ss in change ss with s in HS end.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* ===== 0x86880 .. 0x8689c and the jal: one token run, stopping at the checked memcpy entry ===== *)
paj_run_tok RUN HS HJ SHOK Bspan;
[ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil
| ].
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
(* every byte is kept by the run: all its windows are empty *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a).
{ intros a Ha.
  refine (kept_of_frame E _ (w_H Wc) memc memT (fun _ => False) HFr _ a Ha (fun x => x)).
  intros b wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]).
  destruct Hin. }
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) memT mdq CX CORE CELLS HJ K0)
  as (CORE_T & CELLS_T & NPK_T & LOOPK_T).
pose proof (LOOPK_T mcc (Some gi) line p rest LOOP) as LP_T.
pose proof (NPK_T _ NP) as NP_T.
assert (HZS_T : sa_zs (rdW Wc memT) (frame_addr lyc 1 pos + 32) (low ++ [0])).
{ intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite K0 by lia. exact (HZS i Hi). }
(* the registers at the call *)
assert (RAT : mf_regs_at B v lyc pos regsT).
{ destruct RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
  unfold mf_regs_at, mf_regs_ex.
  rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q22, Q23, Q24, Q25, E32.
  rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
    (EE 19%nat 19%bv eq_refl), (EE 22%nat 22%bv eq_refl), (EE 23%nat 23%bv eq_refl), (EE 24%nat 24%bv eq_refl),
    (EE 25%nat 25%bv eq_refl).
  repeat split; first [assumption | reflexivity]. }
assert (HspT : spZ regsT = mf_s1 (mv_sp v)) by (unfold spZ; rewrite Q2; exact U2).
assert (Hsp : spZ regsT = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by (rewrite HspT; lia).
assert (Po16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0).
{ destruct Ss1 as [E1 | E1]; rewrite E1.
  - replace (mv_sp v - 320 - mv_sp v) with ((-20) * 16) by lia. apply Z_mod_mult.
  - replace (mv_sp v - 336 - mv_sp v) with ((-21) * 16) by lia. apply Z_mod_mult. }
(* ===== the call's premises (aintrin_realizes OCpy through aj_intrin_atS) ===== *)
assert (P10 : getr regsT 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL)).
{ rewrite Q10, E37, unsigned_lit_small by lia. reflexivity. }
assert (P11 : getr regsT 11 = w64 (frame_addr lyc 1 pos + 32)).
{ rewrite Q11, E34, unsigned_lit_small by lia. reflexivity. }
assert (P12 : getr regsT 12 = w64 (Z.of_nat (length low) + 1)).
{ rewrite Q12, (EE 21%nat 21%bv eq_refl), R21. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (P3 : getr regsT 3 = w64 (as_gp B)) by exact (proj1 (proj2 (proj1 RAT))).
assert (P4 : getr regsT 4 = w64 (as_tp B)) by exact (proj1 (proj2 (proj2 (proj1 RAT)))).
assert (Pret : YK0s.ret_ok (getr regsT 1)).
{ rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
destruct (mkr_cpy_pre v lyc Sc Wc memT mdq pos mcc gi low regsT CX CORE_T LCUR Hgif Hlow24 HZS_T HspT)
  as (X1 & X2 & X3 & Xdest & Xwr & Xam & Xra & Xhv & Xsrc).
(* ===== 0x868a0: the checked memcpy ===== *)
eapply SRr_bind.
{ exact (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) (AMEMCPY fx)
    Wc regsT memT SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc mdq 0
    (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (frame_addr lyc 1 pos + 32) (Z.of_nat (length low) + 1)
    (mf_s1 (mv_sp v) - mv_sp v) (getr regsT 1)
    HJ P10 P11 P12 X1 X2 X3 Hsp Po16 ltac:(lia) ltac:(unfold ESTACK; rewrite HSTK; lia)
    P3 P4 eq_refl Pret Xdest Xwr Xam Xra Xhv Xsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A02 & HCPY & HK2 & HPRS & HSBM).
cbv beta iota in HCPY.
(* ===== the block after the call: g->model holds low and its NUL ===== *)
assert (HZ2 : sa_zs (rdW Wc mem2) (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL) (low ++ [0])).
{ intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite HCPY by lia. exact (HZS_T i Hi). }
pose proof CORE_T as (_ & _ & _ & _ & _ & _ & HMCT & _).
assert (MC2 : sa_mconf (rdW Wc mem2) (mv_c v) (m_upd mcc gi (mkt_set_model low))).
{ apply (mkt_sa_mconf_set_model (rdW Wc memT) (rdW Wc mem2) (mv_c v) mcc gi low HMCT LCUR Hlow24 Hnul Hrng);
    [|exact HZ2].
  intros a Ha Hna. unfold seg_spec.SEG_M_SIZE in Ha.
  apply HK2; [lia | intros Hq; apply Hna; lia | unfold ESTACK; lia]. }
(* ===== every cut fact at the return: the entry wrote its window below s1 and g->model, inside the block ===== *)
assert (Hwlo : mv_sp v - SegInstB.STK_m_file <= mf_s1 (mv_sp v) - ESTACK) by (rewrite HSTK; unfold ESTACK; lia).
assert (Hwhi : mf_s1 (mv_sp v) <= mf_s1 (mv_sp v) + 16) by lia.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v)) ->
  ~ (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL <= a <
     seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1)) ->
  rdW Wc mem2 a = rdW Wc memT a).
{ intros a Ha Hw He. apply HK2; [exact Ha | exact He | intros Hq; apply Hw; lia]. }
assert (HEb : forall a, seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL <= a <
    seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1) ->
  mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE).
{ intros a Ha. rewrite Hg in Ha. unfold seg_spec.MS_MODEL in Ha. unfold seg_spec.SEG_M_SIZE. lia. }
destruct (mf_keep_art B v lyc Sc Wc regsT memT mdq pos MF_LOW_ON mcc (Some gi) regs2 mem2 md2
  (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v))
  (fun a => seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL <= a <
            seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_MODEL + (Z.of_nat (length low) + 1))
  (m_upd mcc gi (mkt_set_model low)) CX CORE_T CELLS_T RAT HJ2 HP2 Hwlo Hwhi KW HEb MC2)
  as (CORE2 & CELLS2 & RA2 & NPK & LPK).
(* s4 = g and s11 = line + 1 are callee-saved *)
assert (R20' : getr regs2 20 = w64 (seg_spec.mseg_addr (mv_c v) gi)).
{ transitivity (getr regsT 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia))|].
  rewrite Q20, E37. reflexivity. }
assert (R27' : getr regs2 27 = w64 (line + 1)).
{ transitivity (getr regsT 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia))|].
  rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27. }
pose proof (mkr_loop_set v Wc mem2 mcc gi low (Some gi) line p rest (LPK _ _ _ _ _ LP_T)) as LOOP2.
pose proof (NPK _ NP_T) as NP2.
(* ===== 0x868a4: MK_CRET ===== *)
rewrite Q1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
  replace kk with MK_CRET by (unfold MK_CRET, AF_m_file; reflexivity) end.
change (mf_at B v Wc regs2 mem2 md2 MK_CRET).
exact (CRET v lyc Sc Wc regs2 mem2 md2 pos mcc gi line p rest low
  (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj LEN (conj NE (conj LOOP2 (conj NP2 R27'))))))))))
  Hlow24 Hnul Hrng HFIN' R20').
Qed.

(* MK_RRET 0x86880: the `beqz` on fuzz_catalogue_row's answer *)
Lemma mk_rret_ok : forall n, MK_REFUSE_stmt B n -> MK_CRET_stmt B n -> MK_RRET_stmt B n.
Proof.
intros n REF CRET. unfold MK_RRET_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv BS HFIN Hn0 Hvr HZS R21 A0.
destruct (cat_row (h_fold vv 24)) as [r|] eqn:ECR; rewrite <- ECR in A0.
- exact (mkr_some n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv r CRET BS HFIN Hn0 Hvr HZS R21 A0 ECR).
- exact (mkr_none n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest vv REF BS HFIN ECR A0).
Qed.

End e.
End f.
End d.

About mk_rret_ok.
Print Assumptions mk_rret_ok.
