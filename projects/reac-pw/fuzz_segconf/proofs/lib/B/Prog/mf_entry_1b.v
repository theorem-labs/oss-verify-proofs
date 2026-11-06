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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 595 of its 647 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the piece
   0x86270 -> 0x862ac of the segment S_MF_ENTRY, the second half of the half ENTRY -> 0x862ac.
   A walk lane of the image-B m_file-family owner's G2B (a sub-lane and its worker).
   proves no function (kind: segment lemma; the piece 0x86270 -> 0x862ac of m_file's image-B walk).

   THE CODE (the neutral listing of m_file in image B lines 78-93; the image-B m_file cut map section 5 / C.1):
     0x86270 lui a0,0x2; 0x86274 lui a1,0x2; 0x86278 add a0,s9,a0   (a0 = c + 0x2000)
     0x8627c sd a0,128(s1)                                          (128(s1) = c + seg_spec.MC_N)
     0x86280 addiw a0,a1,948; 0x86284 add a0,s9,a0                  (a0 = c + 0x23b4 = c + MC_READING)
     0x86288 bnez s6,0x86294                 THE LABEL BRANCH: s6 = the label pointer lp
     0x8628c auipc a1,0xfff9b; 0x86290 addi s6,a1,-492   (s6 = "reac-pw.conf", A_OBJ 13 = 0x210a0)
     0x86294 auipc a1,0xfff9b; 0x86298 addi a2,a1,-532   (a2 = "%s", A_OBJ 14 = 0x21080)
     0x8629c li a1,96; 0x862a0 sd a0,64(s1)                         (64(s1) = c + MC_READING)
     0x862a4 mv a3,s6; 0x862a8 jal 0x43af0 (the snprintf trampoline)
   No instrumented check and no UBSan trap branch lies in this range. The branch 0x86288 is decided by
   m_file_pre's `sa_ostr rd lp lab`: lp = 0 exactly when lab = None. Taken arm: lab = Some l, a3 = lp.
   Not-taken arm: lab = None, a3 = the literal "reac-pw.conf". In both arms the %s text is
   mf_entry_d.v's `mf_lab_text (mv_lab v)` and the pointer is `mfb_w v`.

   THE PROOF: one seed (m_file_sd.v mf_seed; cells := false, hnp := false, slx := [], cur := None) at
   MFE_P1 = AF_m_file + 0x130 with the frame-cell region [s1 + 16, s1 + 216) writable for the two stores;
   one token run to the branch, `psrr_branch_tok` at it, one token run per arm through the `jal`
   (mfb_run). At the trampoline's entry the premises of MFE_SNP_STEP are assembled: the journal and the
   Permutation from mf_core, the block's sa_addr / sa_tail there, and the %s argument's facts
   (mfb_label_call: the heap / live-frame / pinned-image case of m_file_pre's label, and the literal for
   lab = None through m_file_k.v's mf_lit_now_j). At the wrapper's return the cut MFE_MID of mf_entry_d.v
   is taken at the FP state fx1 the wrapper returns: mf_core by m_file_k.v's mf_keep with
   mf_entry_m.v's mfe_set_reading for the reading field, mf_loop by mf_loop_keep, the two frame cells
   64(s1) and 128(s1) by mf_slot_keep across the callee's window, the registers by mf_regs_ex_keep.

   Section hypotheses: the ambient fx / rc / SK, the listing instance PI, B and VOBJS. m_file_k.v's
   RELRO and SSP are NOT needed: of its lemmas only mf_rod_now* ask RELRO and mf_ssp_now* ask SSP, and
   this piece uses neither. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_entry_d mf_entry_1c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require mf_entry_m mf_entry_k.
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

(* a register whose symbolic value is atom n + k, or a literal (A_kign_h.v's ki_reg / ki_reg_lit) *)
Lemma mfb_reg : forall E ss (H : word -> bool) ms (r : bv 5) n k,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n k ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. intros E ss H ms r n k HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
Lemma mfb_reg_lit : forall E ss (H : word -> bool) ms (r : bv 5) z,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss H ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
(* an atom holding x, as a symbolic value *)
Lemma mfb_atom : forall E (n : nat) x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n x k Hn Hx. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hx. reflexivity. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS.

(* the %s argument of the call 0x862a8: the label when there is one, else the literal "reac-pw.conf" *)
Definition mfb_w (v : mfv) : Z :=
  match mv_lab v with Some _ => mv_lp v | None => SegInstB.seg_litA_fz S_base end.

(* the state at the snprintf trampoline's entry (the `jal` executed) *)
Definition mfb_call_st (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
(memc : word -> option byte) (pos : Z) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem3 md3 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216) ->
   rdW Wc mem3 a = rdW Wc memc a) /\
val_mem SEGS (mrestrict (w_H Wc) mem3) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos) /\
val_mem SEGS (mrestrict (w_H Wc) mem3) (mf_s1 (mv_sp v) + 64) 8 (mv_c v + seg_spec.MC_READING) /\
val_mem SEGS (mrestrict (w_H Wc) mem3) (mf_s1 (mv_sp v) + 128) 8 (mv_c v + seg_spec.MC_N) /\
getr regs3 1 = Z_to_bv 64 (BASE + MFE_RET_SNP) /\
getr regs3 10 = w64 (mv_c v + seg_spec.MC_READING) /\ getr regs3 11 = w64 96 /\
getr regs3 12 = w64 (SegInstB.seg_litA_fz F_s) /\ getr regs3 13 = w64 (mfb_w v) /\
mf_regs_ex B v lyc pos regs3 /\ getr regs3 25 = w64 (mv_c v) /\ getr regs3 26 = w64 (mv_t v).

(* a pinned image object is apart from c->reading: its bytes are image bytes, and no byte of the mconf
   block is an image byte (m_file_k.v mf_c_entry) *)
Lemma mfb_disj_img : forall v (w : Z) (txt : list Z),
  mf_cx B v -> 0 < w -> sa_img SEGS B w (Z.of_nat (length txt) + 1) ->
  sa_disj w (seg_spec.cstr_span w txt) (mv_c v + seg_spec.MC_READING) 96.
Proof.
intros v w txt CX Hw Himg.
destruct (mf_c_entry B v CX) as (b & m & Hbin & Hb1 & Hb2 & Hb4096 & Hbceil & Hbni).
unfold seg_spec.SEG_M_SIZE in Hb2.
assert (HW : in_img SEGS w) by exact (proj1 (Himg w ltac:(lia))).
unfold sa_disj, seg_spec.MC_READING.
destruct (Z_lt_le_dec w b) as [Hlt | Hge].
- assert (He : w + Z.of_nat (length txt) < b).
  { destruct (Z_lt_le_dec (w + Z.of_nat (length txt)) b) as [Hok | Hge2]; [exact Hok|].
    exfalso. exact (Hbni b ltac:(lia) (proj1 (Himg b ltac:(lia)))). }
  left. rewrite (mf_span_end w txt ltac:(lia)).
  pose proof (Z.mod_pos_bound (w + Z.of_nat (length txt)) 8 ltac:(lia)). lia.
- right.
  assert (Hout : b + req_size m <= w).
  { destruct (Z_lt_le_dec w (b + req_size m)) as [Hin | Hok];
      [exfalso; exact (Hbni w ltac:(lia) HW) | exact Hok]. }
  lia.
Qed.

(* the %s argument at the call state: its text, its bytes, its shadow, where it lies, and that it is
   apart from c->reading. The label's own facts come from m_file_pre at the entry and are carried to the
   call state by the journal: a heap byte by the walk's block-keep premise, a frame byte by the journal's
   frame clause, an image byte by m_file_k.v's mf_img_now_j. For lab = None the literal is
   m_file_k.v's mf_lit_now_j. *)
Lemma mfb_label_call : forall v lyc Sc (Wc : world SEGS) pos mem3 md3,
  mf_cx B v -> lyc = mv_ly v ->
  Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem3 md3 0 ->
  (forall b m a, In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
     rdW Wc mem3 a = rdW (mv_W v) (mv_mem v) a) ->
  0 < mfb_w v /\
  sa_str (rdW Wc mem3) (mfb_w v) (mf_lab_text (mv_lab v)) /\
  sa_addr (rdW Wc mem3) (mfb_w v) (Z.of_nat (length (mf_lab_text (mv_lab v))) + 1) /\
  Z.of_nat (length (mf_lab_text (mv_lab v))) <= 65535 /\
  (sa_heap B lyc Sc (mfb_w v) (Z.of_nat (length (mf_lab_text (mv_lab v))) + 1) \/
   sa_fframe lyc Sc (mfb_w v) (Z.of_nat (length (mf_lab_text (mv_lab v))) + 1) \/
   sa_img SEGS B (mfb_w v) (Z.of_nat (length (mf_lab_text (mv_lab v))) + 1)) /\
  sa_disj (mfb_w v) (seg_spec.cstr_span (mfb_w v) (mf_lab_text (mv_lab v)))
    (mv_c v + seg_spec.MC_READING) 96.
Proof.
intros v lyc Sc Wc pos mem3 md3 CX Ely HPerm HJ3 KB.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & Hlp64 & HMP & _).
pose proof HPRE as (HAR0 & _).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & Hfrs3 & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & HLAB).
subst lyc.
(* the FP lies in the mconf block, which is apart from the shadow band *)
assert (HFPsh : forall x, inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) x ->
  x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x HF. pose proof (mf_fp_in_block B v x CX HF) as Hc.
  destruct (mf_c_entry B v CX) as (b2 & m2 & Hb2in & Hb21 & Hb22 & _ & _ & _).
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ b2 m2 HAR0 Hb2in) as (_ & _ & _ & Bapp & _).
  unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, YG0f.ASAN_CEIL, seg_spec.SEG_M_SIZE in *.
  pose proof (@ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2. lia. }
unfold mfb_w, mf_lab_text.
destruct (mv_lab v) as [l|] eqn:Elab.
- (* the label *)
  destruct HOS as (Hlp0 & HSTRl).
  destruct HLAB as (Hlenl & Hloc & HADDRl & HDISJl).
  pose proof HADDRl as (A0 & A1 & A2 & A3 & A4).
  assert (Hlp : 0 < mv_lp v) by lia.
  pose proof HSTRl as ((HZSl & HNZl) & HTLl).
  destruct Hloc as [Hh | [Hf | Hi]].
  + (* a live heap block *)
    destruct Hh as (b & m & Hbin & Hb1 & Hb2).
    assert (Hbin3 : In (b, m) (ablocks B (mv_ly v) Sc))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbin).
    destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR0 Hbin) as (_ & Bk0 & Bk1 & Bk2 & Bk3 & _ & Bk4).
    pose proof (req_size_pos m (proj1 Bk4)) as [Hr1 Hr2].
    assert (HK : forall a, mv_lp v <= a < mv_lp v + Z.of_nat (length l) + 1 ->
      rdW Wc mem3 a = rdW (mv_W v) (mv_mem v) a) by (intros a Ha; apply (KB b m a Hbin); lia).
    split; [exact Hlp|]. split.
    { split; [split|].
      - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        rewrite HK by lia. exact (HZSl i ltac:(rewrite length_app; cbn [length]; lia)).
      - exact HNZl.
      - intros x Hx.
        pose proof (Z.mod_pos_bound (mv_lp v + Z.of_nat (length l)) 8 ltac:(lia)).
        exact (AR_block_word_vis SEGS B _ _ _ _ _ b m (mv_lp v + Z.of_nat (length l)) x HAR3 Hbin3
          ltac:(lia) ltac:(lia)). }
    split.
    { exact (mf_entry_k.mf_heap_addr SEGS B LAWS (mv_ly v) Sc Wc mem3 md3 (mv_lp v)
        (Z.of_nat (length l) + 1) HAR3 (ex_intro _ b (ex_intro _ m (conj Hbin3 (conj Hb1 Hb2))))
        ltac:(lia)). }
    split; [exact Hlenl|].
    split; [left; exact (ex_intro _ b (ex_intro _ m (conj Hbin3 (conj Hb1 Hb2))))|].
    exact HDISJl.
  + (* a live side-stack frame *)
    destruct Hf as (cid & pos0 & Hin0 & Hcid & Hf1 & Hf2).
    assert (Hin3 : In (cid, pos0) (frames Sc)) by (rewrite Hfrs3; right; exact Hin0).
    destruct (al_frames SEGS B LAWS _ _ _ _ _ cid pos0 HAR3 Hin3) as (Hal3 & _ & Hpres3 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FJ4 & _).
    assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z_mod_mult. }
    assert (Hfa8 : frame_addr (mv_ly v) cid pos0 mod 8 = 0).
    { pose proof (Z.div_mod (frame_addr (mv_ly v) cid pos0) 32 ltac:(lia)) as D32.
      rewrite Hal3, Z.add_0_r in D32.
      replace (frame_addr (mv_ly v) cid pos0) with ((4 * (frame_addr (mv_ly v) cid pos0 / 32)) * 8) by lia.
      apply Z_mod_mult. }
    assert (HKf : forall a, frame_addr (mv_ly v) cid pos0 <= a <
        frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid ->
      rdW Wc mem3 a = rdW (mv_W v) (mv_mem v) a).
    { intros a Ha. apply (FJ4 cid pos0 a Hin0).
      - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
      - intros HF. pose proof (mf_fp_in_block B v a CX HF) as Hc.
        destruct (mf_c_entry B v CX) as (b2 & m2 & Hb2in & Hb21 & Hb22 & _ & _ & _).
        pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b2 m2 cid pos0 HAR0 Hb2in Hin0) as Hsep.
        unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
        pose proof (req_size_pos m2 ltac:(destruct (al_blocks SEGS B LAWS _ _ _ _ _ b2 m2 HAR0 Hb2in)
          as (_ & _ & _ & _ & _ & _ & Hm2); lia)) as [Hq1 Hq2].
        unfold seg_spec.SEG_M_SIZE in Hc, Hb22. lia. }
    assert (Hfe : mv_lp v + Z.of_nat (length l) - (mv_lp v + Z.of_nat (length l)) mod 8 + 8 <=
      frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid).
    { pose proof (Z.div_mod (mv_lp v + Z.of_nat (length l)) 8 ltac:(lia)) as De.
      pose proof (Z.mod_pos_bound (mv_lp v + Z.of_nat (length l)) 8 ltac:(lia)) as Me.
      pose proof (Z.div_mod (frame_addr (mv_ly v) cid pos0) 8 ltac:(lia)) as Df.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Db.
      pose proof (Z.div_mod (mv_lp v + Z.of_nat (length l)) 8 ltac:(lia)).
      assert (Hq : (mv_lp v + Z.of_nat (length l)) / 8 <
        (frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid) / 8).
      { apply Z.div_lt_upper_bound; [lia|].
        pose proof (Z.div_mod (frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid) 8 ltac:(lia)).
        assert (Hm0 : (frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid) mod 8 = 0)
          by (rewrite Zplus_mod, Hfa8, Hb8; reflexivity).
        lia. }
      pose proof (Z.div_mod (frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid) 8 ltac:(lia)).
      assert (Hm0 : (frame_addr (mv_ly v) cid pos0 + fs_frame_bytes cid) mod 8 = 0)
        by (rewrite Zplus_mod, Hfa8, Hb8; reflexivity).
      lia. }
    split; [lia|]. split.
    { split; [split|].
      - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        rewrite HKf by lia. exact (HZSl i ltac:(rewrite length_app; cbn [length]; lia)).
      - exact HNZl.
      - intros x Hx.
        apply (aview_some_of_apresent SEGS). apply (proj1 (Hpres3 x ltac:(lia))). }
    split.
    { split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
      - exact (range_addressable_entry_frame SEGS B LAWS SegInstB.STK_m_file (mv_sp v)
          (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v)
          [(1, pos)] (mv_ly v) Sc Wc mem3 md3 0 cid pos0 (mv_lp v) (Z.of_nat (length l) + 1)
          HJ3 Hin0 Hcid Hf1 Hf2 Hfa8 HFPsh HAR0 A3).
      - intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS (mv_ly v) Sc Wc mem3 md3 cid pos0
          (mv_lp v) (Z.of_nat (length l) + 1) HAR3 Hin3 Hf1 Hf2 ltac:(lia)). }
    split; [exact Hlenl|].
    split; [right; left; exact (ex_intro _ cid (ex_intro _ pos0 (conj Hin3 (conj Hcid (conj Hf1 Hf2)))))|].
    exact HDISJl.
  + (* a pinned image object *)
    destruct Hi as (Himg & Hpin & Hptail).
    split; [lia|]. split.
    { split; [split|].
      - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        destruct (Himg (mv_lp v + Z.of_nat i) ltac:(lia)) as (I1 & I2 & I3).
        rewrite (mf_img_now_j B v (mv_ly v) Sc Wc mem3 md3 pos _ CX HJ3 I1 I2 I3).
        exact (HZSl i ltac:(rewrite length_app; cbn [length]; lia)).
      - exact HNZl.
      - exact (Hptail (mv_ly v) Sc Wc mem3 md3 HAR3). }
    split; [exact (Hpin (mv_ly v) Sc Wc mem3 md3 HAR3)|].
    split; [exact Hlenl|].
    split; [right; right; exact Himg|].
    exact HDISJl.
- (* no label: the literal "reac-pw.conf" *)
  destruct (mf_lit_now_j B v (mv_ly v) Sc Wc mem3 md3 pos S_base CX HJ3 ltac:(right; left; reflexivity))
    as (L0 & LSTR & LPIN & LROM & LIMG).
  split; [exact L0|]. split; [exact LSTR|].
  split; [exact (LPIN (mv_ly v) Sc Wc mem3 md3 HAR3)|].
  split; [vm_compute; discriminate|].
  split; [right; right; exact LIMG|].
  exact (mfb_disj_img v _ S_base CX L0 LIMG).
Qed.

(* the line loop's facts read only the model's three counters and n_kept, which mfe_c0 keeps *)
Lemma mfb_loop_mc : forall v (Wc : world SEGS) memc mcc mcc' cur line p rest,
  mc_kept mcc' = mc_kept mcc -> mc_refused mcc' = mc_refused mcc -> mc_overflow mcc' = mc_overflow mcc ->
  mf_cur_ok mcc' cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_loop v Wc memc mcc' cur line p rest.
Proof.
intros v Wc memc mcc mcc' cur line p rest E1 E2 E3 EC LP.
unfold mf_loop in LP |- *.
destruct LP as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
rewrite E1, E2, E3.
exact (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 (conj EC (conj L7 (conj L8 (conj L9 (conj L10 L11)))))))))).
Qed.

(* 0x86270 to the snprintf trampoline's entry: the two stores, the label branch, the arguments, the `jal` *)
Lemma mfb_run : forall v lyc Sc Wc regs1 memc mdc pos,
  mf_cx B v ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mv_mc v) ->
  mf_regs_ex B v lyc pos regs1 ->
  getr regs1 22 = w64 (mv_lp v) -> getr regs1 25 = w64 (mv_c v) -> getr regs1 26 = w64 (mv_t v) ->
  (forall regs3 mem3 md3, mfb_call_st v lyc Sc Wc memc pos regs3 mem3 md3 ->
    SRr SEGS Wc (mkCfg (mkst regs3 (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) mem3
      (seg_rom SEGS)) md3) (MF_POST B v)) ->
  mf_at B v Wc regs1 memc mdc MFE_P1.
Proof.
intros v lyc Sc Wc regs1 memc mdc pos CX CORE RA R22 R25 R26 KC.
unfold mf_at.
pose proof (mf_regs_base_of_ex B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & Hlp64 & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HMA as (MA1 & MA2 & _).
unfold seg_spec.SEG_M_SIZE in MA2.
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HARc Hfin) as (F1 & F2 & F3 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1b : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320)
  by (destruct Ss1 as [E1|E1]; rewrite E1; lia).
pose proof (@ASAN_CEIL_range rc) as ((CRlo & CRhi) & CRal). unfold YG0f.ASAN_CEIL in CRlo, CRhi, CRal.
(* the seed at 0x86270: the frame cells writable for the two stores; no cells and no np stated *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mv_mc v) None 0 [] MFE_P1
  false false [] false false [] false CX CORE RB ltac:(intros H; discriminate H)
  ltac:(unfold mf_cur_ptr; lia) ltac:(intros H; discriminate H) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
set (E := mfE regs1 v lyc pos None 0 []) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_nil).
assert (E2 : ew E 2 = Z_to_bv 64 (mf_s1 (mv_sp v)))
  by (unfold E; rewrite (mfE_reg regs1 v lyc pos None 0 [] 2 2%bv eq_refl), R2; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 (mv_lp v))
  by (unfold E; rewrite (mfE_reg regs1 v lyc pos None 0 [] 22 22%bv eq_refl), R22; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 (mv_c v))
  by (unfold E; rewrite (mfE_reg regs1 v lyc pos None 0 [] 25 25%bv eq_refl), R25; reflexivity).
pose proof (mfE_extra regs1 v lyc pos None 0 [] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (mfE_extra regs1 v lyc pos None 0 [] 2 ltac:(unfold A_TEXT; lia)) as E34.
cbn [Nat.add nth mf_extra map app] in E32, E34. fold E in E32, E34.
assert (E254 : ew E (A_OBJ 13) = Z_to_bv 64 (SegInstB.seg_litA_fz S_base)).
{ unfold E. rewrite (mfE_img regs1 v lyc pos None 0 [] (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite <- (mf_lit_obj VOBJS S_base 13 ltac:(right; left; reflexivity)). reflexivity. }
assert (E255 : ew E (A_OBJ 14) = Z_to_bv 64 (SegInstB.seg_litA_fz F_s)).
{ unfold E. rewrite (mfE_img regs1 v lyc pos None 0 [] (A_OBJ 14) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite <- (mf_lit_obj VOBJS F_s 14 ltac:(left; reflexivity)). reflexivity. }
assert (HFs : 0 <= SegInstB.seg_litA_fz F_s < 2 ^ 64)
  by (rewrite (mf_lit_obj VOBJS F_s 14 ltac:(left; reflexivity)); apply pa_val_range).
assert (HSb : 0 <= SegInstB.seg_litA_fz S_base < 2 ^ 64)
  by (rewrite (mf_lit_obj VOBJS S_base 13 ltac:(right; left; reflexivity)); apply pa_val_range).
(* 0x86270 .. 0x86284: the two `lui`, the store 128(s1), a0 = c + 0x23b4 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack_off with (d := mf_s1 (mv_sp v) - mv_sp v);
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mB) => rename mB into ms1 end.
assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216) ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hna.
  apply (kept_of_frame E _ (w_H Wc) memc
    (ms_mem ms1) (fun x => mf_s1 (mv_sp v) + 16 <= x < mf_s1 (mv_sp v) + 216) HFr); [| exact Ha | exact Hna].
  intros bb wlo whi x Hin Hr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
  destruct Hin. }
clear HF HFr HG.
(* 0x86288, the label branch: lp = 0 exactly when the label is NULL (m_file_pre's sa_ostr) *)
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
{ (* taken: lp <> 0, so the label is Some l and a3 = lp *)
  assert (Hne : mv_lp v <> 0).
  { rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite (U_atom E 22 (mv_lp v) E22 ltac:(lia)) in Hc.
    assert (HZ : U E (SLit 0) = 0) by reflexivity. rewrite HZ in Hc. exact Hc. }
  assert (Hw : mfb_w v = mv_lp v).
  { unfold mfb_w. destruct (mv_lab v) as [l|]; [reflexivity|]. exfalso. exact (Hne HOS). }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack_off with (d := mf_s1 (mv_sp v) - mv_sp v);
      [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
    do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mB) => rename mB into ms3 end.
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216) ->
    rdW Wc (ms_mem ms3) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha Hna.
    apply (kept_of_frame E _ (w_H Wc) (ms_mem ms1) (ms_mem ms3)
      (fun x => mf_s1 (mv_sp v) + 16 <= x < mf_s1 (mv_sp v) + 216) HFr); [| exact Ha | exact Hna].
    intros bb wlo whi x Hin Hr. cbv beta. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
    destruct Hin. }
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 ->
      getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
      by (intros r n0 k0 Hr; exact (mfb_reg E ssx (w_H Wc) ms3 r n0 k0 HS Hr));
    assert (QL : forall (r : bv 5) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms3) r = Z_to_bv 64 z)
      by (intros r z Hr; exact (mfb_reg_lit E ssx (w_H Wc) ms3 r z HS Hr));
    pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) ms3) 1 _ HS eq_refl) as HR1
  end.
  assert (QA : forall (r : bv 5) n0 x k0, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0) ->
    getr (ms_regs ms3) r = Z_to_bv 64 (x + k0))
    by (intros r n0 x k0 Hn0 Hx Hr; rewrite Hr, Hn0, unsigned_lit_small by exact Hx; reflexivity).
  assert (QS : forall (r : bv 5) n0, ew E n0 = getr regs1 r ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) -> getr (ms_regs ms3) r = getr regs1 r)
    by (intros r n0 Hn0 Hr; rewrite Hr, Z.add_0_r, Hn0; apply Z_to_bv_bv_unsigned).
  pose proof (QR 1%bv 240%nat MFE_RET_SNP eq_refl) as Q1.
  rewrite (img_env_codeptr E HEI MFE_RET_SNP) in Q1.
  pose proof (QA 2%bv 2%nat _ 0 E2 ltac:(lia) (QR 2%bv 2%nat 0 eq_refl)) as Q2.
  pose proof (QS 3%bv 3%nat (mfE_reg regs1 v lyc pos None 0 [] 3 3%bv eq_refl) (QR 3%bv 3%nat 0 eq_refl)) as Q3.
  pose proof (QS 4%bv 4%nat (mfE_reg regs1 v lyc pos None 0 [] 4 4%bv eq_refl) (QR 4%bv 4%nat 0 eq_refl)) as Q4.
  pose proof (QS 8%bv 8%nat (mfE_reg regs1 v lyc pos None 0 [] 8 8%bv eq_refl) (QR 8%bv 8%nat 0 eq_refl)) as Q8.
  pose proof (QA 9%bv 2%nat _ 0 E2 ltac:(lia) (QR 9%bv 2%nat 0 eq_refl)) as Q9.
  pose proof (QA 10%bv 25%nat _ 9140 E25 ltac:(lia) (QR 10%bv 25%nat 9140 eq_refl)) as Q10.
  pose proof (QL 11%bv 96 eq_refl) as Q11.
  pose proof (QA 12%bv (A_OBJ 14) _ 0 E255 HFs (QR 12%bv (A_OBJ 14) 0 eq_refl)) as Q12.
  pose proof (QA 13%bv 22%nat _ 0 E22 ltac:(lia) (QR 13%bv 22%nat 0 eq_refl)) as Q13.
  pose proof (QA 18%bv 32%nat _ 0 E32 ltac:(unfold SHADOW_OFF; lia) (QR 18%bv 32%nat 0 eq_refl)) as Q18.
  pose proof (QS 23%bv 23%nat (mfE_reg regs1 v lyc pos None 0 [] 23 23%bv eq_refl) (QR 23%bv 23%nat 0 eq_refl)) as Q23.
  pose proof (QS 24%bv 24%nat (mfE_reg regs1 v lyc pos None 0 [] 24 24%bv eq_refl) (QR 24%bv 24%nat 0 eq_refl)) as Q24.
  pose proof (QS 25%bv 25%nat (mfE_reg regs1 v lyc pos None 0 [] 25 25%bv eq_refl) (QR 25%bv 25%nat 0 eq_refl)) as Q25.
  pose proof (QS 26%bv 26%nat (mfE_reg regs1 v lyc pos None 0 [] 26 26%bv eq_refl) (QR 26%bv 26%nat 0 eq_refl)) as Q26.
  rewrite !Z.add_0_r in Q2, Q9, Q12, Q13, Q18.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 120 8%N (SOff 34 0)
    (frame_addr lyc 1 pos) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 34 (frame_addr lyc 1 pos) 0 E34 ltac:(lia)); f_equal; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V120_3.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 64 8%N (SOff 25 9140)
    (mv_c v + seg_spec.MC_READING) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 25 (mv_c v) 9140 E25 ltac:(lia)); f_equal;
          unfold seg_spec.MC_READING; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_READING; lia)
    ltac:(cbn; lia)) as V64_3.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 128 8%N (SOff 25 8192)
    (mv_c v + seg_spec.MC_N) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 25 (mv_c v) 8192 E25 ltac:(lia)); f_equal;
          unfold seg_spec.MC_N; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N; lia)
    ltac:(cbn; lia)) as V128_3.
  pmkst HS.
  apply KC. unfold mfb_call_st.
  split; [exact HJ|].
  split; [intros a Ha Hna; rewrite (KP2 a Ha Hna); exact (KP1 a Ha Hna)|].
  split; [exact V120_3|]. split; [exact V64_3|]. split; [exact V128_3|].
  split; [exact Q1|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
  split; [rewrite Q13, Hw; reflexivity|].
  split.
  { apply (mf_regs_ex_of B v lyc pos regs1 (ms_regs ms3) RA);
      [ rewrite Q2, R2; reflexivity | exact Q3 | exact Q4 | exact Q8
      | rewrite Q9, R9; reflexivity | rewrite Q18, R18; reflexivity | exact Q23 | exact Q24 ]. }
  split; [rewrite Q25; exact R25 | rewrite Q26; exact R26]. }
{ (* not taken: lp = 0, so the label is None and a3 = the literal "reac-pw.conf" *)
  assert (Hz : mv_lp v = 0).
  { rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite (U_atom E 22 (mv_lp v) E22 ltac:(lia)) in Hc.
    assert (HZ : U E (SLit 0) = 0) by reflexivity. rewrite HZ in Hc. exact Hc. }
  assert (Hw : mfb_w v = SegInstB.seg_litA_fz S_base).
  { unfold mfb_w. destruct (mv_lab v) as [l|]; [|reflexivity].
    exfalso. exact (proj1 HOS Hz). }
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack_off with (d := mf_s1 (mv_sp v) - mv_sp v);
      [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite HSTK; lia | cbn [YP09.r_whi]; lia |].
    do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mB) => rename mB into ms3 end.
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 16 <= a < mf_s1 (mv_sp v) + 216) ->
    rdW Wc (ms_mem ms3) a = rdW Wc (ms_mem ms1) a).
  { intros a Ha Hna.
    apply (kept_of_frame E _ (w_H Wc) (ms_mem ms1) (ms_mem ms3)
      (fun x => mf_s1 (mv_sp v) + 16 <= x < mf_s1 (mv_sp v) + 216) HFr); [| exact Ha | exact Hna].
    intros bb wlo whi x Hin Hr. cbv beta. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite U2 in Hr; lia | lia] |]).
    destruct Hin. }
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 ->
      getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
      by (intros r n0 k0 Hr; exact (mfb_reg E ssx (w_H Wc) ms3 r n0 k0 HS Hr));
    assert (QL : forall (r : bv 5) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms3) r = Z_to_bv 64 z)
      by (intros r z Hr; exact (mfb_reg_lit E ssx (w_H Wc) ms3 r z HS Hr));
    pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) ms3) 1 _ HS eq_refl) as HR1
  end.
  assert (QA : forall (r : bv 5) n0 x k0, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0) ->
    getr (ms_regs ms3) r = Z_to_bv 64 (x + k0))
    by (intros r n0 x k0 Hn0 Hx Hr; rewrite Hr, Hn0, unsigned_lit_small by exact Hx; reflexivity).
  assert (QS : forall (r : bv 5) n0, ew E n0 = getr regs1 r ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) -> getr (ms_regs ms3) r = getr regs1 r)
    by (intros r n0 Hn0 Hr; rewrite Hr, Z.add_0_r, Hn0; apply Z_to_bv_bv_unsigned).
  pose proof (QR 1%bv 240%nat MFE_RET_SNP eq_refl) as Q1.
  rewrite (img_env_codeptr E HEI MFE_RET_SNP) in Q1.
  pose proof (QA 2%bv 2%nat _ 0 E2 ltac:(lia) (QR 2%bv 2%nat 0 eq_refl)) as Q2.
  pose proof (QS 3%bv 3%nat (mfE_reg regs1 v lyc pos None 0 [] 3 3%bv eq_refl) (QR 3%bv 3%nat 0 eq_refl)) as Q3.
  pose proof (QS 4%bv 4%nat (mfE_reg regs1 v lyc pos None 0 [] 4 4%bv eq_refl) (QR 4%bv 4%nat 0 eq_refl)) as Q4.
  pose proof (QS 8%bv 8%nat (mfE_reg regs1 v lyc pos None 0 [] 8 8%bv eq_refl) (QR 8%bv 8%nat 0 eq_refl)) as Q8.
  pose proof (QA 9%bv 2%nat _ 0 E2 ltac:(lia) (QR 9%bv 2%nat 0 eq_refl)) as Q9.
  pose proof (QA 10%bv 25%nat _ 9140 E25 ltac:(lia) (QR 10%bv 25%nat 9140 eq_refl)) as Q10.
  pose proof (QL 11%bv 96 eq_refl) as Q11.
  pose proof (QA 12%bv (A_OBJ 14) _ 0 E255 HFs (QR 12%bv (A_OBJ 14) 0 eq_refl)) as Q12.
  pose proof (QA 13%bv (A_OBJ 13) _ 0 E254 HSb (QR 13%bv (A_OBJ 13) 0 eq_refl)) as Q13.
  pose proof (QA 18%bv 32%nat _ 0 E32 ltac:(unfold SHADOW_OFF; lia) (QR 18%bv 32%nat 0 eq_refl)) as Q18.
  pose proof (QS 23%bv 23%nat (mfE_reg regs1 v lyc pos None 0 [] 23 23%bv eq_refl) (QR 23%bv 23%nat 0 eq_refl)) as Q23.
  pose proof (QS 24%bv 24%nat (mfE_reg regs1 v lyc pos None 0 [] 24 24%bv eq_refl) (QR 24%bv 24%nat 0 eq_refl)) as Q24.
  pose proof (QS 25%bv 25%nat (mfE_reg regs1 v lyc pos None 0 [] 25 25%bv eq_refl) (QR 25%bv 25%nat 0 eq_refl)) as Q25.
  pose proof (QS 26%bv 26%nat (mfE_reg regs1 v lyc pos None 0 [] 26 26%bv eq_refl) (QR 26%bv 26%nat 0 eq_refl)) as Q26.
  rewrite !Z.add_0_r in Q2, Q9, Q12, Q13, Q18.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 120 8%N (SOff 34 0)
    (frame_addr lyc 1 pos) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 34 (frame_addr lyc 1 pos) 0 E34 ltac:(lia)); f_equal; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as V120_3.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 64 8%N (SOff 25 9140)
    (mv_c v + seg_spec.MC_READING) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 25 (mv_c v) 9140 E25 ltac:(lia)); f_equal;
          unfold seg_spec.MC_READING; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_READING; lia)
    ltac:(cbn; lia)) as V64_3.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 16 216 16 216 128 8%N (SOff 25 8192)
    (mv_c v + seg_spec.MC_N) HR1 U2
    ltac:(cbn [In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity])
    ltac:(rewrite (mfb_atom E 25 (mv_c v) 8192 E25 ltac:(lia)); f_equal;
          unfold seg_spec.MC_N; lia)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N; lia)
    ltac:(cbn; lia)) as V128_3.
  pmkst HS.
  apply KC. unfold mfb_call_st.
  split; [exact HJ|].
  split; [intros a Ha Hna; rewrite (KP2 a Ha Hna); exact (KP1 a Ha Hna)|].
  split; [exact V120_3|]. split; [exact V64_3|]. split; [exact V128_3|].
  split; [exact Q1|]. split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
  split; [rewrite Q13, Hw; reflexivity|].
  split.
  { apply (mf_regs_ex_of B v lyc pos regs1 (ms_regs ms3) RA);
      [ rewrite Q2, R2; reflexivity | exact Q3 | exact Q4 | exact Q8
      | rewrite Q9, R9; reflexivity | rewrite Q18, R18; reflexivity | exact Q23 | exact Q24 ]. }
  split; [rewrite Q25; exact R25 | rewrite Q26; exact R26]. }
Qed.

(* ======================= the piece: 0x86270 -> 0x862ac ======================= *)
Lemma mfe_p1_at : MFE_SNP_STEP B -> MFE_MID_F B -> MFE_P1_stmt B.
Proof.
intros SNP MID.
unfold MFE_P1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos CX FRM LS CORE LOOP KB RA R22 R25 R26.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & Hlp64 & HMP & _).
pose proof HPRE as (HAR0 & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HMA as (MA1 & MA2 & _). unfold seg_spec.SEG_M_SIZE in MA2.
pose proof LS as (Ely & fS & ESc).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HARc Hfin) as (F1 & F2 & F3 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1b : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320)
  by (destruct Ss1 as [E1|E1]; rewrite E1; lia).
pose proof (@ASAN_CEIL_range rc) as ((CRlo & CRhi) & CRal). unfold YG0f.ASAN_CEIL in CRlo, CRhi, CRal.
assert (HSNPK : RtPFSeg.SEG_SNP_K = 8192) by (vm_compute; reflexivity).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mv_mc v) CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
unfold seg_spec.SEG_M_SIZE in Hbc2.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HARc Hbc) as (_ & Bk4096 & Bkceil & Bkapp & _ & _ & Bkn).
pose proof (req_size_pos mbc (proj1 Bkn)) as [Hr1 Hr2].
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
(* the run to the call *)
apply (mfb_run v lyc Sc Wc regs1 memc mdc pos CX CORE RA R22 R25 R26).
intros regs3 mem3 md3 (HJ3 & K3 & V120_3 & V64_3 & V128_3 & Q1 & Q10 & Q11 & Q12 & Q13 & RA3 & Q25 & Q26).
pose proof HJ3 as (HAR3 & _).
pose proof RA3 as (R2' & R3' & R4' & R8' & R9' & R18' & R23' & R24').
(* the block's bytes still hold the entry's values at the call state *)
assert (KB3 : forall b m a, In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
  rdW Wc mem3 a = rdW (mv_W v) (mv_mem v) a).
{ intros b m a Hbin Ha.
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR0 Hbin) as (_ & Q4096 & Qceil & _ & _ & _ & Qm).
  pose proof (req_size_pos m (proj1 Qm)) as [Qr1 Qr2].
  rewrite (K3 a ltac:(lia) ltac:(lia)). exact (KB b m a Hbin Ha). }
(* the block at the call state *)
assert (HSA3 : sa_addr (rdW Wc mem3) (mv_c v) seg_spec.SEG_M_SIZE).
{ pose proof HMA as (A1 & A2 & A3 & _ & _).
  unfold seg_spec.SEG_M_SIZE. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia. }
assert (HST3 : sa_tail (rdW Wc mem3) (mv_c v + seg_spec.SEG_M_SIZE - 1)).
{ unfold seg_spec.SEG_M_SIZE. intros x Hx.
  pose proof (Z.mod_pos_bound (mv_c v + 9236 - 1) 8 ltac:(lia)).
  rewrite (K3 x ltac:(lia) ltac:(lia)). exact (HMT x ltac:(unfold seg_spec.SEG_M_SIZE; lia)). }
(* the %s argument *)
destruct (mfb_label_call v lyc Sc Wc pos mem3 md3 CX Ely HPerm HJ3 KB3)
  as (HW0 & HSTRw & HADDRw & HLENw & HLOCw & HDISJw).
pose proof HSTRw as ((HZSw & HNZw) & HTLw).
destruct (mf_entry_m.mf_reading_bytes (mf_lab_text (mv_lab v)) HNZw) as (_ & Hrl & Hr0).
(* the call *)
refine (SNP v lyc Sc Wc regs3 mem3 md3 pos (mfb_w v) (mf_lab_text (mv_lab v)) CX LS FRM HJ3 HPerm
  HSA3 HST3 HW0 HSTRw HADDRw HLENw HLOCw HDISJw R2' R3' R4' Q1 Q10 Q11 Q12 Q13 _).
intros fx1 regs2 mem2 md2 Hfx HJ2 HP2 HZR HK2.
(* the bytes the run and the call wrote *)
set (RWc := fun a => (mf_s1 (mv_sp v) - RtPFSeg.SEG_SNP_K <= a < mf_s1 (mv_sp v) + 216) \/
  (mv_c v + seg_spec.MC_READING <= a <
     mv_c v + seg_spec.MC_READING + Z.of_nat (length (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))])) + 1)).
set (RWcall := fun a => (mf_s1 (mv_sp v) - RtPFSeg.SEG_SNP_K <= a < mf_s1 (mv_sp v)) \/
  (mv_c v + seg_spec.MC_READING <= a <
     mv_c v + seg_spec.MC_READING + Z.of_nat (length (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))])) + 1)).
assert (KCALL : forall a, 0 <= a < 2 ^ 64 -> ~ RWcall a -> rdW Wc mem2 a = rdW Wc mem3 a).
{ intros a Ha Hn. apply (HK2 a Ha); intros Hx; apply Hn; [left; exact Hx | right; exact Hx]. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ RWc a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn.
  rewrite (KCALL a Ha ltac:(intros [Hx|Hx]; apply Hn; [left; lia | right; exact Hx])).
  apply (K3 a Ha). intros Hx. apply Hn. left. rewrite HSNPK. lia. }
assert (RWok : forall a, RWc a -> mf_rw v lyc pos a).
{ intros a [Ha | Ha]; unfold mf_rw.
  - destruct (Z_lt_le_dec a (mf_s1 (mv_sp v) + 16)) as [Hlo | Hhi].
    + left. rewrite HSTK. rewrite HSNPK in Ha. lia.
    + do 5 right. lia.
  - right; left. unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *. lia. }
assert (RWS : mf_rws v RWcall).
{ intros a Ha Hin. exfalso. destruct Ha as [Ha | Ha].
  - rewrite HSNPK in Ha. lia.
  - unfold seg_spec.MC_READING in Ha. lia. }
(* low.i's shadow bytes are outside the written set *)
assert (HSH : forall i, 4 <= i < 12 -> ~ RWc (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i)).
{ intros i Hi [Hx | Hx].
  - rewrite HSNPK in Hx. unfold SHADOW_OFF in Hx. lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, YG0f.ASAN_CEIL, SHADOW_OFF, seg_spec.MC_READING in *. lia. }
assert (VSH2 : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi.
  apply (mf_val_keep Wc Wc memc mem2 RWc (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1%nat MF_LOW_OFF K2);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
    | intros k Hk; change (Z.of_nat 1) with 1 in Hk;
      replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i + k)
        with (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) by lia; exact (HSH i Hi)
    | exact (VSH i Hi)]. }
assert (V120_2 : val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 120) 8 (frame_addr lyc 1 pos))
  by exact (mf_slot_keep B v Wc Wc mem3 mem2 RWcall 120 _ CX KCALL RWS ltac:(lia) ltac:(lia) V120_3).
(* the block holds mfe_c0 v: the reading field is snprintf's text, every other byte is the entry's *)
assert (MC2 : sa_mconf (rdW Wc mem2) (mv_c v) (mfe_c0 v)).
{ unfold mfe_c0, mfe_reading.
  pose proof HMC as (bs & Hbs & Henc).
  pose proof (proj1 Henc) as Hl. unfold seg_spec.SEG_M_SIZE in Hl.
  set (o := Z.to_nat seg_spec.MC_READING).
  assert (Ho : Z.of_nat o = seg_spec.MC_READING)
    by (unfold o; apply Z2Nat.id; unfold seg_spec.MC_READING; lia).
  apply (mf_entry_m.mfe_set_reading (rdW Wc memc) (rdW Wc mem2) (mv_c v) (mv_mc v)
    (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))]) HMC).
  - intros a Ha Hna. apply K2; [unfold seg_spec.SEG_M_SIZE in Ha; lia|].
    intros [Hx | Hx]; [unfold seg_spec.SEG_M_SIZE in Ha; lia
      | apply Hna; unfold seg_spec.MC_READING in *; lia].
  - exact Hrl.
  - exact Hr0.
  - intros i Hi. apply HZR. rewrite length_app. cbn [length]. lia.
  - intros i Hi.
    destruct (lt_dec i (S (length (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))])))) as [Hlt | Hge].
    + rewrite (HZR i ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
    + rewrite K2; [| unfold seg_spec.MC_READING; lia |].
      * replace (mv_c v + seg_spec.MC_READING + Z.of_nat i) with (mv_c v + Z.of_nat (o + i))
          by (rewrite Nat2Z.inj_add, Ho; lia).
        rewrite (Hbs (o + i)%nat ltac:(unfold seg_spec.MC_READING in Ho; lia)). discriminate.
      * intros [Hx | Hx]; unfold seg_spec.MC_READING in Hx; lia.
  - intros i Hi z Hz. exact (mf_entry_m.mf_aview_byte SEGS (w_H Wc) mem2 _ z Hz). }
(* the cut's pieces at the return *)
assert (CORE2 : mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_OFF (mfe_c0 v))
  by exact (mf_keep B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mv_mc v) Sc Wc mem2 md2 RWc MF_LOW_OFF
    (mfe_c0 v) CX CORE HJ2 (Permutation_refl _) K2 RWok VSH2 V120_2 MC2).
assert (LOOP2 : mf_loop v Wc mem2 (mv_mc v) None 0 (mv_t v) (mv_s v))
  by exact (mf_loop_keep B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mv_mc v) Sc Wc mem2 md2 RWc
    (mv_mc v) None 0 (mv_t v) (mv_s v) CX CORE HJ2 (Permutation_refl _) K2 RWok LOOP).
assert (LOOP2' : mf_loop v Wc mem2 (mfe_c0 v) None 0 (mv_t v) (mv_s v))
  by exact (mfb_loop_mc v Wc mem2 (mv_mc v) (mfe_c0 v) None 0 (mv_t v) (mv_s v)
    eq_refl eq_refl eq_refl I LOOP2).
assert (S64 : mf_slot v mem2 Wc 64 (mv_c v + seg_spec.MC_READING))
  by exact (mf_slot_keep B v Wc Wc mem3 mem2 RWcall 64 _ CX KCALL RWS ltac:(lia) ltac:(lia) V64_3).
assert (S128 : mf_slot v mem2 Wc 128 (mv_c v + seg_spec.MC_N))
  by exact (mf_slot_keep B v Wc Wc mem3 mem2 RWcall 128 _ CX KCALL RWS ltac:(lia) ltac:(lia) V128_3).
assert (RA2 : mf_regs_ex B v lyc pos regs2) by exact (mf_regs_ex_keep B v lyc pos regs3 regs2 RA3 HP2).
assert (P25 : getr regs2 25 = getr regs3 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs3 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
assert (G25 : getr regs2 25 = w64 (mv_c v)) by (rewrite P25; exact Q25).
assert (G26 : getr regs2 26 = w64 (mv_t v)) by (rewrite P26; exact Q26).
(* the cut at the FP state the wrapper returns *)
exact (MID fx1 v lyc Sc Wc regs2 mem2 md2 pos CX (fxrel_frm0 fx fx1 FRM Hfx)
  (conj LS (conj CORE2 (conj LOOP2' (conj S64 (conj S128 (conj RA2 (conj G25 G26)))))))).
Qed.

About mfe_p1_at.
Print Assumptions mfe_p1_at.

End e.
End f.
End d.

About mfe_p1_at.
Print Assumptions mfe_p1_at.
