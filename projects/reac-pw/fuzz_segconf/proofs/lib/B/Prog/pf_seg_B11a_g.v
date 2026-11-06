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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 534 of its 586 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B11b_k.v, with its module paths and module names changed; 433 of its 580 lines of code are new or changed and 439 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B11a of
   reac_segconf_parse_file's walk, the geometry of a cut state and what a step of the segment carries over.
   The B11a segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment kit lib/A/Prog/pf_a5_k.v
   (commit ed36e7310ee1, the image-A A5 segment lane: a5_G / a5_geo / a5_Wrx / the a5_keep lemmas / a5_move),
   re-derived for image B's frame and for the bytes segment B11a writes:
   - b11_geo: the numbers every cut state has (image B: s1 = (sp0 - 0x160) & -32, 0x87e38 / 0x87e78; the class-5
     frame F of the journal, 2048 bytes, 32-aligned, an application range off the image; its shadow SH);
   - b11_Wr: the bytes a B11a step may write -- the callees' windows below s1 (reac_box_catalogue_by_token's
     STK_reac_box_catalogue_by_token and snprintf's 2 * ESTACK, both inside parse_file's window), model low
     (F + 0x2e0, 24 bytes: the fold's stores 0x88728 and the NUL 0x889d0), model low's three shadow cells
     (SH + 0x5c .. 0x5e: 0x886d4-0x886dc), and the three model windows of c->seg[gi] ([cur + 0x24, cur + 0xa0):
     the two snprintf calls 0x88a04 / 0x88a3c and the `sw` 0x88a24);
   - the keep lemmas: every object a cut names outside those bytes reads the same after the step;
   - b11_move / b11_cx_move: pf_base and b11_cx after a step, from the journal the step returns.
   No slot of parse_file's own frame [s1, sp0) is written by the segment, so PF_SL, slot 0x70, slot 0xc0 and the
   saved registers are kept whole. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot
  SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B11a_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= arithmetic ======================= *)
Lemma b11_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma b11_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.
Lemma b11_mod32_down : forall x, 0 <= x -> (x - x mod 32) mod 32 = 0 /\ x - 32 < x - x mod 32 <= x.
Proof.
intros x Hx. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M. pose proof (Z.div_mod x 32 ltac:(lia)) as D.
split; [|lia]. replace (x - x mod 32) with ((x / 32) * 32) by lia. apply Z_mod_mult.
Qed.
Lemma b11_rdword_keep : forall (rd rd' : reader) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd' a = rdword rd a.
Proof. exact rdword_ext. Qed.
(* a register of a list *)
Lemma b11_rg_get : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Lemma b11_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Lemma b11_rg_incl : forall rX L1 L2, incl L2 L1 -> pf_rg rX L1 -> pf_rg rX L2.
Proof. intros rX L1 L2 Hi H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin. exact (H rv (Hi rv Hin)). Qed.
Lemma b11_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Lemma b11_slot_get : forall rd b L off x, pf_sl rd b L -> In (off, x) L -> rdword rd (b + off) = Some x.
Proof. intros rd b L off x H Hin. exact (proj1 (Forall_forall _ _) H (off, x) Hin). Qed.

(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's 256 cells *)
Lemma b11_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma b11_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b11_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* the model window of entry gi < 32 lies inside the table c->seg (c + 0x2c80) *)
Lemma b11_cw_in : forall c (gi : nat), (gi < 32)%nat ->
  c <= seg_spec.rseg_addr c gi + seg_spec.RS_MODEL /\
  seg_spec.rseg_addr c gi + seg_spec.RS_MODEL + 124 <= c + seg_spec.RC_N.
Proof. intros c gi H. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_MODEL, seg_spec.RC_N. lia. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the registers of pf_fi (sp, gp, tp, s0, s1, s4) and of PF_RL / PF_RM are callee-saved *)
Definition b11_FI (B : asyms) (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Lemma b11_FI_cs : forall B v, Forall (fun rv => acallee_saved (fst rv)) (b11_FI B v).
Proof. intros B v. unfold b11_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b11_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof. intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b11_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof. intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b11_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* the numbers every cut state has (b11_geo): the entry sp0 and s1, the class-5 frame F (2048 bytes, 32-aligned, an
   application range off the image [0x10000, kImgEnd)), the block c (a live heap block of 16616 bytes, apart from the
   frame, off the image) and the text's read span apart from c (reader_pre's sa_disj) *)
Definition b11_G (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)) /\
  p_c v mod 16 = 0 /\ 4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= p_c v) /\
  zdisjoint (p_c v, seg_spec.SEG_C_SIZE) (pf_F v pos, 2048) /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  off_img (p_c v) seg_spec.SEG_C_SIZE.

(* the bytes a B11a step may write: the callees' windows below s1, model low, model low's shadow cells (shw), and
   the three model windows of the entry cw points at (cw = Some (cur + 0x24), 124 bytes up to cur + 0xa0) *)
Definition b11_Wr (v : pfv) (pos : Z) (shw : bool) (cw : option Z) (a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (pf_F v pos + PF_O_L146 <= a < pf_F v pos + PF_O_L146 + 24) \/
  (shw = true /\ pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) \/
  (match cw with Some w => w <= a < w + 124 | None => False end).
(* the model window of entry gi *)
Definition b11_cw (v : pfv) (gi : nat) : option Z := Some (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL).
(* the window is inside c's table, or there is none *)
Definition b11_cw_ok (v : pfv) (cw : option Z) : Prop :=
  match cw with None => True | Some w => p_c v <= w /\ w + 124 <= p_c v + seg_spec.RC_N end.
Lemma b11_cw_ok_gi : forall v gi, (gi < 32)%nat -> b11_cw_ok v (b11_cw v gi).
Proof. intros v gi H. unfold b11_cw_ok, b11_cw. exact (b11_cw_in (p_c v) gi H). Qed.
(* rd' agrees with rd off the writes, and every byte visible in rd is visible in rd' *)
Definition b11_kept (v : pfv) (pos : Z) (shw : bool) (cw : option Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b11_Wr v pos shw cw a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma b11_kept_mono : forall v pos shw cw rd rd', b11_kept v pos false None rd rd' -> b11_kept v pos shw cw rd rd'.
Proof.
intros v pos shw cw rd rd' [K V]. split; [|exact V]. intros a Ha Hn. apply K; [exact Ha|].
intros [W | [W | [(W & _) | W]]]; apply Hn; unfold b11_Wr; [left | right; left | discriminate W | destruct W].
exact W. exact W.
Qed.
Lemma b11_kept_trans : forall v pos shw cw rd1 rd2 rd3,
  b11_kept v pos shw cw rd1 rd2 -> b11_kept v pos shw cw rd2 rd3 -> b11_kept v pos shw cw rd1 rd3.
Proof.
intros v pos shw cw rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.

Section x. Context {fx : YK11.FPState}.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b11_fi_regs : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_rg rX (b11_FI B v).
Proof. intros v pos lyc Sc Wc rX memc mdc sc (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma b11_geo : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  b11_G v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & HOBJ & _).
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & Hfb & Hsh).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ, Hfb. change (2048 / 8) with 256 in Hsh.
change (fs_frame_bytes 5 / 8) with 256 in Hsh.
rewrite EF in H32, Happ, Hf0, Hfc, Hfb, Hsh.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b11_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b11_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
(* the block c and the text *)
destruct HOBJ as (_ & _ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & Hb4 & Hbcl & Hbapp & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hbc Hin) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite EF in Hdj. change (fs_frame_bytes 5) with 2048 in Hdj.
destruct HPF as (HRP & _).
destruct HRP as (_ & Hc16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hbapp.
split.
{ unfold b11_G, pf_s1.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
  split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
  split.
  { intros a Ha Hf. rewrite <- EF in Hf.
    destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
      ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
    apply Hz. unfold in_zr. pose proof (pa_img_cover lyc Sc mdc (proj1 (proj2 HAR))) as [IC1 IC2].
    unfold kImgEnd in *. lia. }
  split; [exact Hc16|]. unfold seg_spec.SEG_C_SIZE in *.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold zdisjoint; cbn [fst snd]; lia|]. split; [exact HDJ|].
  pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hbc) as Hoff. unfold off_img in *. lia. }
split; [exact Hin|]. split; [exact EF|]. split; [exact Hfrs|]. split; [exact HAR|]. split; [exact Hly|].
split; [intros a Ha; exact (proj1 (Hfb a Ha))|]. intros i Hi. exact (proj1 (Hsh i Hi)).
Qed.
Lemma b11_SHb : forall v pos, b11_G v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b11_G v pos.
(* an application byte below the allocator's ceiling, outside the class-5 frame; outside the model window cw *)
Definition b11_out0 (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Definition b11_out (cw : option Z) (x : Z) : Prop :=
  b11_out0 x /\ match cw with Some w => ~ (w <= x < w + 124) | None => True end.
Lemma b11_out0_shadow : forall shw cw x, b11_out0 x -> b11_cw_ok v cw ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b11_Wr v pos shw cw (SHADOW_OFF + x / 8).
Proof.
intros shw cw x (Hx1 & Hx2 & Hx3) Hcw.
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _ & C16 & C4 & Cc & Capp & _).
destruct (b11_SHb v pos G) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (AC1 & _). pose proof STK_values as (_ & _ & _ & SPF & _).
assert (F8' : pf_F v pos mod 8 = 0) by (rewrite F8; rewrite Z.mul_comm; apply Z_mod_mult).
pose proof (b11_granule (pf_F v pos) x F8' Hx3 ltac:(lia)) as Gr.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
assert (Hq : x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
split; [unfold SHADOW_OFF; lia|].
unfold b11_Wr, PF_O_L146. rewrite SPF, ESH. unfold SHADOW_OFF in *.
intros [W | [W | [(_ & W) | W]]].
- lia.
- destruct F4; lia.
- lia.
- destruct cw as [w|]; [cbv beta iota in W; cbv beta iota delta [b11_cw_ok] in Hcw | destruct W].
  unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. destruct Capp; lia.
Qed.
Lemma b11_out_nw : forall shw cw x, b11_out cw x -> b11_cw_ok v cw ->
  0 <= x < 2 ^ 64 /\ ~ b11_Wr v pos shw cw x /\
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b11_Wr v pos shw cw (SHADOW_OFF + x / 8).
Proof.
intros shw cw x (H0 & Hw) Hcw. destruct (b11_out0_shadow shw cw x H0 Hcw) as (S1' & S2').
destruct H0 as (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos G) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (AC1 & _). pose proof STK_values as (_ & _ & _ & SPF & _).
split; [lia|]. split; [|exact (conj S1' S2')].
unfold b11_Wr, PF_O_L146. rewrite SPF. intros [W | [W | [(_ & W) | W]]].
- lia.
- lia.
- rewrite ESH in W. unfold SHADOW_OFF in W. destruct Hx2; lia.
- destruct cw as [w|]; [exact (Hw W) | destruct W].
Qed.
Lemma b11_out_img : forall cw x, 0x10000 <= x < kImgEnd -> b11_cw_ok v cw -> b11_out cw x.
Proof.
intros cw x Hx Hcw. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & _ & C4 & _ & _ & _ & _ & Coff).
pose proof asan_consts as (AC1 & _).
unfold kImgEnd in *. split; [split; [lia|]; split; [lia|]; exact (I1 x Hx)|].
destruct cw as [w|]; [|exact I]. cbv beta iota delta [b11_cw_ok] in Hcw. cbv beta iota.
unfold off_img, seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma b11_out_inimg : forall cw x, in_img SEGS x -> b11_cw_ok v cw -> b11_out cw x.
Proof. intros cw x Hx Hcw. apply b11_out_img; [exact (pa_img_range x Hx) | exact Hcw]. Qed.
(* the real stack at and above s1 (the saved registers, the slots) is not written *)
Lemma b11_stack_nw : forall shw cw a, b11_cw_ok v cw -> pf_s1 v <= a < 2 ^ 64 -> ~ b11_Wr v pos shw cw a.
Proof.
intros shw cw a Hcw Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _ & C16 & C4 & Cc & _).
destruct (b11_SHb v pos G) as (_ & SH1 & SH2 & _). pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
unfold b11_Wr, PF_O_L146. intros [W | [W | [(_ & W) | W]]]; try lia.
destruct cw as [w|]; [cbv beta iota in W; cbv beta iota delta [b11_cw_ok] in Hcw | destruct W]. unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* a frame byte off model low is not written *)
Lemma b11_frame_nw : forall shw cw a, b11_cw_ok v cw -> pf_F v pos <= a < pf_F v pos + 2048 ->
  ~ (pf_F v pos + PF_O_L146 <= a < pf_F v pos + PF_O_L146 + 24) -> 0 <= a < 2 ^ 64 /\ ~ b11_Wr v pos shw cw a.
Proof.
intros shw cw a Hcw Ha Hl. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _ & C16 & C4 & Cc & Capp & Cdj & _).
destruct (b11_SHb v pos G) as (ESH & SH1 & SH2 & _). pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
split; [lia|]. unfold b11_Wr. rewrite SPF. intros [W | [W | [(_ & W) | W]]].
- lia.
- exact (Hl W).
- rewrite ESH in W. unfold SHADOW_OFF in W. destruct F4; lia.
- destruct cw as [w|]; [cbv beta iota in W; cbv beta iota delta [b11_cw_ok] in Hcw | destruct W]. unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *.
  unfold zdisjoint in Cdj. cbn [fst snd] in Cdj. lia.
Qed.

Section r.
Variables (shw : bool) (cw : option Z) (rd rd' : reader).
Hypothesis Hcw : b11_cw_ok v cw.
Hypothesis K : b11_kept v pos shw cw rd rd'.
Lemma b11_k_byte : forall x, b11_out cw x -> rd' x = rd x.
Proof. intros x Hx. destruct (b11_out_nw shw cw x Hx Hcw) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma b11_k_shadow : forall x, b11_out0 x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (b11_out0_shadow shw cw x Hx Hcw) as (H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b11_k_zs : forall p l, (forall i, (i < length l)%nat -> b11_out cw (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b11_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b11_k_bytes : forall p l, (forall i, (i < length l)%nat -> b11_out cw (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b11_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b11_k_rdword : forall a, (forall k, 0 <= k < 8 -> b11_out cw (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (b11_k_byte _ (Ho k Hk)). Qed.
Lemma b11_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b11_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b11_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b11_out cw x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as ((He & _) & _).
pose proof asan_consts as (AC1 & _).
split; [split; [|exact Hn] | exact (b11_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b11_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b11_k_addr : forall q n, (forall x, q <= x < q + n -> b11_out0 x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b11_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b11_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b11_k_ra : forall q n, (forall x, q <= x < q + n -> b11_out0 x) ->
  range_addressable rd SHADOW_OFF q n -> range_addressable rd' SHADOW_OFF q n.
Proof.
intros q n Ho H3 x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b11_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b11_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b11_k_str a s); [|exact Hs]. intros x Hx. apply b11_out_inimg; [exact (proj1 (Hi x ltac:(lia))) | exact Hcw].
Qed.
Lemma b11_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b11_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b11_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b11_out_inimg; [|exact Hcw]. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b11_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b11_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b11_out_inimg; [exists sg; split; [exact Hsg | exact Hr] | exact Hcw].
- apply b11_out_img; [unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *; lia | exact Hcw].
Qed.
Lemma b11_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b11_out cw (a + k))
  by (intros a Ha k Hk; apply b11_out_img; [lia | exact Hcw]).
split; [rewrite (b11_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b11_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a range inside a live heap block of the cut's state is an application byte below the ceiling off the frame *)
Lemma b11_out0_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> b11_out0 v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HAR Hin EF Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold b11_out0. lia.
Qed.
Lemma b11_out0_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n -> b11_out0 v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (b11_out0_heap v pos lyc Sc Wc memc mdc b m x HAR Hin EF Hb). lia.
Qed.

(* ---------- the cut's objects, carried across a step ---------- *)
Lemma b11_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc shw cw rd rd',
  b11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc shw cw rd rd' HG HAR Hin EF Hcw K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
pose proof HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C16 & C4 & Cc & Capp & Cdj & HDJ & Coff).
assert (Ht0 : forall x, p_t v <= x < p_t v + pf_len v -> b11_out0 v pos x)
  by (intros x Hx; exact (b11_out0_sa_heap v pos lyc Sc Wc memc mdc _ _ x HAR Hin EF H3 Hx)).
assert (Hc0 : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> b11_out0 v pos x)
  by (intros x Hx; exact (b11_out0_sa_heap v pos lyc Sc Wc memc mdc _ _ x HAR Hin EF H5 Hx)).
assert (Hspan : (Z.of_nat (length (p_s v)) + 1 <= seg_spec.cstr_span (p_t v) (p_s v))).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
assert (Ht : forall x, p_t v <= x < p_t v + (Z.of_nat (length (p_s v)) + 1) -> b11_out v pos cw x).
{ intros x Hx. split; [apply Ht0; unfold pf_len; lia|].
  destruct cw as [w|]; [|exact I]. cbv beta iota delta [b11_cw_ok] in Hcw. cbv beta iota. unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *.
  unfold sa_disj, seg_spec.SEG_C_SIZE in HDJ. lia. }
split; [exact (b11_k_str v pos HG shw cw rd rd' Hcw K _ _ Ht H1)|].
split; [exact (b11_k_addr v pos HG shw cw rd rd' Hcw K _ _ Ht0 H2)|]. split; [exact H3|].
split; [exact (b11_k_addr v pos HG shw cw rd rd' Hcw K _ _ Hc0 H4)|]. split; [exact H5|].
split; [exact (b11_k_cat v pos HG shw cw rd rd' Hcw K _ H6)|].
split; [intros x Hx; exact (b11_k_lit v pos HG shw cw rd rd' Hcw K _ _ (H7 x Hx))|].
split; [exact (b11_k_rod v pos HG shw cw rd rd' Hcw K H8) | exact (b11_k_ssp v pos HG shw cw rd rd' Hcw K H9)].
Qed.
Lemma b11_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc shw rd rd' cf,
  b11_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  b11_kept v pos shw None rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc shw rd rd' cf HG HAR Hin EF K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (b11_k_bytes v pos HG shw None rd rd' I K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _]. split; [|exact I].
apply (b11_out0_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HAR Hin EF Hh). lia.
Qed.
Lemma b11_keep_saved : forall v pos shw cw rd rd' regs, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos shw cw rd rd' regs HG Hcw K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (proj1 K); [lia|]. apply (b11_stack_nw v pos HG shw cw); [exact Hcw | lia].
Qed.
Lemma b11_keep_flag : forall v pos shw cw rd rd', b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos shw cw rd rd' HG Hcw K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (b11_frame_nw v pos HG shw cw (pf_F v pos + 2048 - 8 + k) Hcw ltac:(lia)
  ltac:(unfold PF_O_L146; lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma b11_keep_slot : forall v pos shw cw rd rd' off w, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  0 <= off <= 0xd8 -> rdword rd (pf_s1 v + off) = Some w -> rdword rd' (pf_s1 v + off) = Some w.
Proof.
intros v pos shw cw rd rd' off w HG Hcw K Ho H. rewrite (rdword_ext rd rd'); [exact H|].
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (proj1 K); [lia|]. apply (b11_stack_nw v pos HG shw cw); [exact Hcw | lia].
Qed.
Lemma b11_keep_sl : forall v pos shw cw rd rd' L, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  (forall ov, In ov L -> 0 <= fst ov <= 0xd8) ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos shw cw rd rd' L HG Hcw K HL H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
exact (b11_keep_slot v pos shw cw rd rd' (fst ov) (snd ov) HG Hcw K (HL ov Hov) (H ov Hov)).
Qed.
Lemma b11_keep_nm : forall v pos shw cw rd rd' nm, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos shw cw rd rd' nm HG Hcw K (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
destruct (b11_frame_nw v pos HG shw cw (pf_F v pos + 0x20 + Z.of_nat i) Hcw ltac:(lia)
  ltac:(unfold PF_O_L146; lia)) as (H0 & H1).
rewrite (proj1 K _ H0 H1). exact (Hb i ltac:(lia)).
Qed.
(* a C string in buf (val) *)
Lemma b11_keep_buf_str : forall v pos shw cw rd rd' p s, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos shw cw rd rd' ->
  pf_inb (pf_F v pos + PF_O_BUF) p s -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros v pos shw cw rd rd' p s HG Hcw K Hb [[Hz Hn] Ht]. unfold pf_inb, PF_O_BUF in Hb.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
assert (KB : forall x, pf_F v pos + 0x40 <= x < pf_F v pos + 0x240 -> rd' x = rd x).
{ intros x Hx. destruct (b11_frame_nw v pos HG shw cw x Hcw ltac:(lia) ltac:(unfold PF_O_L146; lia)) as (H0 & H1).
  exact (proj1 K _ H0 H1). }
split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KB by lia. exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  assert (F8 : pf_F v pos mod 8 = 0).
  { apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
  assert (Hx2 : x < pf_F v pos + 0x240).
  { pose proof (Z.div_mod (p + Z.of_nat (length s)) 8 ltac:(lia)).
    pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). lia. }
  rewrite KB by lia. exact (Ht x Hx).
Qed.

End x.

Section y. Context {fx : YK11.FPState}.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* pf_base after a step that kept every byte off b11_Wr (and every visible byte visible), with the journal it
   returned at the same layout, the frame state changed at most (set_fs), the live blocks permuted, at the FP state
   fx of this section (the one the step returns, whose rounding mode is 0) *)
Lemma b11_move : forall (fx0 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' shw cw,
  @pf_base fx0 rc SK PI B v pos lyc Sc Wc rX memc mdc sc ->
  b11_cw_ok v cw ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  b11_kept v pos shw cw (rdW Wc memc) (rdW Wc' memc') ->
  pf_rg rX' (b11_FI B v) -> sa_frm0 ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros fx0 v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' shw cw HB Hcw HJ' [f HSf] HPerm K HRG HFRM HFSH.
destruct (@b11_geo fx0 B v pos lyc Sc Wc rX memc mdc sc HB) as (HG & Hin & EF & Hfrs & HAR & Hly & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & _ & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply b11_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (b11_keep_saved v pos shw cw _ _ _ HG Hcw K HSV)|].
  split; [exact (b11_keep_flag v pos shw cw _ _ HG Hcw K HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [|exact HRG].
  unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
  exact (b11_keep_slot v pos shw cw _ _ 0xc8 _ HG Hcw K ltac:(lia) HC8). }
split.
{ pose proof (b11_keep_obj B v pos lyc Sc Wc memc mdc shw cw _ _ HG HAR Hin EF Hcw K HOBJ) as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (b11_keep_sl v pos shw cw _ _ _ HG Hcw K (b11_PF_SL_offs v pos) HSL) | exact HFSH].
Qed.

(* the frame shadow after a step that wrote no shadow cell *)
Lemma b11_keep_fsh : forall v pos cw rd rd' sc, b11_G v pos -> b11_cw_ok v cw -> b11_kept v pos false cw rd rd' ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos cw rd rd' sc HG Hcw K H i Hi.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _ & C16 & C4 & Cc & Capp & _).
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & _). pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
rewrite (proj1 K); [exact (H i Hi) | lia |].
unfold b11_Wr. rewrite SPF, ESH. unfold SHADOW_OFF, PF_O_L146 in *. intros [W | [W | [(W & _) | W]]].
- lia.
- destruct F4; lia.
- discriminate W.
- destruct cw as [w|]; [cbv beta iota in W; cbv beta iota delta [b11_cw_ok] in Hcw | destruct W]. unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. destruct Capp; lia.
Qed.

(* b11_cx after a step that wrote at most below s1 and model low (no shadow cell, no byte of c) *)
Lemma b11_cx_move : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc' Wc' rX' memc' mdc',
  b11_cx B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  b11_kept v pos false None (rdW Wc memc) (rdW Wc' memc') ->
  pf_rg rX' (b11_FI B v) ->
  b11_cx B n v pos lyc Sc' Wc' rX' memc' mdc' cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val Sc' Wc' rX' memc' mdc' HCX HJ' HSf HPerm K HRG.
destruct HCX as (HB & HMID & HST & HSTR & HINB & HSL70).
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_L146 HB) as (HG & Hin & EF & Hfrs & HAR & Hly & _).
pose proof HB as (_ & (_ & _ & _ & _ & _ & _ & HFRM & _) & HOBJ & _ & HFSH).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split.
{ apply (b11_move fx v pos lyc Sc Wc rX memc mdc PF_SC_L146 Sc' Wc' rX' memc' mdc' PF_SC_L146 false None HB I HJ' HSf HPerm
    K HRG HFRM).
  exact (b11_keep_fsh v pos None _ _ _ HG I K HFSH). }
split; [exact HMID|].
split.
{ destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
  split; [exact (b11_keep_rconf B v pos lyc Sc Wc memc mdc false _ _ _ HG HAR Hin EF K HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (b11_keep_nm v pos false None _ _ nm HG I K HNM)|]. split; [exact HCNT|].
  exact (b11_keep_slot v pos false None _ _ 0xc0 _ HG I K ltac:(lia) HC0). }
split; [exact (b11_keep_buf_str v pos false None _ _ vp val HG I K HINB HSTR)|].
split; [exact HINB|].
apply (b11_keep_sl v pos false None _ _ _ HG I K); [|exact HSL70].
intros ov [<- | []]. cbn [fst]. lia.
Qed.

(* the frame's bytes in scope are addressable (buf: cells 8 .. 0x47; model low: cells 0x5c .. 0x5e) *)
Lemma b11_ra_frame : forall v pos lyc Sc Wc rX memc mdc sc lo len, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  lo mod 8 = 0 -> len mod 8 = 0 -> 0 <= lo -> 0 <= len -> lo + len <= 1152 ->
  (forall i, lo / 8 <= i < (lo + len) / 8 -> pf_shb sc i = 0) ->
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + lo) len.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc lo len HB Hlo Hlen H0 H0' H1 Hz.
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HG & _).
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HB as (_ & _ & _ & _ & HFSH).
assert (Elo : lo = 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
assert (Elen : len = 8 * (len / 8)) by (pose proof (Z.div_mod len 8 ltac:(lia)); lia).
assert (EA : (pf_F v pos + lo) / 8 = pf_F v pos / 8 + lo / 8).
{ replace (pf_F v pos + lo) with ((pf_F v pos / 8 + lo / 8) * 8) by lia. apply Z.div_mul. lia. }
assert (Hl8 : (lo + len) / 8 = lo / 8 + len / 8).
{ replace (lo + len) with ((lo / 8 + len / 8) * 8) by lia. apply Z.div_mul. lia. }
apply zero_shadow_range.
- replace (pf_F v pos + lo) with ((pf_F v pos / 8 + lo / 8) * 8) by lia. apply Z_mod_mult.
- exact Hlen.
- intros i Hi. unfold shadow_of_addr. rewrite EA.
  replace (SHADOW_OFF + (pf_F v pos / 8 + lo / 8) + i) with (pf_SH v pos + (lo / 8 + i)) by (rewrite ESH; lia).
  rewrite (HFSH (lo / 8 + i)) by lia. rewrite (Hz (lo / 8 + i)) by lia. reflexivity.
Qed.

End y.
End f.
End d.
