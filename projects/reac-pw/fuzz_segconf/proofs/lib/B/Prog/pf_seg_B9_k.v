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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 607 of its 660 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the transport kit of segment B9 of
   reac_segconf_parse_file (the key line, KEY 0x883f8 .. KREF 0x889a0, 131 instructions).
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: helper facts of segment B9, image B).
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_a5_k.v (commit e326ef3cdba9, the
   image-A A5 segment lane; a5_ renamed b9_), for B9's write set and image B's cut parts (lib/B/Prog/pf_pieces.v):
   - the geometry of a cut state (b9_G, b9_geo): image B's realigned base s1 = (sp0 - 0x160) & -32 (0x87e38 /
     0x87e78 / 0x87e7c), so sp0 - 368 <= s1 <= sp0 - 352 (A: 0x140, 352 .. 320), STK_reac_segconf_parse_file = 12832
     (SegInstB.STK_values);
   - the bytes a B9 step may write (b9_Wrx): the callees' windows below s1 (strchr, trim, strlen, strcasecmp,
     refuse: each runs at sp <= s1), slot 0x70 (val, `sd s3,112(s1)` 0x88574, the flag sl), and buf (the store
     `sb zero,0(s8)` of the '=' at 0x8841c, the unquote store 0x8855c, and trim's / refuse's writes inside buf).
     B9 writes no shadow cell (its five checks B#9, B#10, B#11, B#13, B#14 only read buf's shadow) and no other
     slot of s1 (the slot-write list of pf_pieces.v: the loop writes 0x60, 0x68, 0x70 and 0xc0; B9's code writes
     only 0x70);
   - what a step that keeps every other byte carries over (the b9_keep lemmas), over image B's pf_st (5
     conjuncts, cur in slot 0xc0), PF_SL (23 slots at 0x00 .. 0x58 and 0x78 .. 0xd8), pf_fi's slot 0xc8 (c) and
     any list of slots off [s1 + 0x70, s1 + 0x78) (b9_keep_slots), slot 0x70 under the narrower write set
     (b9_keep_slot70);
   - the same for a step that may also write a region [cb, cb + cn) of application bytes below the ceiling,
     outside the image range and the frame (b9_RG): the b9_keep_*_r lemmas. The plain b9_keep lemmas are their
     cn = 0 case;
   - the rebuild of pf_base after a step (b9_move, b9_move0): image B's pf_fi has 10 conjuncts (pf_tf and
     pf_sl [(0xc8, c)] besides A's 8), and its register list has SHADOW_OFF in x20 = s4 (A: x22). After refuse
     (KREF -> TAIL) pf_base is rebuilt from refuse's journal by pf_seg_B9_s11.v's own lemmas: refuse's journal
     does not keep every byte off b9_Wrx (its class-0 frame and shadow, errno, owned statics change);
   - the read-only view (b9_rom), the frame chain at a call (b9_chain), the text (b9_text), the register list
     helpers (b9_rg_*, b9_RL_cs, b9_RM_cs, b9_FI, b9_FI_cs, b9_fi_regs).
   Left out of the A file (A5-only): a5_ln, a5_post, a5_mid, a5_post_step, a5_fill_fsh, a5_shb_buf, a5_shb_in,
   a5_keep_ln, a5_keep_slot (A's slot 0xb0); a5_heap_tail_out is not needed (a string's tail granule is only
   asked to be visible, which the visibility premise gives). Kept besides the list B9's stretches use: b9_move0
   (b9_move with no Section hypothesis, a5_move0's), b9_keep_obj0 / b9_keep_ssp / b9_keep_rod0 / b9_low_out.
   SECTION HYPOTHESES: VRO (the listing's read-only range, B's SegObj.seg_val_relro) and SSPX (the stack-protector
   cells at every AR state, as lib/B/Prog/reac_segconf_parse.v states it).
   POSITIONAL NAMES: none of an A table. The slot offsets are image B's (pf_pieces.v PF_SL, pf_st, pf_fi), the frame
   offsets PF_O_* B's (.rodata 0x11b81, the same as A's), the shadow cells pf_shb B's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the numbers of a cut state, and the bytes a B9 step writes ======================= *)
Lemma b9_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
Lemma b9_set_fs2 : forall f g s, set_fs f (set_fs g s) = set_fs f s.
Proof. intros f g s. destruct s. reflexivity. Qed.
Lemma b9_mod32_down : forall x, 0 <= x -> (x - x mod 32) mod 32 = 0 /\ x - 32 < x - x mod 32 <= x.
Proof.
intros x Hx. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M. pose proof (Z.div_mod x 32 ltac:(lia)) as D.
split; [|lia]. replace (x - x mod 32) with ((x / 32) * 32) by lia. apply Z_mod_mult.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the numbers every cut state has (b9_geo): the entry sp0 and s1 (image B: (sp0 - 0x160) & -32), the class-5
   frame F (2048 bytes, 32-aligned, in the application range) and its shadow SH (256 cells, in the shadow band) *)
Definition b9_G (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + STK_reac_segconf_parse_file <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  in_app (pf_F v pos) 2048 /\ pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\
  kLowMemEnd <= pf_SH v pos /\ pf_SH v pos + 256 <= kHighShadowEnd.
(* the bytes a B9 step may write: the callees' windows below s1 (and the rest of parse_file's window below s1),
   slot 0x70 (sl: val, 0x88574) and buf (F + 0x40, 512 bytes) *)
Definition b9_Wrx (v : pfv) (pos : Z) (sl : bool) (a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (sl = true /\ pf_s1 v + 0x70 <= a < pf_s1 v + 0x78) \/
  (pf_F v pos + PF_O_BUF <= a < pf_F v pos + PF_O_BUF + 512).
Lemma b9_Wrx_mono : forall v pos sl a, b9_Wrx v pos sl a -> b9_Wrx v pos true a.
Proof.
intros v pos sl a [H | [(_ & H) | H]]; unfold b9_Wrx; [left | right; left | right; right]; auto.
Qed.
(* a byte below alloc_ceiling and outside the frame is not one *)
Lemma b9_out : forall v pos a, b9_G v pos -> a < alloc_ceiling -> ~ (pf_F v pos <= a < pf_F v pos + 2048) ->
  ~ b9_Wrx v pos true a.
Proof.
intros v pos a G Hc Hf W. pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
unfold b9_Wrx, PF_O_BUF in W. rewrite SPF in G1, W.
destruct W as [W | [W | W]].
- lia.
- destruct W as [_ W]. lia.
- lia.
Qed.
(* a word whose 8 bytes are kept *)
Lemma b9_rdword_keep : forall (rd rd' : reader) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd' a = rdword rd a.
Proof. exact rdword_ext. Qed.
(* a region [cb, cb + cn) a step may write besides b9_Wrx: application bytes below the ceiling, outside the image
   range [0x10000, kImgEnd) and the frame; the empty region (cn = 0) gives the plain keep lemmas *)
Definition b9_RG (v : pfv) (pos : Z) (cb cn : Z) : Prop :=
  forall a, cb <= a < cb + cn ->
  a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ ~ (0x10000 <= a < kImgEnd) /\
  ~ (pf_F v pos <= a < pf_F v pos + 2048).
Lemma b9_RG_0 : forall v pos cb, b9_RG v pos cb 0.
Proof. intros v pos cb a Ha. exfalso. lia. Qed.
Lemma b9_RG_low : forall v pos cb cn a, b9_RG v pos cb cn -> 0x10000 <= a < kImgEnd -> ~ (cb <= a < cb + cn).
Proof. intros v pos cb cn a H Ha Hr. exact (proj1 (proj2 (proj2 (H a Hr))) Ha). Qed.
Lemma b9_RG_img : forall v pos cb cn a, b9_RG v pos cb cn -> in_img SEGS a -> ~ (cb <= a < cb + cn).
Proof. intros v pos cb cn a H Hi. exact (b9_RG_low v pos cb cn a H (pa_img_range a Hi)). Qed.
Lemma b9_RG_stk : forall v pos cb cn a, b9_RG v pos cb cn -> alloc_ceiling <= a -> ~ (cb <= a < cb + cn).
Proof. intros v pos cb cn a H Ha Hr. pose proof (proj1 (H a Hr)). lia. Qed.
Lemma b9_RG_frm : forall v pos cb cn a, b9_RG v pos cb cn -> pf_F v pos <= a < pf_F v pos + 2048 ->
  ~ (cb <= a < cb + cn).
Proof. intros v pos cb cn a H Ha Hr. exact (proj2 (proj2 (proj2 (H a Hr))) Ha). Qed.
(* the shadow band holds no application byte *)
Lemma b9_RG_band : forall v pos cb cn a, b9_RG v pos cb cn -> kLowMemEnd <= a < kHighShadowEnd ->
  ~ (cb <= a < cb + cn).
Proof.
intros v pos cb cn a H Ha Hr. destruct (H a Hr) as (_ & H2 & _).
unfold kLowMemEnd, kHighShadowEnd, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* the shadow cell of a byte below the ceiling *)
Lemma b9_RG_sh : forall v pos cb cn x, b9_RG v pos cb cn -> 0 <= x < alloc_ceiling ->
  ~ (cb <= SHADOW_OFF + x / 8 < cb + cn).
Proof.
intros v pos cb cn x H Hx. apply (b9_RG_band v pos cb cn _ H).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF. lia.
Qed.

(* ======================= the register lists ======================= *)
Lemma b9_rg_get : forall rX L r x, pf_rg rX L -> In (r, x) L -> getr rX (Z_to_bv 5 r) = w64 x.
Proof. intros rX L r x H Hin. exact (proj1 (Forall_forall _ _) H (r, x) Hin). Qed.
Lemma b9_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Lemma b9_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Lemma b9_rg_incl : forall rX L1 L2, incl L2 L1 -> pf_rg rX L1 -> pf_rg rX L2.
Proof. intros rX L1 L2 Hi H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin. exact (H rv (Hi rv Hin)). Qed.
(* every register of PF_RL, PF_RM and pf_fi's list is callee-saved *)
Lemma b9_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof. intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b9_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof. intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
(* pf_fi's register list (image B: SHADOW_OFF in x20 = s4, 0x87e9c) *)
Definition b9_FI (B : asyms) (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Lemma b9_FI_cs : forall B v, Forall (fun rv => acallee_saved (fst rv)) (b9_FI B v).
Proof. intros B v. unfold b9_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the image's read-only range is the listing's (B's SegObj.v; the pinned instance gives it by computation) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (as lib/B/Prog/reac_segconf_parse.v states it: the allocator record
   pins them; image B's stage-2 SegRecCells gives it from SegBSyms) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Lemma b9_fi_regs : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_rg rX (b9_FI B v).
Proof. intros v pos lyc Sc Wc rX memc mdc sc (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma b9_geo : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\ In (5, pos) (frames Sc) /\ b9_G v pos /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & _).
destruct HFI as (HJ & Hly & _).
destruct HCX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
subst lyc.
destruct (al_frames _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & Hfb & Hsh).
destruct (frames_bounds SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
change (fs_frame_bytes 5) with 2048 in *. change (2048 / 8) with 256 in Hsh.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *. rewrite SPF in *.
split; [exact HAR|]. split; [reflexivity|]. split; [exact Hin|].
split.
- unfold b9_G. rewrite SPF.
  pose proof (b9_mod32_down (pf_sp0 v - 0x160) ltac:(lia)) as (M1 & M2).
  assert (Hs1 : pf_s1 v = pf_sp0 v - 0x160 - (pf_sp0 v - 0x160) mod 32) by reflexivity.
  assert (ESH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
  assert (M16 : (pf_sp0 v - 0x160) mod 32 = 0 \/ (pf_sp0 v - 0x160) mod 32 = 16).
  { pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)).
    assert (E16 : (pf_sp0 v - 0x160) mod 16 = 0).
    { replace (pf_sp0 v - 0x160) with (pf_sp0 v + (-22) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
    pose proof (Z.div_mod (pf_sp0 v - 0x160) 32 ltac:(lia)) as D32.
    pose proof (Z.div_mod (pf_sp0 v - 0x160) 16 ltac:(lia)) as D16. lia. }
  pose proof Happ as Happ0.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  assert (Hq0 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : (pf_F v pos + 2048) / 8 = pf_F v pos / 8 + 256).
  { replace (pf_F v pos + 2048) with (pf_F v pos + 256 * 8) by lia. apply Z.div_add. lia. }
  assert (Hq3 : (pf_F v pos + 2048) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (Hq4 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in Hq4.
  rewrite ESH. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [rewrite Hs1; lia|].
  split; [rewrite Hs1; exact M1|]. split; [lia|]. split; [lia|]. split; [exact H32|].
  split; [exact Happ0|]. split; [reflexivity|]. split; lia.
- split; [exact (fun a Ha => proj1 (Hfb a Ha))|]. intros i Hi. exact (proj1 (Hsh i Hi)).
Qed.

(* ======================= what a B9 step keeps ======================= *)
(* the facts of a state: AR, the frame, the layout *)
Lemma b9_heap_out : forall v pos lyc Sc Wc memc mdc b m a,
  b9_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ b9_Wrx v pos true a.
Proof.
intros v pos lyc Sc Wc memc mdc b m a G HAR Hin Hly Hb Ha. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
change (fs_frame_bytes 5) with 2048 in Hd.
apply (b9_out v pos a G); lia.
Qed.
(* the shadow cell of a heap byte *)
Lemma b9_heap_shadow_out : forall v pos lyc Sc Wc memc mdc b m x,
  b9_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ b9_Wrx v pos true (SHADOW_OFF + x / 8).
Proof.
intros v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb Hx. subst lyc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, G9.
unfold b9_Wrx, PF_O_BUF. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *.
intros [W | [W | W]].
- lia.
- destruct W as [_ W]. lia.
- lia.
Qed.
(* an image byte *)
Lemma b9_img_out : forall v pos lyc Sc Wc memc mdc a,
  b9_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  in_img SEGS a -> ~ b9_Wrx v pos true a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Hi. subst lyc.
pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
pose proof (frm_img SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos a HAR Hin) as Hf.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hf. change (fs_frame_bytes 5) with 2048 in Hf.
pose proof asan_consts as (C1 & _).
apply (b9_out v pos a G); [lia | intros Ha; exact (Hf Ha Hi)].
Qed.
Lemma b9_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma b9_ro_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (b9_relro_img a Hr)].
Qed.
(* the layout's image range [0x10000, kImgEnd) holds no frame byte (AR's ledger, PAImg's pa_img_cover and
   al_client_img): so the read-only window and the stack-protector cells are not B9 writes, with no hypothesis on
   the instance *)
Lemma b9_low_out : forall v pos lyc Sc Wc memc mdc a,
  b9_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  0x10000 <= a < kImgEnd -> ~ b9_Wrx v pos true a.
Proof.
intros v pos lyc Sc Wc memc mdc a G HAR Hin Hly Ha. subst lyc.
pose proof HAR as (M & LG & _).
pose proof (pa_img_cover (p_ly v) Sc mdc LG) as [IC1 IC2].
pose proof asan_consts as (AC & _).
apply (b9_out v pos a G).
- unfold kImgEnd in *. lia.
- intros Hf. destruct (al_client_img _ _ LAWS (p_ly v) Sc Wc memc mdc a HAR) as [Hz _].
  { right. left. exists 5, pos. split; [exact Hin|].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048. exact Hf. }
  apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.

(* the keep premise every lemma below takes: rd' agrees with the state's reader off the B9 writes and off a
   region [cb, cb + cn) (b9_RG), and every visible byte stays visible *)
Section kr.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (rd' : reader) (cb cn : Z).
Hypothesis G : b9_G v pos.
Hypothesis HAR : AR SEGS B lyc Sc Wc memc mdc.
Hypothesis Hin : In (5, pos) (frames Sc).
Hypothesis Hly : lyc = p_ly v.
Hypothesis HRG : b9_RG v pos cb cn.
Hypothesis HKr : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> ~ (cb <= a < cb + cn) ->
  rd' a = rdW Wc memc a.
Hypothesis HV : forall a, rdW Wc memc a <> None -> rd' a <> None.

Lemma b9_keep_addr_r : forall q n, sa_heap B lyc Sc q n -> sa_addr (rdW Wc memc) q n -> sa_addr rd' q n.
Proof.
intros q n (b & m & Hb & H1 & H2) (A0 & A1 & A2 & A3 & A4).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HKr; [exact Hs | | |].
  + pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)).
    unfold SHADOW_OFF. lia.
  + exact (b9_heap_shadow_out v pos lyc Sc Wc memc mdc b m x G HAR Hin Hly Hb ltac:(lia)).
  + exact (b9_RG_sh v pos cb cn x HRG ltac:(lia)).
- intros Hn s Hs. apply HV. exact (A4 Hn s Hs).
Qed.
(* a heap string apart from the region; its tail granule is asked only to be visible (sa_tail) *)
Lemma b9_keep_hstr_r : forall q s, sa_heap B lyc Sc q (Z.of_nat (length s) + 1) ->
  (forall x, q <= x < q + (Z.of_nat (length s) + 1) -> ~ (cb <= x < cb + cn)) ->
  sa_str (rdW Wc memc) q s -> sa_str rd' q s.
Proof.
intros q s (b & m & Hb & H1 & H2) HD ((Hz & Hn) & Ht).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HKr; [exact (Hz i Hi) | lia | |].
  + refine (b9_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). lia.
  + apply HD. lia.
- intros x Hx. apply HV. exact (Ht x Hx).
Qed.
Lemma b9_keep_lit_r : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | intros x Hx; apply HV; exact (Ht x Hx)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
rewrite HKr; [exact (Hz i Hi') | lia | exact (b9_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Himg) |
  exact (b9_RG_img v pos cb cn _ HRG Himg)].
Qed.
Lemma b9_keep_img_word_r : forall a, (forall k, 0 <= k < 8 -> in_img SEGS (a + k)) ->
  rdword rd' a = rdword (rdW Wc memc) a.
Proof.
intros a Hi. apply b9_rdword_keep. intros k Hk. pose proof (pa_img_range _ (Hi k Hk)) as Hrg. unfold kImgEnd in Hrg.
apply HKr; [lia | exact (b9_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly (Hi k Hk)) |
  exact (b9_RG_img v pos cb cn _ HRG (Hi k Hk))].
Qed.
Lemma b9_keep_cat_r : sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B rd' catA.
Proof.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b9_keep_lit_r tp _ Hl)].
rewrite b9_keep_img_word_r; [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
refine (proj1 (Hi (pin_spec.row_addr catA i + k) _)). unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b9_keep_rod_r : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros HR a Hro Ho He. pose proof (b9_ro_img a Hro) as Hi. pose proof (pa_img_range _ Hi) as Hrg. unfold kImgEnd in Hrg.
rewrite HKr; [exact (HR a Hro Ho He) | lia | exact (b9_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Hi) |
  exact (b9_RG_img v pos cb cn _ HRG Hi)].
Qed.
Lemma b9_keep_obj_r : (forall x, p_t v <= x < p_t v + pf_len v -> ~ (cb <= x < cb + cn)) ->
  sa_ssp rd' gotwA guardA -> pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof.
intros HT HS (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & _).
split; [exact (b9_keep_hstr_r _ _ T3 HT T1)|]. split; [exact (b9_keep_addr_r _ _ T3 T2)|]. split; [exact T3|].
split; [exact (b9_keep_addr_r _ _ C2 C1)|]. split; [exact C2|]. split; [exact (b9_keep_cat_r CA)|].
split; [intros x Hx; exact (b9_keep_lit_r _ _ (LI x Hx))|]. split; [exact (b9_keep_rod_r RO) | exact HS].
Qed.
(* the stack-protector cells and the read-only window, kept with no Section hypothesis (b9_low_out) *)
Lemma b9_keep_ssp_r : sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (S1 & g & S2).
assert (KW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword rd' a = rdword (rdW Wc memc) a).
{ intros a H1 H2. apply b9_rdword_keep. intros k Hk. apply HKr; [unfold kImgEnd in *; lia | |].
  - apply (b9_low_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly). lia.
  - apply (b9_RG_low v pos cb cn _ HRG). lia. }
split; [rewrite KW; [exact S1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite KW; [exact S2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
Lemma b9_keep_rod0_r : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd /\ ~ b9_Wrx v pos true a).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (pa_img_range _ Hi) as Hrg.
    split; [exact Hrg | exact (b9_img_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Hi)].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr.
    assert (Hl : 0x10000 <= a < kImgEnd) by (unfold kImgEnd; lia).
    split; [exact Hl | exact (b9_low_out v pos lyc Sc Wc memc mdc _ G HAR Hin Hly Hl)]. }
rewrite HKr; [exact (HR a Hro Ho He) | unfold kImgEnd in *; lia | exact (proj2 Hlow) |
  exact (b9_RG_low v pos cb cn a HRG (proj1 Hlow))].
Qed.
Lemma b9_keep_obj0_r : (forall x, p_t v <= x < p_t v + pf_len v -> ~ (cb <= x < cb + cn)) ->
  pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof.
intros HT (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (b9_keep_hstr_r _ _ T3 HT T1)|]. split; [exact (b9_keep_addr_r _ _ T3 T2)|]. split; [exact T3|].
split; [exact (b9_keep_addr_r _ _ C2 C1)|]. split; [exact C2|]. split; [exact (b9_keep_cat_r CA)|].
split; [intros x Hx; exact (b9_keep_lit_r _ _ (LI x Hx))|].
split; [exact (b9_keep_rod0_r RO) | exact (b9_keep_ssp_r SS)].
Qed.
End kr.

(* the plain keep lemmas: rd' agrees with the state's reader off the B9 writes (the empty region) *)
Section k.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (rd' : reader).
Hypothesis G : b9_G v pos.
Hypothesis HAR : AR SEGS B lyc Sc Wc memc mdc.
Hypothesis Hin : In (5, pos) (frames Sc).
Hypothesis Hly : lyc = p_ly v.
Hypothesis HK : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rd' a = rdW Wc memc a.
Hypothesis HV : forall a, rdW Wc memc a <> None -> rd' a <> None.
Let HR0 : b9_RG v pos 0 0 := b9_RG_0 v pos 0.
Let HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> ~ (0 <= a < 0 + 0) -> rd' a = rdW Wc memc a :=
  fun a Ha HW _ => HK a Ha HW.

Lemma b9_keep_addr : forall q n, sa_heap B lyc Sc q n -> sa_addr (rdW Wc memc) q n -> sa_addr rd' q n.
Proof. intros q n H1 H2. eapply b9_keep_addr_r; eassumption. Qed.
Lemma b9_keep_hstr : forall q s, sa_heap B lyc Sc q (Z.of_nat (length s) + 1) -> sa_str (rdW Wc memc) q s ->
  sa_str rd' q s.
Proof. intros q s H1 H2. eapply b9_keep_hstr_r; try eassumption. intros x _ Hx. lia. Qed.
Lemma b9_keep_lit : forall a s, sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B rd' a s.
Proof. intros a s H. eapply b9_keep_lit_r; eassumption. Qed.
Lemma b9_keep_img_word : forall a, (forall k, 0 <= k < 8 -> in_img SEGS (a + k)) ->
  rdword rd' a = rdword (rdW Wc memc) a.
Proof. intros a H. eapply b9_keep_img_word_r; eassumption. Qed.
Lemma b9_keep_cat : sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B rd' catA.
Proof. intros H. eapply b9_keep_cat_r; eassumption. Qed.
Lemma b9_keep_rod : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof. intros H. eapply b9_keep_rod_r; eassumption. Qed.
Lemma b9_keep_obj : sa_ssp rd' gotwA guardA -> pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof. intros H1 H2. eapply b9_keep_obj_r; try eassumption. intros x _ Hx. lia. Qed.
Lemma b9_keep_ssp : sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof. intros H. eapply b9_keep_ssp_r; eassumption. Qed.
Lemma b9_keep_rod0 : arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof. intros H. eapply b9_keep_rod0_r; eassumption. Qed.
Lemma b9_keep_obj0 : pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc rd'.
Proof. intros H. eapply b9_keep_obj0_r; try eassumption. intros x _ Hx. lia. Qed.
(* c's bytes, cur_name (F + 0x20, below buf) and cur's slot 0xc0 (image B's pf_st) *)
Lemma b9_keep_st : forall cf cur nm k, sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros cf cur nm k (b & m & Hb & H1 & H2) ((bs & Hbs & Henc) & HC & (f & Hf & Hfe) & HN & HS0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof asan_consts as (AC1 & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
split; [|split; [exact HC|split; [|split; [exact HN|]]]].
- exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
  rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
  refine (b9_heap_out v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). unfold seg_spec.SEG_C_SIZE in *. lia.
- exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
  rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
  unfold b9_Wrx, PF_O_BUF, PF_O_CN. rewrite SPF in *.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
- rewrite b9_rdword_keep with (rd := rdW Wc memc); [exact HS0|]. intros j Hj. apply HK; [lia|].
  unfold b9_Wrx, PF_O_BUF. rewrite SPF in *.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
Qed.
End k.

(* the stack slots, the saved registers, the flag word and the frame's shadow, kept by a step that writes only
   b9_Wrx bytes and a region (each with the narrowest write set it needs; sl is free where slot 0x70 is not
   read). The plain lemmas are the empty region's case. *)
(* any slots off [s1 + 0x70, s1 + 0x78): those of [s1, s1 + 0x70) and of [s1 + 0x78, s1 + 0xe0) (0x40, 0xc0, 0xc8,
   PF_SL's 23) *)
Lemma b9_keep_slots_r : forall v pos (rd rd' : reader) sl cb cn (L : list (Z * Z)), b9_G v pos ->
  b9_RG v pos cb cn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> ~ (cb <= a < cb + cn) -> rd' a = rd a) ->
  Forall (fun ov => (0 <= fst ov /\ fst ov + 8 <= 0x70) \/ (0x78 <= fst ov /\ fst ov + 8 <= 0xe0)) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' sl cb cn L G HR HK HL H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov.
specialize (H _ Hov). specialize (HL _ Hov). cbn [fst snd] in *.
rewrite b9_rdword_keep with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia | |].
- unfold b9_Wrx, PF_O_BUF. rewrite SPF.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
- apply (b9_RG_stk v pos cb cn _ HR). lia.
Qed.
Lemma b9_keep_slots : forall v pos (rd rd' : reader) sl (L : list (Z * Z)), b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> rd' a = rd a) ->
  Forall (fun ov => (0 <= fst ov /\ fst ov + 8 <= 0x70) \/ (0x78 <= fst ov /\ fst ov + 8 <= 0xe0)) L ->
  pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos rd rd' sl L G HK. apply (b9_keep_slots_r v pos rd rd' sl 0 0 L G (b9_RG_0 v pos 0)).
intros a Ha HW _. exact (HK a Ha HW).
Qed.
Lemma b9_keep_sl_r : forall v pos (rd rd' : reader) sl cb cn, b9_G v pos -> b9_RG v pos cb cn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> ~ (cb <= a < cb + cn) -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' sl cb cn G HR HK H. apply (b9_keep_slots_r v pos rd rd' sl cb cn _ G HR HK); [|exact H].
unfold PF_SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
Qed.
Lemma b9_keep_sl : forall v pos (rd rd' : reader) sl, b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' sl G HK. apply (b9_keep_sl_r v pos rd rd' sl 0 0 G (b9_RG_0 v pos 0)).
intros a Ha HW _. exact (HK a Ha HW).
Qed.
Lemma b9_keep_slot70 : forall v pos (rd rd' : reader) x, b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos false a -> rd' a = rd a) ->
  pf_sl rd (pf_s1 v) [(0x70, x)] -> pf_sl rd' (pf_s1 v) [(0x70, x)].
Proof.
intros v pos rd rd' x G HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in H. cbn [fst snd] in *.
rewrite b9_rdword_keep with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia|].
unfold b9_Wrx, PF_O_BUF. rewrite SPF in *.
intros [W | [W | W]]; [lia | destruct W as [W _]; discriminate W | lia].
Qed.
Lemma b9_keep_saved_r : forall v pos (rd rd' : reader) sl cb cn regs, b9_G v pos -> b9_RG v pos cb cn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> ~ (cb <= a < cb + cn) -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' sl cb cn regs G HR HK H j r Hj.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite b9_rdword_keep with (rd := rd); [exact (H j r Hj)|]. intros k Hk. apply HK; [lia | |].
- unfold b9_Wrx, PF_O_BUF. rewrite SPF.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
- apply (b9_RG_stk v pos cb cn _ HR). lia.
Qed.
Lemma b9_keep_saved : forall v pos (rd rd' : reader) sl regs, b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> rd' a = rd a) ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' sl regs G HK. apply (b9_keep_saved_r v pos rd rd' sl 0 0 regs G (b9_RG_0 v pos 0)).
intros a Ha HW _. exact (HK a Ha HW).
Qed.
Lemma b9_keep_flag_r : forall v pos (rd rd' : reader) sl cb cn x, b9_G v pos -> b9_RG v pos cb cn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> ~ (cb <= a < cb + cn) -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos rd rd' sl cb cn x G HR HK H.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
change (fs_frame_bytes 5) with 2048 in *.
rewrite b9_rdword_keep with (rd := rd); [exact H|]. intros k Hk. apply HK; [lia | |].
- unfold b9_Wrx, PF_O_BUF. rewrite SPF.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
- apply (b9_RG_frm v pos cb cn _ HR). lia.
Qed.
Lemma b9_keep_flag : forall v pos (rd rd' : reader) sl x, b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> rd' a = rd a) ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x -> rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros v pos rd rd' sl x G HK. apply (b9_keep_flag_r v pos rd rd' sl 0 0 x G (b9_RG_0 v pos 0)).
intros a Ha HW _. exact (HK a Ha HW).
Qed.
Lemma b9_keep_fsh_r : forall v pos (rd rd' : reader) sl cb cn sc, b9_G v pos -> b9_RG v pos cb cn ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> ~ (cb <= a < cb + cn) -> rd' a = rd a) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sl cb cn sc G HR HK H i Hi.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite HK; [exact (H i Hi) | unfold kHighShadowEnd in G12; lia | |].
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
  unfold b9_Wrx, PF_O_BUF. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
  intros [W | [W | W]]; [lia | destruct W as [_ W]; lia | lia].
- apply (b9_RG_band v pos cb cn _ HR). lia.
Qed.
Lemma b9_keep_fsh : forall v pos (rd rd' : reader) sl sc, b9_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos sl a -> rd' a = rd a) ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sl sc G HK. apply (b9_keep_fsh_r v pos rd rd' sl 0 0 sc G (b9_RG_0 v pos 0)).
intros a Ha HW _. exact (HK a Ha HW).
Qed.

(* ======================= the cut state after a step ======================= *)
(* pf_base after a step that kept every byte off b9_Wrx (and every visible byte visible), with the journal it
   returned at the same layout, the frame state changed at most (set_fs), the live blocks permuted; image B's
   pf_fi carries pf_tf (a Prop over v pos, handed on) and c's slot 0xc8 (b9_keep_slots) *)
Lemma b9_move : forall v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (b9_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm HK HV HRG HFSH.
pose proof (b9_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & HFRM & HTF & HSLC & _).
pose proof (SSPX _ _ _ _ _ (proj1 HJ')) as HSS.
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply b9_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (b9_keep_saved v pos _ _ true _ G HK HSV)|].
  split; [exact (b9_keep_flag v pos _ _ true _ G HK HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [|exact HRG].
  apply (b9_keep_slots v pos _ _ true _ G HK); [|exact HSLC].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst]. lia. }
split.
{ assert (HO : pf_obj B v lyc Sc (rdW Wc' memc')) by (eapply b9_keep_obj; eassumption).
  destruct HO as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (b9_keep_sl v pos _ _ true G HK HSL) | exact HFSH].
Qed.
(* b9_move with no Section hypothesis: the stack-protector cells and the read-only window are kept bytes
   (b9_keep_obj0), so neither SSPX nor VRO is needed *)
Lemma b9_move0 : forall v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc' Wc' memc' mdc' 0 ->
  (exists f, Sc' = set_fs f Sc) -> Permutation (ablocks B lyc Sc') (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc' memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc' memc' a <> None) ->
  pf_rg rX' (b9_FI B v) ->
  pf_fsh (rdW Wc' memc') (pf_SH v pos) sc' ->
  pf_base B v pos lyc Sc' Wc' rX' memc' mdc' sc'.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc Sc' Wc' rX' memc' mdc' sc' HB HJ' [f HSf] HPerm HK HV HRG HFSH.
pose proof (b9_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & _).
destruct HFI as (_ & _ & (f0 & HS0) & HP0 & HSV & HFL & HFRM & HTF & HSLC & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exists f; rewrite HSf, HS0; apply b9_set_fs2|].
  split; [exact (Permutation_trans HPerm HP0)|].
  split; [exact (b9_keep_saved v pos _ _ true _ G HK HSV)|].
  split; [exact (b9_keep_flag v pos _ _ true _ G HK HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [|exact HRG].
  apply (b9_keep_slots v pos _ _ true _ G HK); [|exact HSLC].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst]. lia. }
split.
{ assert (HO : pf_obj B v lyc Sc (rdW Wc' memc')) by (eapply b9_keep_obj0; eassumption).
  destruct HO as (T1 & T2 & T3 & C1 & C2 & REST).
  assert (TR : forall q n, sa_heap B lyc Sc q n -> sa_heap B lyc Sc' q n).
  { intros q n (b & m & Hb & H1 & H2). exists b, m. split; [|lia].
    exact (Permutation_in _ (Permutation_sym HPerm) Hb). }
  exact (conj T1 (conj T2 (conj (TR _ _ T3) (conj C1 (conj (TR _ _ C2) REST))))). }
split; [exact (b9_keep_sl v pos _ _ true G HK HSL) | exact HFSH].
Qed.
(* ======================= the text, the read-only view, the frame chain ======================= *)
Lemma b9_text : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ~ In 0 (p_s v) /\ (length (p_s v) <= 65535)%nat /\ sa_str (rdW Wc memc) (p_t v) (p_s v) /\
  sa_addr (rdW Wc memc) (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & _ & HOBJ & _).
destruct HOBJ as (HSTR & HADDR & HHEAP & _ & HC & _).
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLS & _).
split; [exact (proj2 (proj1 HSTR))|]. split; [exact HLS|]. auto.
Qed.
Lemma b9_rom : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
intros a (sg & Hsg & Hw & Hr) Ho He. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* the frame chain at a call from B9 (s0 = sp0, the frame pointer, 0x87e74): the prologue's record (ra at sp0 - 8,
   the entry s0 at sp0 - 16, pf_saved) on afn_pre's chain, which the journal keeps above sp0 *)
Lemma b9_chain : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof (b9_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & _).
destruct HFI as (HJ & _ & _ & _ & HSV & _).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [rewrite SPF in G1; lia | rewrite SPF; lia |].
    intros Hf. apply b9_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. rewrite SPF in G1. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + rewrite SPF in G1. lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
End e.
End f.
End d.
