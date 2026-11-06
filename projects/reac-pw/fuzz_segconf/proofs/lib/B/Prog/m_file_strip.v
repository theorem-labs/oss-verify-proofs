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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 260 of its 303 lines of code are new or changed and 410 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the ONE shared strip call
   step of the image-B m_file segment walks, stated over lib/B/Prog/m_file_m.v's cut predicates, in the continuation
   form of lib/B/Prog/m_file_iq.v's mf_ieq_call. Image A has no counterpart (clang inlines strip into m_file there).
   Shared file of the image-B m_file-family owner's G2B (owner's decision 18:3xZ; users FRONT, HDRA, KEYA), written by one of its walk lanes.
   proves no function (kind: segment lemma of m_file's walk: the call step of strip).

   mf_strip_call: a call of strip (image B 0x879cc = BASE + AF_strip; m_file's five sites 0x864c0 (cells 176 / 168,
   FRONT), 0x86530 (208 / 200, HDRA), 0x865a0 (192 / 184, HDRA), 0x86658 (208 / 200, KEYA), 0x86664 (192 / 184,
   KEYA); the image-B m_file cut map section 3), from the state at strip's entry (the `jal` executed: pc = BASE + AF_strip, ra =
   BASE + ret, a0 = s1 + osc, a1 = s1 + oec, two distinct 8-aligned frame cells in [s1 + 160, s1 + 216), sp = s1),
   the cell osc holding p + a and the cell oec holding p + b, a <= b <= |rest|: strip_contract (lib/B/Prog/strip_c.v,
   written by the image-B contracts lane, accepted 75d9c51ac6cb) at SegInstB.STK_strip over the bytes l = zb (slice a b rest) of the text
   left. strip's post is apost_base (no side-stack frame, no allocator entry, EV_strip = 0), so the walk goes on at
   BASE + ret at the SAME FP state, with the cell osc holding p + a + strip_lead (slice a b rest) and the cell oec
   holding p + b - strip_trail (slice a b rest) (strip_c.v's strip_mid: the bytes between are h_strip of the slice),
   every cut fact kept, and every byte outside strip's stack window [s1 - STK_strip, s1) and the two cells as at the
   call (strip's sa_kept).
   THE CALL: PaCall.cl_callS does not fit, because strip's footprint is two cells of m_file's own stack frame, not a
   heap block (cl_callS's footprint premise); the step is PaNoChain.cl_callS_wide (the kit's ajournal_sub_wide): each
   footprint byte lies in m_file's stack window [sp0 - STK_m_file, sp0) (awr_byte's first arm) and is mapped after
   the call (strip's post holds a value in each cell). The callee's afn_pre comes from the walk's journal
   (YCbq.afn_pre_at) with the frame chain at s1 and s0 = sp0 (m_file_k.v's mf_chain_at, m_file's own record).
   THE PREMISES strip_pre asks, each from a cut fact: the cells (strip_args' sa_addr and alignment, strip_slot's
   presence and sp <= c) by m_file_sd.v's mf_slot_addr; c + 8 <= ly_top from the entry's astk_ok (sp0 <= ly_top,
   s1 + 216 <= sp0 - 104); the bytes (sa_bytes, sa_addr, sa_loc's heap arm, 0 < s0) from mf_loop's sa_str / sa_addr
   of the text left and m_file_pre's text block (m_file_sd.v's mf_txt_heap_now); apart from the cells by
   mf_heap_below_stack (every heap byte lies below s1 - 2 * ESTACK).
   THE KEEP: m_file_k.v's mf_keep_callx (84ea19e46fcc) with E = the two cells, inside mf_cfp's
   per-line scratch cells [s1 + 160, s1 + 216); the mconf block below the allocator's ceiling keeps its model
   (mf_mconf_keep).
   IMAGE B: s1 = (sp0 - 320) & -32, STK_m_file = 8,592, STK_strip = 16 (SegInstB.v).
   POSITIONAL NAMES: the cell offsets osc / oec are parameters (each site passes its own); the scratch area
   [s1 + 160, s1 + 216) is image B's table C.1 (cells 168 .. 208, 160 = FB unread), checked against
   the image-B m_file cut map's cell list.
   Section hypotheses: STRIP only (strip_contract at BASE + AF_strip and SegInstB.STK_strip, at every FP state). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq strip_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ===================================== lists ===================================== *)
Lemma st_slice_length : forall (l : list Z) a b, (a <= b <= length l)%nat -> length (slice a b l) = (b - a)%nat.
Proof. intros l a b H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.
Lemma st_slice_nth : forall (l : list Z) a b x, (x < b - a)%nat -> (b <= length l)%nat ->
  nth x (slice a b l) 0 = nth (a + x) l 0.
Proof. intros l a b x Hx Hb. unfold slice. rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _) Hx). rewrite nth_skipn. reflexivity. Qed.
Lemma st_zs_zb : forall l : list Z, (forall i, (i < length l)%nat -> 0 <= nth i l 0 < 256) -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
intros l. induction l as [|z r IH]; intros H; [reflexivity|].
cbn [seg_spec.zs seg_spec.zb map]. f_equal.
- pose proof (H 0%nat ltac:(cbn; lia)) as Hz. cbn [nth] in Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. cbn [Z.of_N]. lia.
- apply IH. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.
Lemma st_zb_length : forall l, length (seg_spec.zb l) = length l.
Proof. intros l. unfold seg_spec.zb. apply length_map. Qed.

(* ===================================== readers ===================================== *)
(* a sub-range of an addressable range is addressable (the image-A m_file-family lane's lib/A/Prog/m_file_s_hdra_e.v hda_hull_sub /
   hda_addr_sub, statements and proofs) *)
Lemma st_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> 0 < n' -> q <= q' -> q' + n' <= q + n ->
  shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hn' H1 H2 s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : q / 8 <= q' / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (q' + n' - 1) / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (B1 : (SHADOW_OFF + q / 8) / 8 * 8 <= (SHADOW_OFF + q' / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  assert (B2 : (SHADOW_OFF + (q' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  lia.
Qed.
Lemma st_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' ->
  sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (H1 & H2 & H3 & H4 & H5) Hq Hn Hn0.
  split; [lia|]. split; [lia|]. split.
  - unfold amem_range in *. destruct H3 as [H3|[H3a H3b]]; [left; lia | right; split; lia].
  - split; [exact (range_addressable_sub rd SHADOW_OFF q n q' n' H4 Hq Hn)|].
    intros Hn'. apply (st_hull_sub rd q n q' n'); [apply H5; lia | lia | lia | lia].
Qed.
(* byte x of the text left rest at p (its NUL at x = |rest|) (m_file_s_hdra_e.v hda_txt_byte) *)
Lemma st_txt_byte : forall rd p rest x, sa_str rd p rest -> (x <= length rest)%nat ->
  rd (p + Z.of_nat x) = Some (nth x rest 0).
Proof.
  intros rd p rest x ((HZ & _) & _) Hx.
  rewrite (HZ x ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (Nat.eq_dec x (length rest)) as [->|Hne].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - rewrite app_nth1 by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte through the world's view is a byte *)
Lemma st_aview_range : forall (W : world SEGS) mem x v, rdW W mem x = Some v -> 0 <= v < 256.
Proof.
intros W mem x v H. unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) x) as [b|]; [|discriminate].
cbn [option_map] in H. injection H as <-. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
cbn [Z.of_N] in R. lia.
Qed.
(* a field of the restricted memory is the same field through the world's view, and back *)
Lemma st_sa_val_of_val_mem : forall (W : world SEGS) mem a n v,
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> sa_val (rdW W mem) a n v.
Proof.
intros W mem a n v H k Hk. unfold aview. rewrite (H k Hk). cbn [option_map]. f_equal.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) 256 ltac:(lia)) as HR.
rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|].
change (bv_modulus 8) with 256. exact HR.
Qed.
Lemma st_val_mem_of_sa_val : forall (W : world SEGS) mem a n v,
  sa_val (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate].
cbn [option_map] in H. injection H as H.
f_equal. rewrite <- (Z_to_bv_bv_unsigned _ b). f_equal. rewrite H. reflexivity.
Qed.
(* the bytes of the text left are bytes *)
Lemma st_rest_range : forall (W : world SEGS) mem p rest, sa_str (rdW W mem) p rest ->
  forall i, (i < length rest)%nat -> 0 <= nth i rest 0 < 256.
Proof.
intros W mem p rest HS i Hi. apply (st_aview_range W mem (p + Z.of_nat i)).
apply st_txt_byte; [exact HS | lia].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callee, at every FP state *)
Hypothesis STRIP : forall fx0 : YK11.FPState,
  strip_contract (fx := fx0) SEGS B (BASE + AF_strip) SegInstB.STK_strip.

(* strip from its entry with the cells osc / oec holding p + a / p + b, the bytes [a, b) of the text left: the cells
   at BASE + ret hold the stripped ends, every cut fact kept, every byte outside strip's window and the two cells
   unchanged *)
Lemma mf_strip_call : forall v lyc Sc Wc (regsc : bvmap 5 word) memc mdc pos lowsh (mcc : mconf) (cur : option nat)
  (line p : Z) (rest : list Z) (np ret osc oec : Z) (a b : nat),
  mf_cx B v -> mf_ls v lyc Sc ->
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc np -> mf_regs_at B v lyc pos regsc ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  160 <= osc -> osc + 8 <= 216 -> osc mod 8 = 0 -> 160 <= oec -> oec + 8 <= 216 -> oec mod 8 = 0 -> osc <> oec ->
  getr regsc 10 = w64 (mf_s1 (mv_sp v) + osc) -> getr regsc 11 = w64 (mf_s1 (mv_sp v) + oec) ->
  (a <= b <= length rest)%nat ->
  mf_slot v memc Wc osc (p + Z.of_nat a) -> mf_slot v memc Wc oec (p + Z.of_nat b) ->
  (forall S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    wle Wc W2 -> mf_ls v lyc S2 ->
    mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc -> mf_cells v lyc pos mem2 W2 cur ->
    mf_loop v W2 mem2 mcc cur line p rest -> mf_np v mem2 W2 np -> mf_regs_at B v lyc pos regs2 ->
    aregs_preserved regsc regs2 ->
    mf_slot v mem2 W2 osc (p + Z.of_nat a + Z.of_nat (strip_lead (slice a b rest))) ->
    mf_slot v mem2 W2 oec (p + Z.of_nat b - Z.of_nat (strip_trail (slice a b rest))) ->
    (forall x, 0 <= x < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - SegInstB.STK_strip <= x < mf_s1 (mv_sp v)) ->
     ~ (mf_s1 (mv_sp v) + osc <= x < mf_s1 (mv_sp v) + osc + 8) ->
     ~ (mf_s1 (mv_sp v) + oec <= x < mf_s1 (mv_sp v) + oec + 8) ->
     rdW W2 mem2 x = rdW Wc memc x) ->
    SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_strip)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur line p rest np ret osc oec a b
  CX LS CORE CELLS LOOP NP RA R1 Hret Hret2 Ho1 Ho2 Ho3 He1 He2 He3 Hoe R10 R11 Hab VS VE KC.
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht64 & _ & _ & HMP & HEV).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi, Htop.
assert (HSTK0 : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK0 in Hslo.
pose proof CORE as (HJ & HPm & _).
pose proof HJ as (HAR & Hly & _ & Hwle & _ & Hfrs & Hnev & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & Ho16).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HSTK1 : SegInstB.STK_strip = 16) by (vm_compute; reflexivity).
assert (HSTKR : SegInstB.STK_fuzz_catalogue_row = 8256) by (vm_compute; reflexivity).
pose proof LS as (Ely & f0 & ESc).
pose proof LOOP as (L1 & L2 & L3 & LSTR & LADDR & _).
pose proof LADDR as (Hp0 & Hp63 & _).
pose proof (mf_sp_at B v lyc pos regsc CX RA) as Hsp0.
destruct (mf_chain_at B v lyc Sc Wc memc mdc pos lowsh mcc regsc CX CORE RA) as (ch1 & HCH).
set (sp0 := mv_sp v) in *.
set (s1 := mf_s1 sp0) in *.
assert (Hsp : spZ regsc = sp0 + (s1 - sp0)) by lia.
rewrite Hsp in HCH.
(* the cells *)
destruct (mf_slot_addr B v lyc Sc Wc memc mdc pos lowsh mcc osc CX LS CORE ltac:(lia) ltac:(lia))
  as (SCA & SCP & _ & Hs1m).
destruct (mf_slot_addr B v lyc Sc Wc memc mdc pos lowsh mcc oec CX LS CORE ltac:(lia) ltac:(lia))
  as (ECA & ECP & _ & _).
fold sp0 s1 in SCA, SCP, ECA, ECP, Hs1m.
set (sc := s1 + osc) in *. set (ec := s1 + oec) in *.
assert (Hs18 : s1 mod 8 = 0).
{ replace s1 with ((s1 / 32) * 4 * 8) by (pose proof (Z.div_mod s1 32 ltac:(lia)); lia). apply Z.mod_mul. lia. }
assert (Hsc8 : sc mod 8 = 0) by (subst sc; rewrite Zplus_mod, Hs18, Ho3; reflexivity).
assert (Hec8 : ec mod 8 = 0) by (subst ec; rewrite Zplus_mod, Hs18, He3; reflexivity).
assert (Hoe8 : osc + 8 <= oec \/ oec + 8 <= osc).
{ pose proof (Z.div_mod osc 8 ltac:(lia)). pose proof (Z.div_mod oec 8 ltac:(lia)).
  assert (osc / 8 <> oec / 8) by (intros Heq; apply Hoe; lia). lia. }
(* the bytes [a, b) of the text left *)
set (sl := slice a b rest).
set (l := seg_spec.zb sl).
assert (Lsl : length sl = (b - a)%nat) by (subst sl; apply st_slice_length; lia).
assert (Hsl : forall x, (x < length sl)%nat -> 0 <= nth x sl 0 < 256).
{ intros x Hx. subst sl. rewrite Lsl in Hx. rewrite st_slice_nth by lia.
  apply (st_rest_range Wc memc p rest LSTR). lia. }
assert (Hzs : seg_spec.zs l = sl) by (subst l; apply st_zs_zb; exact Hsl).
assert (Ll : length l = (b - a)%nat) by (subst l; rewrite st_zb_length; exact Lsl).
assert (HSB : sa_bytes (rdW Wc memc) (p + Z.of_nat a) l).
{ intros x Hx. rewrite Ll in Hx. subst l. unfold seg_spec.zb.
  rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map, Lsl; lia).
  rewrite map_nth. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small.
  2:{ unfold bv_modulus. cbn [Z.of_N]. pose proof (Hsl x ltac:(rewrite Lsl; lia)). lia. }
  subst sl. rewrite st_slice_nth by lia. replace (p + Z.of_nat a + Z.of_nat x) with (p + Z.of_nat (a + x)) by lia.
  apply st_txt_byte; [exact LSTR | lia]. }
assert (HTH : sa_heap B lyc Sc (mv_t v) (Z.of_nat (length (mv_s v)) + 1))
  by exact (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE).
pose proof (mf_heap_below_stack B v lyc Sc Wc memc mdc pos lowsh mcc _ _ CX CORE HTH) as HBS.
fold sp0 s1 in HBS.
assert (HES : YG0d.ESTACK = 4096) by reflexivity.
assert (Hrest : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & (Ht1 & _) & _).
assert (Hend : p + Z.of_nat b < s1 - 2 * YG0d.ESTACK) by (apply HBS; lia).
assert (HSA : sa_addr (rdW Wc memc) (p + Z.of_nat a) (p + Z.of_nat b - (p + Z.of_nat a)))
  by (apply (st_addr_sub _ p (Z.of_nat (length rest) + 1)); [exact LADDR | lia | lia | lia]).
assert (HSH : sa_heap B lyc Sc (p + Z.of_nat a) (p + Z.of_nat b - (p + Z.of_nat a))).
{ destruct HTH as (bb & bm & Hbin & Hb1 & Hb2). exists bb, bm. split; [exact Hbin|]. lia. }
(* the call's entry facts *)
assert (Hraw4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + ret))) by (rewrite unsigned_lit_small by lia; lia).
assert (Hsc64 : 0 <= sc < 2 ^ 64) by (subst sc; lia).
assert (Hec64 : 0 <= ec < 2 ^ 64) by (subst ec; lia).
assert (HSP : strip_pre SEGS B lyc Sc Wc memc regsc sc ec (p + Z.of_nat a) (p + Z.of_nat b) l).
{ split; [|split; [|split]].
  - split; [exact Hsc8|]. split; [exact Hec8|]. split; [unfold sa_disj; subst sc ec; lia|].
    split; [exact (st_sa_val_of_val_mem Wc memc sc 8 _ VS)|]. split; [exact SCA|].
    split; [exact (st_sa_val_of_val_mem Wc memc ec 8 _ VE)|]. split; [exact ECA|].
    split; [lia|]. split; [exact HSB|]. split; [rewrite Ll; lia|]. split; [exact HSA|].
    split; unfold sa_disj; subst sc ec; lia.
  - split; [subst sc; lia|]. split; [subst sc; rewrite Ely; lia|].
    intros i Hi. exact (SCP i Hi).
  - split; [subst ec; lia|]. split; [subst ec; rewrite Ely; lia|].
    intros i Hi. exact (ECP i Hi).
  - left. exact HSH. }
assert (HEV1 : st_nev Sc + EV_strip <= EV_MAX).
{ unfold EV_strip. unfold EV_m_file in HEV. rewrite ESc. cbn [st_nev set_fs]. lia. }
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_strip)) SegInstB.STK_m_file sp0
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdc 0 SegInstB.STK_strip [(sc, sc + 8); (ec, ec + 8)] EV_strip (s1 - sp0) (Z_to_bv 64 (BASE + ret)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_val (rdW W2 mem2) sc 8%nat (p + Z.of_nat a + Z.of_nat (strip_lead (seg_spec.zs l))) /\
       sa_val (rdW W2 mem2) ec 8%nat (p + Z.of_nat b - Z.of_nat (strip_trail (seg_spec.zs l))) /\
       sa_kept SEGS Wc memc W2 mem2 regsc SegInstB.STK_strip (fun x => sc <= x < sc + 8 \/ ec <= x < ec + 8) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - lia.
  - rewrite HSTK1; lia.
  - rewrite HSTK, HSTK1; lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - exact Hraw4.
  - exact HCH.
  - intros HPRE1. eapply SRr_mono.
    + exact (STRIP fx lyc Sc Wc regsc memc mdc ch1 sc ec (p + Z.of_nat a) (p + Z.of_nat b) l HPRE1
        R10 Hsc64 R11 Hec64 HSP HEV1).
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, R1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - (* strip's footprint, the two cells, lies in m_file's stack window *)
    intros x Hx. unfold awr_byte. left. rewrite HSTK.
    destruct Hx as (r & Hr & Hxr). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hxr; subst sc ec; lia.
  - (* and is mapped after the call: strip's post holds a value in each cell *)
    intros ly2 S2 W2 regs2 mem2 md2 (VS2 & VE2 & _) x Hx _ _.
    destruct Hx as (r & Hr & Hxr). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hxr.
    + specialize (VS2 (Z.to_nat (x - sc)) ltac:(lia)). replace (sc + Z.of_nat (Z.to_nat (x - sc))) with x in VS2 by lia.
      rewrite VS2. discriminate.
    + specialize (VE2 (Z.to_nat (x - ec)) ltac:(lia)). replace (ec + Z.of_nat (Z.to_nat (x - ec))) with x in VE2 by lia.
      rewrite VE2. discriminate. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (VS3 & VE3 & HKP & HNA)).
rewrite Hzs in VS3, VE3. unfold EV_strip in HJo.
assert (K3 : forall x, 0 <= x < 2 ^ 64 -> ~ (s1 - SegInstB.STK_strip <= x < s1) ->
  ~ (s1 + osc <= x < s1 + osc + 8) -> ~ (s1 + oec <= x < s1 + oec + 8) -> rdW W3 mem3 x = rdW Wc memc x).
{ intros x Hx Hw Hc1 Hc2. apply (HKP x Hx).
  - rewrite Hsp. replace (sp0 + (s1 - sp0)) with s1 by lia. exact Hw.
  - subst sc ec. lia. }
(* the mconf block lies below the allocator's ceiling, apart from strip's window and the cells *)
assert (HMC3 : sa_mconf (rdW W3 mem3) (mv_c v) mcc).
{ pose proof CORE as (_ & _ & _ & _ & _ & _ & HMC & _).
  destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bc & mc0 & Hinc & Hbc & Hec).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc0 HAR Hinc) as (_ & Hbc4096 & Hbcceil & _).
  apply (mf_mconf_keep Wc W3 memc mem3
    (fun x => (s1 - SegInstB.STK_strip <= x < s1) \/ (s1 + osc <= x < s1 + osc + 8) \/ (s1 + oec <= x < s1 + oec + 8))
    (mv_c v) mcc).
  - intros x Hx Hn. apply K3;
      [exact Hx | intros H; apply Hn; left; exact H | intros H; apply Hn; right; left; exact H
      | intros H; apply Hn; right; right; exact H].
  - lia.
  - unfold seg_spec.SEG_M_SIZE in *. lia.
  - intros x Hx. rewrite HSTK1. unfold seg_spec.SEG_M_SIZE in *. lia.
  - exact HMC. }
destruct (mf_keep_callx B v lyc Sc Wc regsc memc mdc pos lowsh mcc cur ly3 S3 W3 regs3 mem3 md3 (0 + 0)
  SegInstB.STK_strip (fun x => sc <= x < sc + 8 \/ ec <= x < ec + 8) mcc CX CORE CELLS RA HJo ltac:(lia) HP3 HNA)
  as (-> & LSf & CORE3 & CELLS3 & RA3 & NPf & LPf).
- rewrite HSTK1, HSTKR. lia.
- exact HKP.
- intros x Hx. unfold mf_cfp. right; left. fold sp0 s1. subst sc ec. lia.
- exact HMC3.
- apply (KC S3 W3 regs3 mem3 md3 Hwle3).
  + exact (LSf LS).
  + exact CORE3.
  + exact CELLS3.
  + exact (LPf _ _ _ _ _ LOOP).
  + exact (NPf _ NP).
  + exact RA3.
  + exact HP3.
  + unfold mf_slot. fold sp0 s1. apply st_val_mem_of_sa_val. exact VS3.
  + unfold mf_slot. fold sp0 s1. apply st_val_mem_of_sa_val. exact VE3.
  + exact K3.
Qed.
End e.
End f.
End d.
