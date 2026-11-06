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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 70 of its 103 lines of code are new or changed and 420 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): lemma P5 of the A10b bcmp / refuse piece (lib/A/Prog/
   pf_a10b_b.v, PA10_B; code 0x88450 .. 0x884f8 of reac_segconf_parse_file, image A 0x87a78). Part of segment
   A10b's proof, by the G3 walk owner, 2026-10-30. Rule 24: proves no function (kind: segment lemma); the function
   this belongs to is reac_segconf_parse_file, whose reuse search and verdict (none: written new) are in the unit's
   internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md.
   No instruction is walked here. b_join: after the refuse call at 0x884e8 (made at sp = s1, footprint
   refuse_W c cf) returned at the FP state fx1, the JOIN cut (pf_a10b_k.INV_JOIN, 0x8888c) holds at the returned
   state with c's state refuse cf (ln + 1) F_badrole [AS nm; AS val]. The cut facts are rebuilt by segment A6's shared
   kit lib/A/Prog/pf_a6_k.v (a6_keeps_refuse: refuse's journal gives the agreements a6_keeps; a6_base_move: pf_base
   at fx1 from them and the caller's journal; a6_nm_move: cur_name); the line's state by SegModel.refuse_proj and
   pfA_facts.pf_cnt_refuse; the registers by aregs_preserved (pf_a5_k.a5_rg_pres). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces pf_a10b_k.
(* the shared transport kits of the parse_file walk (pieces A5 and A6, in the base) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k pf_a6_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

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
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis VRO : seg_val_relro (PI := PI).

(* two register files that both hold the list L agree on every register L names *)
Lemma bj_rg_same : forall (r1 r2 : bvmap 5 word) (L : list (Z * Z)) (r : Z),
  pf_rg r1 L -> pf_rg r2 L -> In r (map fst L) -> getr r1 (Z_to_bv 5 r) = getr r2 (Z_to_bv 5 r).
Proof.
intros r1 r2 L r H1 H2 Hr. apply in_map_iff in Hr as ([r' x] & Hrr & Hin). cbn [fst] in Hrr. subst r'.
unfold pf_rg in H1, H2. rewrite Forall_forall in H1, H2.
specialize (H1 _ Hin). specialize (H2 _ Hin). cbn [fst snd] in H1, H2. rewrite H1, H2. reflexivity.
Qed.

(* ---- P5: the JOIN cut's facts after refuse returned at the FP state fx1 ---- *)
Lemma b_join : forall (fx1 : YK11.FPState) n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val
    (regsc : bvmap 5 word) ly2 S2 W2 regs2 mem2 md2,
  fxrel fx fx1 ->
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LOW -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  spZ regsc = pf_s1 v ->
  pf_rg regsc ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++
               [(20, seg_spec.rseg_addr (p_c v) gi)]) ->
  pf_rg regsc [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF)] ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 (0 + EV_refuse) ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 EV_refuse ->
  aregs_preserved regsc regs2 ->
  sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badrole [AS nm; AS val]) ->
  sa_noalloc B lyc Sc ly2 S2 ->
  INV_JOIN (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_badrole [AS nm; AS val])
    nm o ln d gi.
Proof.
intros fx1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsc ly2 S2 W2 regs2 mem2 md2
  Hfx HB HMID HST _ _ _ HRGA HRGB HJ0 HJR HPRES HRC HNA.
assert (E0 : 0 + EV_refuse = 0) by reflexivity. rewrite E0 in HJ0.
destruct HNA as (HP2 & Hly2 & HS2).
pose proof HB as (_ & (_ & _ & _ & _ & _ & _ & _ & HRG) & _).
(* refuse's journal (sp = s1, footprint in the block c) gives the agreements the cut's facts need *)
assert (KP : a6_keeps B v pos Wc memc W2 mem2)
  by exact (a6_keeps_refuse (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LOW cf ly2 S2 W2 mem2 md2 EV_refuse
    HB HJR HP2).
pose proof KP as (_ & _ & _ & KF).
unfold INV_JOIN.
split.
{ (* SSPX and VRO are used here and only here: a6_base_move takes both to rebuild pf_obj after refuse. refuse's
     post gives only its journal, which keeps an image byte only outside as_owned_static B (YCbq.v:479), so the
     stack-protector cells (GOT word 0xa36d8, guard 0x5ff078) come back by SSPX at the new AR state; and
     arodata_okP's relro arm needs those addresses to be image bytes, pa_relro_img through VRO. *)
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 22] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HPRES r) by (cbn [In] in Hr; unfold acallee_saved; lia).
    exact (bj_rg_same regsc rX _ r HRGB HRG Hr). }
  exact (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc rX memc mdc PF_SC_LOW ly2 S2 W2 regs2 mem2 md2
    HB Hfx HJ0 Hly2 HS2 HP2 KP KR). }
split; [exact HMID|].
split.
{ destruct HST as (RC & COK & NM & CNT).
  split; [exact HRC|].
  split.
  { change (gi < length (rc_seg (refuse cf (ln + 1) F_badrole [AS nm; AS val])))%nat.
    rewrite (proj1 (refuse_proj cf (ln + 1) F_badrole [AS nm; AS val])). exact COK. }
  split.
  { exact (a6_nm_move v pos _ _ nm NM (fun a Ha => KF a (or_introl Ha))). }
  exact (pf_cnt_refuse cf (ln + 1) F_badrole [AS nm; AS val] _ _ (pf_next_skipn_lt (p_s v) o (proj1 HMID)) CNT). }
apply (a5_rg_pres regsc regs2 _ HPRES); [|exact HRGA].
unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

End e.
End f.
End d.
