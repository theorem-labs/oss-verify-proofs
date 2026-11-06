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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 496 of its 541 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan): the sub-walk JOIN of segment A8b of
   reac_segconf_parse_file's walk, 0x889b4 .. 0x889f4 (lib/A/Prog/pf_a8b_d.v's cut PF_A8B_JOIN). By the G3 walk
   owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk): one sub-walk of a walk-internal
   segment; the lane's rule-24 record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md
   (reuse verdict: none, written new).

   pfa8b_join : forall n, HA_TAIL B n -> H_A8B_JOIN (fx := fx) B n.

   THE CODE (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x889b4 lb a0,0(a3); bnez a0                       check #38 (load4 c->gen; a3 = shadow_addr (c + RC_GEN))
     0x889bc addi a0,s4,0x160; srli a1,a0,3; add a1,a1,s6; lb a2,0(a1)   check #39 (store4 seg[i].seen_gen)
     0x889cc ld a1,0x40(s1); lw a1,0(a1); bnez a2        a1 = c->gen
     0x889d8 sw a1,0(a0)                                 seg[i].seen_gen = c->gen
     0x889dc a2 = "%s"; a1 = 0x10; a0 = slot 0x50 = cur_name; a3 = s9 = np
     0x889f0 jal snprintf                                snprintf(cur_name, 16, "%s", np)   (PROV2's pc)
     0x889f4 j 0x88068                                   TAIL

   THE WALK. (1) The token executor from lib/A/Prog/pf_a8b_q.v's seed pfa8b_jseed runs 0x889b4 .. 0x889ec and
   decides both checks from pfj_SH (no obligation, no token); its awr_ok is the block case of awr_byte for the
   seen_gen store. (2) A plain run takes the jal. (3) pf_a8b_t.v's pfa8b_aj_snprintf_atSF steps the snprintf at
   row 4 (the destination cur_name lies in this call's class-5 frame: awr_byte's in_frames case, off_img from
   frm_off_imgP, the shadow from pf_fsh's cells 4 .. 5); the FR_cmd fact is pfa8b_FR_s_regs. (4) The walk is
   lifted to the FP state fx1 the call returned (srr_apost_baseF_lift), re-seeded with pfa8b_seed at 0x889f4,
   and the jump reaches TAIL, where HA_TAIL is applied at fx1 with the next line's offset and lineno.
   The facts at each state: pfj_move rebuilds pf_base after the store (the 4 seen_gen bytes of the block c) and
   after the call (cur_name and the callee's window below s1) by pf_a8b_k.v's transport; arodata_okP by
   pfj_arodata (the read-only window lies in [0x10000, kImgEnd), off the block, the frame and the window) and
   sa_ssp likewise, so neither VRO nor SSPX is taken. sa_rconf is pf_a8b_m.v's pfa8b_rconf_seengen, whose keep
   premise asks only the struct's bytes; cur_name's pf_nm is rebuilt by pfj_nm_after over the old 16-byte
   witness from the bytes the snprintf wrote.
   Section hypotheses: ASNP (row 4's snprintf, RtFormat.asnprintf_realizes at the listing's trampoline) and OBJ
   (seg_val_objs: "%s" is listing object 35). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_d pf_a8b_t pf_a8b_k pf_a8b_m
pf_a8b_q pf_a5_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pfj_gen_range : forall rd c cf, sa_rconf rd c cf -> 0 <= rc_gen cf < 2 ^ 32.
Proof. intros rd c cf (bs & _ & Henc). destruct Henc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _)). exact H. Qed.
Lemma pfj_nseg : forall rd c cf, sa_rconf rd c cf -> (length (rc_seg cf) <= 32)%nat.
Proof. intros rd c cf (bs & _ & Henc). exact (proj1 (proj2 Henc)). Qed.
(* the frame's shadow cells of cur_name (4, 5) and of buf (8 .. 71) are 0 at the line scope *)
Lemma pfj_shb0 : forall i, (4 <= i < 6 \/ 8 <= i < 72) -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb, PF_SC_LINE, pf_io. cbn [sc_cn sc_buf].
destruct (Z.ltb_spec i 4); [lia|]. destruct (Z.ltb_spec i 6); [reflexivity|].
destruct (Z.ltb_spec i 8); [lia|]. destruct (Z.ltb_spec i 72); [reflexivity | lia].
Qed.
(* cur_name after snprintf(cur_name, 16, "%s", name): the C string and its NUL over the old 16-byte witness *)
Lemma pfj_nm_after : forall (rd rd' : reader) (a : Z) (nm name : list Z) (f : list byte),
  sa_bytes rd a f -> seg_spec.cstr_enc 16 nm f ->
  (length name <= 15)%nat -> ~ In 0 name -> Forall (fun z => 0 < z < 256) name ->
  (forall j, (j <= length name)%nat -> rd' (a + Z.of_nat j) = Some (nth j (name ++ [0]) 0)) ->
  (forall j, (length name < j < 16)%nat -> rd' (a + Z.of_nat j) = rd (a + Z.of_nat j)) ->
  pf_nm rd' a name.
Proof.
intros rd rd' a nm name f Hf Henc Hl Hn0 Hr Hnew Hold.
pose proof (pfa8b_cstr_len _ _ _ Henc) as Lf.
assert (Lz : length (seg_spec.zb (name ++ [0])) = S (length name))
  by (unfold seg_spec.zb; rewrite length_map, length_app; cbn [length]; lia).
assert (Hr' : Forall (fun z => 0 <= z < 256) name)
  by (rewrite Forall_forall in *; intros z Hz; specialize (Hr z Hz); lia).
exists (pfa8b_splice 0 (seg_spec.zb (name ++ [0])) f). split.
- intros j Hj. rewrite pfa8b_splice_len in Hj by lia.
  destruct (Nat.le_gt_cases j (length name)) as [Hjn|Hjn].
  + rewrite pfa8b_splice_nth_in by lia. rewrite Nat.sub_0_r. rewrite Hnew by lia. f_equal.
    unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map, length_app; cbn [length]; lia).
    rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    symmetry. apply Z.mod_small.
    destruct (Nat.lt_ge_cases j (length name)) as [Hj1|Hj1].
    * rewrite app_nth1 by exact Hj1. rewrite Forall_forall in Hr'. apply Hr'. apply nth_In. exact Hj1.
    * rewrite app_nth2 by exact Hj1. replace (j - length name)%nat with 0%nat by lia. cbn [nth]. lia.
  + rewrite pfa8b_splice_nth_out by lia. rewrite Hold by lia. exact (Hf j ltac:(lia)).
- apply pfa8b_cstr_splice0; [exact Lf | lia | exact Hn0 | exact Hr'].
Qed.

Ltac pfj_in := cbn [a5_FI PF_SL PF_RM In app]; repeat (first [left; reflexivity | right]).
(* the callee-saved registers (YG0d.acallee_saved) *)
Definition pfj_KL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Section d. Context {rc : YM05.RunCeil}.
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
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* arodata_okP across a step whose two written ranges miss the image and [0x10000, kImgEnd) (the read-only window
   RLO_A .. RHI_A lies there), with no hypothesis on the instance *)
Lemma pfj_arodata : forall (rd rd' : reader) d L lo hi,
  pfk_keep rd rd' d L lo hi -> pfk_noimg d L lo hi ->
  (forall a, 0x10000 <= a < kImgEnd -> ~ (d <= a < d + L) /\ ~ (lo <= a < hi)) ->
  arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros rd rd' d L lo hi K NI NL HR a Ha Ho He.
assert (Hn : (~ (d <= a < d + L) /\ ~ (lo <= a < hi)) /\ 0 <= a < 2 ^ 64).
{ destruct Ha as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    split; [exact (NI a Hi) | pose proof (pa_segs_low a Hi) as Hl; unfold kLowMemEnd in Hl; lia].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. split; [apply NL; unfold kImgEnd; lia | lia]. }
destruct Hn as ([N1 N2] & Hr). unfold pfk_keep in K. rewrite (K a Hr N1 N2). exact (HR a Ha Ho He).
Qed.

(* cur_name and buf are addressable at the line scope (segment A7's pf_a7_d.v a7_addr_buf, commit
   0c85038238f5, for both objects; the hull from PaLibF's shadow_hull_vis_of_frame) *)
Lemma pfj_addr_frame : forall v pos lyc Sc (Wc : world SEGS) mem md q n,
  AR SEGS B lyc Sc Wc mem md -> In (5, pos) (frames Sc) -> lyc = p_ly v -> a5_G v pos ->
  pf_fsh (rdW Wc mem) (pf_SH v pos) PF_SC_LINE ->
  ((pf_F v pos + 32 <= q /\ q + n <= pf_F v pos + 48) \/ (pf_F v pos + 64 <= q /\ q + n <= pf_F v pos + 576)) ->
  0 < n -> sa_addr (rdW Wc mem) q n.
Proof.
intros v pos lyc Sc Wc mem md q n HAR Hin Hly G HF Hq Hn.
pose proof G as (GA & GB & GC & GD & GE & GF & GG & GH & GI & GJ & GK & GL).
assert (HF8 : pf_F v pos mod 8 = 0).
{ pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D. rewrite GH, Z.add_0_r in D. rewrite D.
  replace (32 * (pf_F v pos / 32)) with ((4 * (pf_F v pos / 32)) * 8) by lia. apply Z_mod_mult. }
pose proof alloc_ceiling_lt as HC.
split; [lia|]. split; [lia|].
split; [apply (amem_range_sub_app (pf_F v pos) 2048); [exact GI | lia | lia | lia | lia]|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
  rewrite (HF ((x - pf_F v pos) / 8)).
  + f_equal. apply pfj_shb0. destruct Hq as [Hq|Hq]; [left | right];
      (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  + split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc mem md 5 pos); [exact HAR | exact Hin | | | exact Hn];
    rewrite Hly; change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048; lia.
Qed.

(* pf_base after a step or a call whose writes are [d, d + L) -- 4 bytes of the block c past its first 8, or a
   range of cur_name -- and the window [lo, hi) of a callee below s1 (or nothing), with the journal at the new
   state: every fact of pf_base is outside both, by the pf_a8b_k.v transport. arodata_okP goes by pfj_arodata, so
   no VRO; sa_ssp by the stack-protector cells lying in [0x10000, kImgEnd), so no SSPX. The FP state may change
   (fa to fb), the rounding mode at fb being a premise. *)
Lemma pfj_move : forall (fa fb : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX memc mdc rX' memc' mdc' d L lo hi,
  pf_base (fx := fa) B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  pfk_keep (rdW Wc memc) (rdW Wc memc') d L lo hi -> 0 <= L ->
  ((p_c v + 8 <= d /\ d + L <= p_c v + seg_spec.SEG_C_SIZE) \/
   (pf_F v pos + 32 <= d /\ d + L <= pf_F v pos + 64)) ->
  ((lo = 0 /\ hi = 0) \/ (alloc_ceiling + 8 <= lo /\ hi <= pf_s1 v)) ->
  pf_rg rX' (a5_FI B v) -> sa_frm0 (fx := fb) ->
  pf_base (fx := fb) B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE.
Proof.
intros fa fb v pos lyc Sc Wc rX memc mdc rX' memc' mdc' d L lo hi HB HJ' K HL HD HW HRG' HFRM'.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin5 & G & _ & _).
pose proof G as (GA & GB & GC & GD & GE & GF & GG & GH & GI & GJ & GK & GL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & Hly' & HSf & HPERM & HSV & HFL & _ & _).
pose proof HOBJ as (HTS & HTA & HTH & HCA & HCH & HCAT & HLIT & HROD & HSSP).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (HRP & _)) & _).
pose proof HRP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDISJ & _).
pose proof HCH as (bc & mc & Hinc & Hbc1 & Hbc2).
pose proof HTH as (bt & mt & Hint & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hinc) as (_ & Hbc4096 & Hbcceil & Hbcapp & _ & _ & Hmc).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hint) as (_ & Hbt4096 & Hbtceil & Hbtapp & _ & _ & Hmt).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrc]. pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mc 5 pos HAR Hinc Hin5) as Sc5.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bt mt 5 pos HAR Hint Hin5) as St5.
pose proof (blk_off_imgP B _ _ _ _ _ bc mc HAR Hinc) as Oc.
pose proof (frm_off_imgP B _ _ _ _ _ 5 pos HAR Hin5) as OF.
unfold zdisjoint in Sc5, St5. cbn [fst snd] in Sc5, St5.
rewrite Hly in Sc5, St5, OF. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Sc5, St5, OF.
change (fs_frame_bytes 5) with 2048 in Sc5, St5, OF.
unfold off_img in Oc, OF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbcapp, Hbtapp, GI.
unfold sa_disj in HDISJ. unfold pf_len in Hbt2.
pose proof (pfa8b_str_end_span (p_t v) (p_s v)) as Hspan. unfold str_end in Hspan.
pose proof (Z.mod_pos_bound (p_t v + Z.of_nat (length (p_s v))) 8 ltac:(lia)) as Hm8.
(* a range apart from the block's tail [c + 8, c + 16616), from cur_name's [F + 32, F + 64) and from the window *)
assert (AP : forall q n, 0 <= q -> 0 <= n ->
  (p_c v + seg_spec.SEG_C_SIZE <= q \/ q + n <= p_c v + 8) ->
  (pf_F v pos + 64 <= q \/ q + n <= pf_F v pos + 32) ->
  (q + n <= alloc_ceiling + 8 \/ pf_s1 v <= q) -> pfk_apart q n d L lo hi).
{ intros q n Hq Hn Hc Hf Hw. unfold pfk_apart. clear - HD HW Hq Hn Hc Hf Hw. split.
  - destruct HD as [[H1 H2] | [H1 H2]]; lia.
  - destruct HW as [[-> ->] | [H1 H2]]; lia. }
assert (NI : pfk_noimg d L lo hi).
{ intros x Hx. pose proof (pa_segs_low x Hx) as Hxl. split.
  - intros Hdx. destruct HD as [[H1 H2] | [H1 H2]].
    + apply (blk_img SEGS B LAWS _ _ _ _ _ bc mc x HAR Hinc); [clear - H1 H2 Hdx Hbc1 Hbc2 Hrc; lia | exact Hx].
    + apply (frm_img SEGS B LAWS _ _ _ _ _ 5 pos x HAR Hin5); [|exact Hx].
      rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048.
      clear - H1 H2 Hdx. lia.
  - clear - HW Hxl C1 C5. destruct HW as [[-> ->] | [H1 H2]]; lia. }
assert (NS : pfk_noshadow d L lo hi).
{ intros x Hx. unfold kLowMemEnd, kHighMemBeg in Hx.
  split; [|clear - HW Hx C1; destruct HW as [[-> ->] | [H1 H2]]; lia].
  intros Hdx. clear - HD Hdx Hx Hbcapp GI Hbc1 Hbc2 Hrc. destruct HD as [[H1 H2] | [H1 H2]]; lia. }
assert (NL : forall a, 0x10000 <= a < kImgEnd -> ~ (d <= a < d + L) /\ ~ (lo <= a < hi)).
{ intros a Ha. unfold kImgEnd in Ha. split; [|clear - HW Ha C1; destruct HW as [[-> ->] | [H1 H2]]; lia].
  intros Hdx. clear - HD Hdx Ha Oc OF Hbc1 Hbc2 Hrc. destruct HD as [[H1 H2] | [H1 H2]]; lia. }
(* the objects apart from both written ranges, each from the separation facts it needs *)
assert (AT : pfk_apart (p_t v) (Z.of_nat (length (p_s v)) + 8) d L lo hi).
{ apply AP; [clear - Hbt1 Hbt4096; lia | clear; lia | clear - HDISJ Hspan Hm8; lia
  | clear - St5 Hbt1 Hbt2 Hrt; lia | clear - Hbt2 Hrt Hbtceil; lia]. }
assert (AG : pfk_apart gotwA 8 d L lo hi).
{ unfold gotwA. apply AP; [clear; lia | clear; lia | clear - Oc Hbc1 Hbc2 Hrc; lia | clear - OF; lia
  | clear - C1; lia]. }
assert (AH : pfk_apart guardA 8 d L lo hi).
{ unfold guardA. apply AP; [clear; lia | clear; lia | clear - Oc Hbc1 Hbc2 Hrc; lia | clear - OF; lia
  | clear - C1; lia]. }
assert (AFL : pfk_apart (pf_F v pos + 2048 - 8) 8 d L lo hi).
{ apply AP; [clear - GF; lia | clear; lia | clear - Sc5 Hbc1 Hbc2 Hrc; lia | clear; lia | clear - GG; lia]. }
assert (ASH : pfk_apart (pf_SH v pos) 144 d L lo hi).
{ apply AP; [clear - GK C5; lia | clear; lia | clear - Hbcapp Hbc1 Hbc2 Hrc GK GL C2 C5; lia
  | clear - GI GK GL C2 C5; lia | clear - GL C1 C2; lia]. }
pose proof (pfj_arodata _ _ d L lo hi K NI NL HROD) as HROD'.
clear HD HW HDISJ St5 Sc5 Oc OF Hbcapp Hbtapp GI NL.
assert (Hpo : pf_obj B v lyc Sc (rdW Wc memc')).
{ refine (conj _ (conj _ (conj HTH (conj _ (conj HCH (conj _ (conj _ (conj _ _)))))))).
  - apply (pfk_sa_str _ _ d L lo hi _ _ K HTS); [lia | lia | exact AT].
  - apply (pfk_sa_addr _ _ d L lo hi _ _ K NS HTA); [lia | unfold pf_len; lia].
  - apply (pfk_sa_addr _ _ d L lo hi _ _ K NS HCA); [lia | lia].
  - exact (pfk_sa_cat B _ _ d L lo hi _ K NI NS HCAT).
  - intros x Hx. exact (pfk_sa_lit B _ _ d L lo hi _ _ K NI NS (HLIT x Hx)).
  - exact HROD'.
  - apply (pfk_sa_ssp _ _ d L lo hi _ _ K HSSP); unfold gotwA, guardA in *; try lia; assumption. }
split; [exact HCX|].
split.
{ refine (conj HJ' (conj Hly' (conj HSf (conj HPERM (conj _ (conj _ (conj HFRM' HRG'))))))).
  - apply (pfk_pf_saved _ _ d L lo hi (pf_sp0 v) (p_regs v) K HSV); [lia | lia | apply AP; lia].
  - change (fs_frame_bytes 5) with 2048 in *.
    rewrite (pfk_rdword _ _ d L lo hi (pf_F v pos + 2048 - 8) K); [exact HFL | lia | lia | exact AFL]. }
split; [exact Hpo|].
split.
- apply (pfk_pf_sl _ _ d L lo hi (pf_s1 v) (PF_SL v pos) K HSL). unfold PF_SL.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [lia | split; [lia | apply AP; lia]]).
- apply (pfk_pf_fsh _ _ d L lo hi (pf_SH v pos) PF_SC_LINE K HFSH); [lia | lia | exact ASH].
Qed.

Section c. Context {fx : YK11.FPState}.
Let RUNTO := paj_run_to B LAWS.
Lemma pfa8b_join : forall n : nat, HA_TAIL B n -> H_A8B_JOIN (fx := fx) B n.
Proof.
intros n HAT. unfold H_A8B_JOIN.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i INV.
pose proof INV as (HB & HMID & HST0 & HSTR & HINB & HNL & HI & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin5 & G & HFP & HSHP).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFIR.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & (f0 & HSf) & HPERM & HSV & HFL & HFRM & _).
pose proof HOBJ as (HTS & HTA & HTH & HCA & HCH & HCAT & HLIT & HROD & HSSP).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPF as (HRP & _).
pose proof HRP as (_ & Hc16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDISJ & _).
clear HRP HPF fe.
pose proof HST0 as (HRC & HNM & HCNT).
pose proof G as (GA & GB & GC & GD & GE & GF & GG & GH & GI & GJ & GK & GL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (EG : seg_spec.RC_GEN = 16608) by reflexivity. assert (ES : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ER : seg_spec.RS_SEEN_GEN = 352) by reflexivity. assert (EO : SHADOW_OFF = 2147450880) by reflexivity.
set (s1 := pf_s1 v) in *. set (sp0 := pf_sp0 v) in *. set (c := p_c v) in *. set (F := pf_F v pos) in *.
(* the block c *)
destruct HCH as (bc & mc & Hinc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hinc) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
pose proof (pfj_nseg _ _ _ HRC) as Hn32.
pose proof (pfj_gen_range _ _ _ HRC) as Hg.
assert (Hi32 : (i < 32)%nat) by lia.
assert (Hri : c <= seg_spec.rseg_addr c i <= c + 11036)
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE; lia).
set (ri := seg_spec.rseg_addr c i) in *.
assert (Hri4 : ri mod 4 = 0).
{ unfold ri, seg_spec.rseg_addr, seg_spec.RSEG_SIZE.
  pose proof (Z.div_mod c 16 ltac:(lia)) as Dc.
  replace (c + 356 * Z.of_nat i) with ((4 * (c / 16) + 89 * Z.of_nat i) * 4) by lia. apply Z_mod_mult. }
assert (EN : seg_spec.RC_N = 11392) by reflexivity.
(* the registers and slots the seed reads *)
assert (R9 : getr rX 9 = w64 s1) by (exact (a5_rg_get rX _ 9 s1 HFIR ltac:(pfj_in))).
assert (R22 : getr rX 22 = w64 SHADOW_OFF) by (exact (a5_rg_get rX _ 22 SHADOW_OFF HFIR ltac:(pfj_in))).
assert (R13 : getr rX 13 = w64 (shadow_addr (c + seg_spec.RC_GEN)))
  by (exact (a5_rg_get rX _ 13 _ HRG ltac:(pfj_in))).
assert (R20 : getr rX 20 = w64 ri) by (exact (a5_rg_get rX _ 20 _ HRG ltac:(pfj_in))).
assert (R24 : getr rX 24 = w64 c) by (exact (a5_rg_get rX _ 24 _ HRG ltac:(pfj_in))).
assert (K40 : rdword (rdW Wc memc) (s1 + 0x40) = Some (c + seg_spec.RC_GEN))
  by (exact (proj1 (Forall_forall _ _) HSL (0x40, c + seg_spec.RC_GEN) ltac:(pfj_in))).
assert (K50 : rdword (rdW Wc memc) (s1 + 0x50) = Some (F + PF_O_CN))
  by (exact (proj1 (Forall_forall _ _) HSL (0x50, F + PF_O_CN) ltac:(pfj_in))).
pose proof (pfq_rd32_gen _ _ _ HRC) as KG.
assert (KP : forall a, ri + 0x160 <= a < ri + 0x164 -> apresent (w_H Wc) memc a)
  by (intros a Ha; apply (proj1 (Hbcpres a ltac:(lia)))).
pose proof (pfa8b_jseed (fx := fx) Wc rX memc s1 c ri (F + PF_O_CN) (rc_gen cf) R9 R13 R20 R22 R24
  ltac:(lia) ltac:(lia) GE ltac:(lia) ltac:(lia) Hc16 ltac:(lia) ltac:(lia) Hri4
  ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; rewrite Zplus_mod, GH; reflexivity) Hg ltac:(lia)
  K40 K50 KG KP) as HS.
assert (HEI : img_env VAL A_LIM (pfj_E rX (F + PF_O_CN) (rc_gen cf))) by apply pfj_E_img.
pose proof (pfj_E_agree rX (F + PF_O_CN) (rc_gen cf)) as HA0.
pose proof (pfj_E_reg rX (F + PF_O_CN) (rc_gen cf)) as EE.
pose proof (pfj_E32 rX (F + PF_O_CN) (rc_gen cf)) as E32.
pose proof (pfj_E33 rX (F + PF_O_CN) (rc_gen cf)) as E33.
revert HS HEI HA0 EE E32 E33. generalize (pfj_E rX (F + PF_O_CN) (rc_gen cf)) as E.
intros E HS HEI HA0 EE E32 E33.
assert (E20 : ew E 20 = Z_to_bv 64 ri) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = Z_to_bv 64 c) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (UB : U E pfq_Bx = SHADOW_OFF) by (unfold pfq_Bx; apply U_atom; [exact E22 | lia]).
assert (U24 : U E (SOff 24 0) = c) by (apply U_atom; [exact E24 | lia]).
assert (U20 : U E (SOff 20 0) = ri) by (apply U_atom; [exact E20 | lia]).
pose proof HCA as (_ & _ & _ & HRAc & _).
assert (HAPP : forall x, c <= x < c + seg_spec.SEG_C_SIZE -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbcapp. lia. }
assert (SHOK : sh_ok SEGS pfq_Bx pfj_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pfj_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H Wc) memc E pfq_Bx 24%nat c seg_spec.SEG_C_SIZE c
      seg_spec.RC_GEN (seg_spec.RC_GEN + 8) HRAc UB U24); [lia | lia |].
    intros x Hx. apply HAPP. lia.
  - apply (shent_ok_of_range SEGS (w_H Wc) memc E pfq_Bx 20%nat c seg_spec.SEG_C_SIZE ri
      seg_spec.RS_SEEN_GEN (seg_spec.RS_SEEN_GEN + 8) HRAc UB U20); [lia | lia |].
    intros x Hx. apply HAPP. lia. }
unfold cfg_at.
(* 0x889b4 .. 0x889ec: checks #38 and #39 (both granules covered), seg[i].seen_gen = c->gen, the snprintf
   arguments; the token run stops at PROV2's pc 0x889f0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_PROV2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 20%nat) (b := ri);
    [reflexivity | rewrite E20; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pfa8b_fp_block; lia.
  - exists bc, mc. split; [exact Hinc | lia]. }
(* the run wrote seg[i].seen_gen only, and kept every present byte *)
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ri + 352 <= a < ri + 356) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms)
    (fun a' => ri + 352 <= a' < ri + 356) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
    [lia | lia | rewrite E20, unsigned_lit_small in Hrr by lia; lia]. }
assert (KP1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* 0x889f0: the jal to the snprintf trampoline *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 20%nat) (b := ri);
    [reflexivity | rewrite E20; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pfa8b_fp_block; lia.
  - exists bc, mc. split; [exact Hinc | lia]. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms)) (mrestrict _ (ms_mem ?m2)) |- _ =>
  rename HFx into HFr2; rename m2 into ms2 end.
lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into HG2 end.
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (ri + 352 <= a < ri + 356) -> rdW Wc (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha Hn. rewrite <- (KM1 a Ha Hn).
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms) (ms_mem ms2)
    (fun a' => ri + 352 <= a' < ri + 356) HFr2); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
    [lia | lia | rewrite E20, unsigned_lit_small in Hrr by lia; lia]. }
assert (KP2 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG2 (KP1 a Ha))).
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdv := m) in * end. clearbody mdv.
(* the written seen_gen bytes, from the call state's region 2 *)
assert (HW2 : sa_bytes (rdW Wc (ms_mem ms2)) (ri + seg_spec.RS_SEEN_GEN) (Mem.le4 (Z_to_bv 64 (rc_gen cf)))).
{ pose proof (st_ok_region_nth (segs := SEGS) E _ _ 2%nat _ HS eq_refl) as Hr.
  pose proof (field_of_region_any E _ 20%nat ri _ _ _ _ _ 352 4%N (SExt true 32 (SOff 33 0)) Hr
    ltac:(rewrite E20; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(lia)) as V.
  cbn [ms_mem restrict] in V.
  assert (Hv : bv_unsigned (sv_denot E (SExt true 32 (SOff 33 0))) mod 2 ^ (8 * Z.of_N 4) = rc_gen cf).
  { change (bv_unsigned (sv_denot E (SExt true 32 (SOff 33 0)))) with (U E (SExt true 32 (SOff 33 0))).
    rewrite U_SExt, (U_atom E 33 (rc_gen cf) E33) by lia.
    change (8 * Z.of_N 4) with 32. change (Z.of_N 32) with 32. exact (YI67.sext32_low (rc_gen cf) Hg). }
  rewrite Hv in V. change (N.to_nat 4) with 4%nat in V. rewrite ER.
  exact (pfq_sa_bytes_le4 SEGS (w_H Wc) (ms_mem ms2) (ri + 352) (rc_gen cf) V Hg). }
pmkst HS.
prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
prreg HS (12%bv : bv 5) N12. prreg HS (13%bv : bv 5) N13.
pose proof (regs_kept_of_st_ok SEGS E _ (restrict (w_H Wc) ms2) rX [] pfj_KL HS HA0
  ltac:(vm_compute; reflexivity)) as HK2.
cbn [ms_regs restrict] in HK2.
set (regsT := ms_regs ms2) in *. set (memT := ms_mem ms2) in *.
assert (HP2 : aregs_preserved rX regsT) by (apply aregs_preserved_eqs; apply HK2; cbn; tauto).
assert (R2T : getr regsT 2 = w64 s1)
  by (rewrite (HK2 2%bv ltac:(cbn; tauto)); exact (a5_rg_get rX _ 2 s1 HFIR ltac:(pfj_in))).
assert (R3T : getr regsT 3 = w64 (as_gp B))
  by (rewrite (HK2 3%bv ltac:(cbn; tauto)); exact (a5_rg_get rX _ 3 _ HFIR ltac:(pfj_in))).
assert (R4T : getr regsT 4 = w64 (as_tp B))
  by (rewrite (HK2 4%bv ltac:(cbn; tauto)); exact (a5_rg_get rX _ 4 _ HFIR ltac:(pfj_in))).
assert (Hsp2 : spZ regsT = sp0 + (s1 - sp0)) by (unfold spZ; rewrite R2T; unfold w64; rewrite unsigned_lit_small by lia; lia).
rewrite E32 in N10.
assert (R25 : getr rX 25 = w64 np) by (exact (a5_rg_get rX _ 25 np HRG ltac:(pfj_in))).
rewrite (EE 25%nat 25%bv eq_refl), R25 in N13.
assert (HFSV : seg_litA_rc F_s = 0x21340) by (vm_compute; reflexivity).
assert (E276 : ew E 276 = w64 (seg_litA_rc F_s)).
{ rewrite (img_env_atomP E 276%nat HEI) by (unfold A_TEXT, A_LIM; lia).
  change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64; f_equal; vm_compute; reflexivity. }
rewrite E276 in N12.
(* the cut's facts at the call state: the run wrote 4 bytes of the block c past its first 8 *)
assert (K2 : pfk_keep (rdW Wc memc) (rdW Wc memT) (ri + 352) 4 0 0)
  by (intros a Ha Hn _; apply KM2; [exact Ha | intros H; apply Hn; lia]).
pose proof (pfj_move fx fx v pos lyc Sc Wc rX memc mdc regsT memT mdv (ri + 352) 4 0 0 HB HJ K2 ltac:(lia)
  ltac:(left; lia) ltac:(left; split; reflexivity) (a5_rg_pres rX regsT _ HP2 (a5_FI_cs B v) HFIR) HFRM) as HB2.
pose proof HB2 as (_ & _ & HOBJ2 & HSL2 & HFSH2).
pose proof HOBJ2 as (_ & _ & _ & _ & _ & _ & HLIT2 & HROD2 & HSSP2).
pose proof (proj1 HJ) as HAR2.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mc 5 pos HAR Hinc Hin5) as HSEP.
unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite Hly in HSEP.
change (frame_addr (p_ly v) 5 pos) with F in HSEP. change (fs_frame_bytes 5) with 2048 in HSEP.
pose proof (frm_off_imgP B _ _ _ _ _ 5 pos HAR Hin5) as OF.
rewrite Hly in OF. change (frame_addr (p_ly v) 5 pos) with F in OF. change (fs_frame_bytes 5) with 2048 in OF.
unfold off_img in OF. unfold PF_O_BUF, PF_O_CN in *. unfold pf_inb in HINB.
assert (HSTR2 : sa_str (rdW Wc memT) np name).
{ apply (pfk_sa_str _ _ (ri + 352) 4 0 0 np name K2 HSTR); [lia | lia |].
  unfold pfk_apart. split; [destruct HSEP; lia | lia]. }
pose proof (pfa8b_bytes_range_aview _ _ _ _ _ HSTR) as HNB.
assert (HN0 : ~ In 0 name) by (exact (proj2 (proj1 HSTR))).
assert (Hsn : sn_len (16 - 1) name = Z.of_nat (length name) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
  rewrite length_app, firstn_all2 by lia. cbn [length]. lia. }
pose proof (pfa8b_o_ok v GC) as (Ho16 & Ho0 & Ho1).
assert (Hra : YK0s.ret_ok (getr regsT 1)) by (rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (pfa8b_str_end_span np name) as Hspn. unfold str_end in Hspn.
pose proof (Z.mod_pos_bound (np + Z.of_nat (length name)) 8 ltac:(lia)) as Hmn.
(* 0x889f0: snprintf(cur_name, 16, "%s", np) at row 4 *)
eapply SRr_bind.
{ apply (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (SIGMA SS___interceptor_trampoline_snprintf)
    (ASNP fx) Wc regsT memT STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0 (F + 32) 16 (seg_litA_rc F_s) name (s1 - sp0) (getr regsT 1) HJ).
  - exact N10.
  - exact N11.
  - exact N12.
  - lia.
  - lia.
  - lia.
  - exact Hsp2.
  - exact Ho16.
  - exact Ho0.
  - unfold CMD_SNP_K, ESTACK. lia.
  - exact R3T.
  - exact R4T.
  - reflexivity.
  - exact Hra.
  - intros a Ha. split.
    + right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite Hly. change (frame_addr (p_ly v) 5 pos) with F. change (fs_frame_bytes 5) with 2048. lia.
    + unfold CMD_SNP_K, ESTACK. lia.
  - intros a Ha _ _. apply (apresent_writable SEGS). apply KP2. apply HFP. lia.
  - apply (amem_range_sub_app F 2048); [exact GI | lia | lia | lia | lia].
  - exact (proj1 (proj2 (proj2 (proj2 (pfj_addr_frame v pos lyc Sc Wc memT mdv (F + 32) 16 HAR2 Hin5 Hly G HFSH2
      ltac:(left; lia) ltac:(lia)))))).
  - exact (proj2 (proj2 (proj2 (proj2 (pfj_addr_frame v pos lyc Sc Wc memT mdv (F + 32) 16 HAR2 Hin5 Hly G HFSH2
      ltac:(left; lia) ltac:(lia))))) ltac:(lia)).
  - apply (pfa8b_off_img_sub F 2048); [exact OF | lia | lia | lia].
  - unfold CMD_IMG_HI, kImgEnd, CMD_SNP_K, ESTACK. lia.
  - exact HSSP2.
  - unfold gotwA. lia.
  - unfold gotwA, CMD_IMG_HI, kImgEnd. lia.
  - unfold guardA. lia.
  - unfold guardA, CMD_IMG_HI, kImgEnd. lia.
  - unfold gotwA, CMD_IMG_LO. lia.
  - unfold guardA, CMD_IMG_LO. lia.
  - pose proof (HLIT2 F_s ltac:(unfold PARSE_FILE_LITS; repeat (first [left; reflexivity | right]))) as HL.
    destruct HL as (HL0 & HLs & HLp & _ & _).
    apply (pfa8b_FR_s_regs _ _ (seg_litA_rc F_s) np name regsT).
    + unfold argZ. assert (Hb13 : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
      rewrite Hb13, N13. unfold w64. apply unsigned_lit_small. lia.
    + exact HL0.
    + rewrite HFSV. unfold CMD_IMG_LO. lia.
    + rewrite HFSV. unfold CMD_GOTW. lia.
    + exact HLs.
    + exact (HLp _ _ _ _ _ HAR2).
    + unfold snp_out. rewrite Hsp2. rewrite HFSV.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia.
    + lia.
    + exact HNB.
    + lia.
    + exact HSTR2.
    + exact (pfj_addr_frame v pos lyc Sc Wc memT mdv np (Z.of_nat (length name) + 1) HAR2 Hin5 Hly G HFSH2
        ltac:(right; lia) ltac:(lia)).
    + apply (amem_range_sub_app F 2048); [exact GI | lia | lia | lia | lia].
    + unfold snp_out. rewrite Hsp2. rewrite <- Hspn.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia.
  - lia.
  - exact (a5_rom B v pos lyc Sc Wc regsT memT mdv PF_SC_LINE HB2).
  - exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP3 & H10' & HBY & HK3 & HPR3 & HSM3).
(* the walk goes on at the FP state fx1 the call returned *)
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx|].
rewrite N1.
clear HFr2 HG2.
pose proof (pfa8b_seed (fx := fx1) 15552 Wc regs2 mem2) as HS3.
assert (HEI3 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
assert (HA3 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
revert HS3 HEI3 HA3. generalize (Eimg (Ereg regs2 [])) as E3. intros E3 HS3 HEI3 HA3.
(* 0x889f4: j 0x88068 (TAIL) *)
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS3 HJ2 PF_TAIL.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?m3)) |- _ =>
  rename HFx into HFr3; rename m3 into ms3 end.
assert (KM3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms3) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E3 _ (w_H Wc) mem2 (ms_mem ms3) (fun _ => False) HFr3);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [] pfj_KL HS3 HA3 ltac:(vm_compute; reflexivity)) as HK4.
cbn [ms_regs restrict] in HK4.
assert (HP4 : aregs_preserved regs2 (ms_regs ms3)) by (apply aregs_preserved_eqs; apply HK4; cbn; tauto).
assert (HPall : aregs_preserved rX (ms_regs ms3))
  by (intros r Hr; rewrite (HP4 r Hr), (HP3 r Hr), (HP2 r Hr); reflexivity).
pmkst HS3.
set (regs3 := ms_regs ms3) in *. set (mem3 := ms_mem ms3) in *.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
(* the bytes the call kept, from the cut's memory *)
assert (K3 : pfk_keep (rdW Wc memT) (rdW Wc mem3) (F + 32) 16 (s1 - 8192) s1).
{ intros a Ha Hn Hw. rewrite KM3 by exact Ha.
  apply HK3; [exact Ha | intros H; apply Hn; rewrite Hsn in H; lia | intros H; apply Hw; unfold CMD_SNP_K, ESTACK in H; lia]. }
(* TAIL at fx1, with the next line's offset and lineno *)
apply (HAT fx1 v pos lyc Sc Wc regs3 mem3 md3 (r_upd cf i (rs_with_gen (rc_gen cf))) (Some i)
  (snprintf_s 16 F_s [AS name]) (pf_next (p_s v) o) (ln + 1) d).
unfold INV_TAIL. split; [|split; [|split; [|split]]].
- exact (pfj_move fx fx1 v pos lyc Sc Wc regsT memT mdv regs3 mem3 md3 (F + 32) 16 (s1 - 8192) s1 HB2 HJ2 K3
    ltac:(lia) ltac:(right; lia) ltac:(right; unfold CMD_SNP_K, ESTACK; lia)
    (a5_rg_pres rX regs3 _ HPall (a5_FI_cs B v) HFIR) (fxrel_frm0 fx fx1 HFRM Hfx)).
- exact (proj2 (proj2 HMID)).
- pose proof (pf_next_skipn_lt (p_s v) o (proj1 HMID)). pose proof (proj1 (proj2 HMID)). lia.
- split; [|split; [|split]].
  + pose proof (pfa8b_rconf_seengen (rdW Wc memc) (rdW Wc memT) c cf i (rc_gen cf) (Mem.le4 (Z_to_bv 64 (rc_gen cf)))
      HRC HI ltac:(lia) ltac:(split; [exact Hg | reflexivity])
      ltac:(intros x Hx Hn; apply KM2; [lia | lia]) HW2) as HRC1.
    destruct HRC1 as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
    pose proof (proj1 Henc) as Hlen.
    apply (pfk_sa_bytes _ _ (F + 32) 16 (s1 - 8192) s1 c bs K3 Hbs); [lia | lia |].
    unfold pfk_apart. split; [destruct HSEP; lia | lia].
  + cbn [pf_cur_ok]. unfold r_upd, r_set_segs. cbn [rc_seg]. rewrite upd_nth_len. exact HI.
  + rewrite (pfa8b_snprintf_name16 name HN0 ltac:(lia)).
    destruct HNM as (f & Hf & Hfe).
    change (pf_F v pos + PF_O_CN) with (F + 32) in *.
    apply (pfj_nm_after (rdW Wc memc) (rdW Wc mem3) (F + 32) nm name f Hf Hfe ltac:(lia) HN0 HNB).
    * intros j Hj. rewrite KM3 by lia.
      pose proof (HBY (Z.of_nat j) ltac:(rewrite Hsn; lia)) as Hb. rewrite Nat2Z.id in Hb. rewrite Hb. f_equal.
      unfold sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. reflexivity.
    * intros j Hj. rewrite KM3 by lia.
      rewrite HK3; [| lia | rewrite Hsn; lia | unfold CMD_SNP_K, ESTACK; lia].
      apply KM2; [lia | destruct HSEP; lia].
  + exact HCNT.
- apply (a5_rg_pres rX regs3 _ HPall).
  + apply Forall_app. split; [apply a5_RL_cs|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
  + refine (a5_rg_incl rX _ _ _ HRG).
    intros x Hx. unfold PF_RL in Hx. cbn [app In pf_cur_ptr] in Hx.
    repeat destruct Hx as [<- | Hx]; try destruct Hx; pfj_in.
Qed.
End c.
End e.
End f.
End d.
