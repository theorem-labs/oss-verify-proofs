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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 172 of its 211 lines of code are new or changed and 414 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: the closed site lemma of the snprintf call at 0x88698 in the join loop of segment
   A11b of reac_segconf_parse_file's walk (VERIFY rule 1j-bis; part of segment A11b's proof, by the G3 walk owner,
   2026-10-30).

   proves no function (kind: segment lemma of reac_segconf_parse_file's walk): no function of the binary is walked
   here; the rule-24 record of reac_segconf_parse_file is the unit's internal record,
   commit dfb49d6ad789, path records/segp/g3-lookup.md (CONFIRMed
   2026-10-30T15:42:08Z, reuse verdict none: written new).

   The call is snprintf(known + kn, 240 - kn, "%s%s", sep, token): d = pf_F v pos + PF_O_KNOWN + pf_kn ti,
   n = 240 - pf_kn ti, the format at seg_litA_rc F_ss, a3 = the separator literal seg_litA_rc (pf_sep ti), a4 = the
   row's token pointer tp, the text T = pf_sep ti ++ pf_tok ti; the call's sp is pf_s1 v and the journal's sp0 is
   pf_sp0 v. pfj_snp_site_ok gives, from the loop-head cut INV_KLOOP, every premise of pf_a8b_t.v's
   pfa8b_aj_snprintf_atSF that is not a register or journal fact. It takes no Section hypothesis.
   - the destination is inside the class-5 frame (awr_byte's in_frames case), below alloc_ceiling and so apart from
     the call's window; it is apart from the block c, so the premise on the walk's footprint is vacuous;
   - its shadow cells are known's 30 cells, all 0 at PF_SC_KN (pf_fsh);
   - the frame is off the image (PaLibH.frm_off_imgP), so every literal (format, separator, token: each in
     [0x10000, kImgEnd) by sa_img and pa_img_range) is apart from the written part and from the window. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_d pf_a5_k pf_a11b_d pf_a11b_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16 YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_t pf_a11b_js pf_a11b_jk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* known's 30 shadow cells 0x64 .. 0x81 are 0 while known is in scope *)
Lemma pfj_shb_known : forall i, 100 <= i < 130 -> pf_shb PF_SC_KN i = 0.
Proof.
intros i Hi. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 72) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 80) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 88) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 92) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 95) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 100) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 130) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

(* snprintf's written bytes and their count when the text fits: sn_bytes N L = L ++ [0] *)
Lemma pfj_sn_fit : forall (N : Z) (L : list Z), (length L <= Z.to_nat N)%nat ->
  sn_len N L = Z.of_nat (length L) + 1 /\ sn_bytes N L = L ++ [0].
Proof.
intros N L HL. unfold sn_len, sn_bytes. rewrite firstn_all2 by exact HL.
rewrite length_app. cbn [length]. split; [lia | reflexivity].
Qed.

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

(* a literal's facts at an AR state: its bytes and NUL, its amem and shadow (sa_pinned), 8 bytes of slack in low
   application memory, and its read span inside [0x10000, kImgEnd) (sa_img, pa_img_range; kImgEnd is 8-aligned) *)
Lemma pfj_lit_facts : forall lyc Sc Wc memc mdc a s,
  AR SEGS B lyc Sc Wc memc mdc -> sa_lit SEGS B (rdW Wc memc) a s ->
  0 < a /\ sa_str (rdW Wc memc) a s /\ sa_addr (rdW Wc memc) a (Z.of_nat (length s) + 1) /\
  amem_range a (Z.of_nat (length s) + 8) /\
  0x10000 <= a /\ 0 <= seg_spec.cstr_span a s /\ a + seg_spec.cstr_span a s <= kImgEnd.
Proof.
intros lyc Sc Wc memc mdc a s HAR (Ha & Hs & Hp & _ & Hi).
pose proof (Hp _ _ _ _ _ HAR) as Haddr.
destruct (Hi a ltac:(lia)) as (Hia & _ & _).
destruct (Hi (a + Z.of_nat (length s)) ltac:(lia)) as (Hie & _ & _).
pose proof (pa_img_range _ Hia) as R1. pose proof (pa_img_range _ Hie) as R2.
pose proof asan_consts as (_ & _ & _ & _ & C5).
unfold seg_spec.cstr_span. unfold kImgEnd in *.
pose proof (Z.div_mod (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M.
split; [exact Ha|]. split; [exact Hs|]. split; [exact Haddr|].
split; [unfold amem_range; left; lia|].
split; [lia|]. split; lia.
Qed.

(* the closed site lemma of the snprintf call at 0x88698 *)
Lemma pfj_snp_site_ok : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti tp (regsT : bvmap 5 word),
  INV_KLOOP B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  rdword (rdW Wc memc) (pin_spec.row_addr catA ti) = Some tp ->
  sa_lit SEGS B (rdW Wc memc) tp (pf_tok ti) ->
  argZ regsT 3 = seg_litA_rc (pf_sep ti) -> argZ regsT 4 = tp -> spZ regsT = pf_s1 v ->
  (forall a, pf_F v pos + PF_O_KNOWN + pf_kn ti <= a < pf_F v pos + PF_O_KNOWN + pf_kn ti + (240 - pf_kn ti) ->
     awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
       (ablocks B (p_ly v) (p_S v)) (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a /\
     ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - RtPFCmd.CMD_SNP_K <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v))) /\
  (forall a, pf_F v pos + PF_O_KNOWN + pf_kn ti <= a < pf_F v pos + PF_O_KNOWN + pf_kn ti + (240 - pf_kn ti) ->
     inFP (seg_spec.RC_PARSE_W (p_c v)) a ->
     (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ pf_sp0 v <= a < ly_top lyc ->
     writable_at SEGS (mrestrict (w_H Wc) memc) a) /\
  amem_range (pf_F v pos + PF_O_KNOWN + pf_kn ti) (240 - pf_kn ti + 8) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_KNOWN + pf_kn ti) (240 - pf_kn ti) /\
  shadow_hull_vis (rdW Wc memc) (pf_F v pos + PF_O_KNOWN + pf_kn ti) (240 - pf_kn ti) /\
  YCbq.off_img (pf_F v pos + PF_O_KNOWN + pf_kn ti) (RtPFShared.sn_len (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti)) /\
  RtPFCmd.CMD_IMG_HI <= pf_sp0 v + (pf_s1 v - pf_sp0 v) - RtPFCmd.CMD_SNP_K /\
  aguard_ok SEGS Wc memc gotwA guardA /\
  RtPFCmd.FR_cmd (rdW Wc memc)
    (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) (pf_F v pos + PF_O_KNOWN + pf_kn ti)
       (RtPFShared.sn_len (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti)))
    (seg_litA_rc F_ss) (map (argZ regsT) [3; 4; 5; 6; 7]) (pf_sep ti ++ pf_tok ti) /\
  Z.of_nat (length (pf_sep ti ++ pf_tok ti)) < 2 ^ 31 - 1 /\
  RtDefs.rt_rom_view SEGS B Wc memc /\
  RtPFShared.sn_len (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti) = Z.of_nat (length (pf_sep ti ++ pf_tok ti)) + 1 /\
  RtPFShared.sn_bytes (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti) = (pf_sep ti ++ pf_tok ti) ++ [0].
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti tp regsT HI Htp HTL E3 E4 Esp.
destruct HI as (HB & _ & _ & _ & _ & Hti & _).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_rom B _ _ _ _ _ _ _ _ _ HB) as HROM.
destruct HB as (_ & _ & HOBJ & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & HC & _ & LI & _ & HSS).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hti10 : (ti <= 10)%nat) by lia.
pose proof (pf_kn_bound ti ltac:(lia)) as Hkn.
pose proof (pf_sep_len ti) as Hsl. pose proof (pf_tok_len ti Hti10) as Htl.
assert (HT : (length (pf_sep ti ++ pf_tok ti) <= 12)%nat) by (rewrite length_app; lia).
destruct (pfj_sn_fit (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti) ltac:(lia)) as [ESL ESB].
assert (Hoff : YCbq.off_img (pf_F v pos) 2048).
{ pose proof (frm_off_imgP B (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as H.
  change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in H. change (fs_frame_bytes 5) with 2048 in H. exact H. }
(* every range inside [0x10000, kImgEnd) is apart from the call's window and from the written part *)
assert (HOUT : forall x w, 0x10000 <= x -> 0 <= w -> x + w <= kImgEnd ->
  Forall (zdisjoint (x, w)) (snp_out CMD_SNP_K (spZ regsT) (pf_F v pos + PF_O_KNOWN + pf_kn ti)
    (sn_len (240 - pf_kn ti - 1) (pf_sep ti ++ pf_tok ti)))).
{ intros x w Hx Hw Hxw. unfold snp_out. rewrite Esp, ESL.
  unfold CMD_SNP_K, ESTACK, kImgEnd, PF_O_KNOWN in *. unfold YCbq.off_img in Hoff.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
(* the three literals *)
pose proof (pfj_lit_facts _ _ _ _ _ _ _ HAR (LI F_ss pf_in_lits_ss)) as (LF1 & LF2 & LF3 & _ & LF5 & _ & _).
pose proof (pfj_lit_facts _ _ _ _ _ _ _ HAR (LI (pf_sep ti) (pf_in_lits_sep ti)))
  as (LS1 & LS2 & LS3 & LS4 & LS5 & LS6 & LS7).
pose proof (pfj_lit_facts _ _ _ _ _ _ _ HAR HTL) as (LT1 & LT2 & LT3 & LT4 & LT5 & LT6 & LT7).
unfold PF_O_KNOWN in *.
split.
{ (* the destination: inside the class-5 frame, below the call's window *)
  intros a Ha. split.
  - unfold awr_byte. right; right; right; left. unfold in_frames.
    exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (p_ly v) 5 pos) with (pf_F v pos). change (fs_frame_bytes 5) with 2048. lia.
  - unfold CMD_SNP_K, ESTACK. lia. }
split.
{ (* the walk's footprint is the block c, which the frame does not meet *)
  intros a Ha Hfp _. exfalso. apply a5_rcw_in in Hfp.
  destruct HC as (b & m & Hb & H1 & H2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
  pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
  change (fs_frame_bytes 5) with 2048 in Hd. lia. }
split.
{ apply (amem_range_sub_app (pf_F v pos) 2048); [exact G9 | lia | lia | lia | lia]. }
split.
{ (* known's shadow cells are 0 *)
  intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)) as MF8.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF32.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  replace (SHADOW_OFF + x / 8) with (pf_SH v pos + (x / 8 - pf_F v pos / 8)) by (rewrite G10; lia).
  rewrite (HFSH (x / 8 - pf_F v pos / 8)) by lia.
  rewrite pfj_shb_known by lia. reflexivity. }
split.
{ apply (shadow_hull_vis_of_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos); [exact HAR | exact Hin | | | lia];
    try change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); try change (fs_frame_bytes 5) with 2048; lia. }
split.
{ rewrite ESL. apply (pfa8b_off_img_sub (pf_F v pos) 2048); [exact Hoff | lia | lia | lia]. }
split.
{ unfold CMD_IMG_HI, CMD_SNP_K, ESTACK, kImgEnd. lia. }
split; [exact HSS|].
split.
{ (* the format "%s%s" with the separator in a3 and the token in a4 *)
  apply (pfj_FR_ss_regs (rdW Wc memc) _ (seg_litA_rc F_ss) (seg_litA_rc (pf_sep ti)) tp (pf_sep ti) (pf_tok ti)
    regsT E3 E4).
  - exact LF1.
  - unfold CMD_IMG_LO. lia.
  - rewrite pf_lit_ss. unfold CMD_GOTW. lia.
  - exact LF2.
  - assert (E5 : Z.of_nat (length F_ss) + 1 = 5) by (rewrite pfj_F_ss_len; reflexivity).
    rewrite E5 in LF3. exact LF3.
  - apply HOUT; [exact LF5 | lia | rewrite pf_lit_ss; unfold kImgEnd; lia].
  - exact LS1.
  - exact (pf_sep_byte ti).
  - lia.
  - exact LS2.
  - exact LS3.
  - exact LS4.
  - apply HOUT; [exact LS5 | exact LS6 | exact LS7].
  - exact LT1.
  - exact (pf_tok_byte ti Hti10).
  - lia.
  - exact LT2.
  - exact LT3.
  - exact LT4.
  - apply HOUT; [exact LT5 | exact LT6 | exact LT7]. }
split; [lia|].
split; [exact HROM|].
split; [exact ESL | exact ESB].
Qed.
End e.
End f.
End d.
