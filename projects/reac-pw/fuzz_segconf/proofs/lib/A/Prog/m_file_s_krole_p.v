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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 242 of its 283 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KROLE, piece kr_s_post: from the inner point KR_POST
   0x8672c (the fold done) to KR_WORDS 0x86750 with i = 0 (lib/A/Prog/m_file_s_krole_m.v). The KROLE segment lane of
   the G2 walk owner's G2, piece agent the KROLE post sub-lane. Nothing is called.

   THE CODE (listing m_file.fuzz_segconf.asan.s): 0x8672c `sd s8,96(s1)` (line + 1 into 96(s1)); 0x86730 s11 = 0;
   0x86734 a0 = a7 + s4 (low + ln); 0x86738 `auipc a1`; 0x8673c `sb zero,0(a0)` (low[ln] = 0, no check); 0x86740
   s7 = &m_key.role (listing object 18); 0x86744 s5 = 80(s1) = WORDS; 0x86748 s10 = s5; 0x8674c s8 = 72(s1) =
   shadow(WORDS).

   THE PROOF: mf_seed at KR_POST (the slots of mf_cells, 144(s1) = the next line, low.i's shadow 0, xs = [low + ln]);
   the slots' write window narrowed to 96(s1) [96, 104); low.i's read-only region dropped and a writable one-byte
   region added at atom 52 = low + ln (ln <= 63, so low + ln lies in low.i). A plain run to 0x8673c; there a0 =
   a7 + s4 is replaced by atom 52 (equal values: a7 = low, s4 = ln); a plain run to 0x86750. The two runs keep every
   byte outside 96(s1) and low[ln] (kept_of_frame), so m_file_k.v's mf_keep_run_s carries the KDISP facts (kr_cx);
   the final state gives 96(s1) = line + 1 and low[ln] = 0 (field_of_region); KR_WORDS_stmt at i = 0 ends it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_s_krole_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the 0x8672c .. 0x86750 stops: 0x8673c (the store at a0 = low + ln) and KR_WORDS *)
Definition KR_P_SB : Z := AF_m_file + 0x880.
(* the bytes the two runs write: 96(s1) (8 bytes from s1 + 96) and low[ln] (the byte b = low + ln) *)
Definition krp_rw (s1 b x : Z) : Prop := (s1 + 96 <= x < s1 + 104) \/ x = b.

(* the line is a prefix of the text left *)
Lemma krp_line_len : forall l, (length (fst (break_nl l)) <= length l)%nat.
Proof.
  induction l as [|b l IH]; cbn; [lia|]. destruct (b =? NL); cbn; [lia|].
  destruct (break_nl l) as [x q]; cbn in *; lia.
Qed.

(* the state's form, computed *)
Ltac krp_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* the run's writes are the journal's: the byte at atom 52 (low + ln) is the side-stack frame's, 96(s1) is in the
   stack window below sp0; every other region is read-only *)
Ltac krp_awr U52 U2 HSTK :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
  | |- awr_ok _ _ _ (YP09.mkRegion (Some 52%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
    eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ _ _ _ 52%nat); [reflexivity | exact U52 | |];
    [ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; eexists 1, _;
      split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia | ]
  | |- awr_ok _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?spx _ _ _ _ _ _ =>
    lazymatch type of U2 with _ = ?s1 =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (s1 - spx));
    [ reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite HSTK; unfold mf_s1 in *; lia
    | cbn [YP09.r_whi]; unfold mf_s1 in *; lia | ] end
  end ].

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
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

Lemma kr_s_post : forall n, KR_WORDS_stmt B n -> KR_POST_stmt B n.
Proof.
intros n WORDS. unfold KR_POST_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KCX RA LOW R20 R24 R17.
pose proof KCX as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & KV & FIN & NP & IEQ).
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcurok & _ & Hline0 & Hline1 & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE Hcurok) as Hcur.
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & _).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
(* ln = kr_ln vl = |kr_low vv| <= 63 *)
assert (Hln : (kr_ln vl <= 63)%nat) by (unfold kr_ln; lia).
assert (Hvl : length vv = vl).
{ destruct KV as (_ & KV2 & _ & KV4). rewrite <- KV4, length_firstn, length_skipn.
  pose proof (krp_line_len rest). unfold mf_line in KV2. lia. }
assert (Hlowl : length (kr_low vv) = kr_ln vl) by (rewrite kr_low_length, Hvl; reflexivity).
(* the seed *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest)
  [frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)] KR_POST true true [] false false [] false CX CORE RB
  (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)]) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) (mf_next p rest) [frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)]) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (E52 : ew E 52 = Z_to_bv 64 (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)))
  by (subst E; exact (mfE_xs regs1 v lyc pos (Some gi) (mf_next p rest) _ 0 ltac:(unfold A_TEXT; lia))).
assert (EW : ew E (A_OBJ MF_WORDS_OBJ) = Z_to_bv 64 SegInstA.wordsA)
  by (subst E; rewrite mfE_img by (unfold A_OBJ, MF_WORDS_OBJ, A_TEXT, A_LIM; lia); rewrite (mf_words_obj VOBJS); reflexivity).
assert (ER : ew E (A_OBJ MF_ROLES_OBJ) = Z_to_bv 64 SegInstA.rolesA)
  by (subst E; rewrite mfE_img by (unfold A_OBJ, MF_ROLES_OBJ, A_TEXT, A_LIM; lia); rewrite (mf_roles_obj VOBJS); reflexivity).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E34, E36.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U52 : bv_unsigned (ew E 52) = frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl))
  by (rewrite E52; apply unsigned_lit_small; lia).
(* the slots' write window: 96(s1) only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 96 104) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 96 104 HR1
      ltac:(intros o Ho; pose proof HR1 as (_ & _ & HW & _); apply HW; cbn; lia))) as HS1 end.
clear HS0 HR1. krp_norm HS1.
(* low.i's read-only region dropped *)
lazymatch type of HS1 with st_ok_pi _ _ _ (mkSS _ _ [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] _ _) _ =>
  pose proof (st_ok_pi_submem E _ _ [r0; r1; r2; r4; r5] HS1 ltac:(cbn [ss_mem]; submem_tac)
    ltac:(vm_compute; reflexivity)) as HS2 end.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
(* low[ln]: a writable byte at atom 52 *)
assert (HS3 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 52%nat) 0 1 0 1 []) HS2 ltac:(vm_compute; reflexivity)).
clear HS2.
lapply HS3; clear HS3; [intros HS3|].
2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U52. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. cbn [restrict ms_mem mkst]. apply (apresent_writable SEGS).
    destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & HFpres & _).
    change (fs_frame_bytes 1) with 128 in HFpres.
    apply (proj1 (HFpres (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl) + o) ltac:(lia))). }
lapply HS3; clear HS3; [intros HS3|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U52, ?U2, ?U8, ?U34, ?U36.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
    unfold mf_s1, SHADOW_OFF in *.
    repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
unfold mf_at.
(* 0x8672c .. 0x86738: a plain run to the store at a0 = low + ln *)
paj_run_to_sh RUNTOP HS3 HJ KR_P_SB.
{ krp_awr U52 U2 HSTK. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
(* a0 = a7 + s4 = low + ln: atom 52 *)
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms1 (10%bv : bv 5) HS3) as Q10.
lazymatch type of Q10 with _ = sv_denot _ (sr_get (ss_regs ?ss) _) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
  change (sr_get (ss_regs ss) (10%bv : bv 5)) with e in Q10 end.
assert (D10 : sv_denot E (SOff 52 0) = getr (ms_regs (restrict (w_H Wc) ms1)) (10%bv : bv 5)).
{ change (getr (ms_regs (restrict (w_H Wc) ms1)) (10%bv : bv 5)) with (getr (ms_regs ms1) (10%bv : bv 5)).
  rewrite Q10, denot_lit_U, denot_lit_U. f_equal.
  rewrite U_SAlu, !U_SOff, E52, (EE 17%nat 17%bv eq_refl), R17, (EE 20%nat 20%bv eq_refl), R20. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  rewrite (zcanon_id (frame_addr lyc 1 pos + 32)) by (unfold M64; lia).
  rewrite (zcanon_id (Z.of_nat (kr_ln vl))) by (unfold M64; lia).
  cbn [zalu_raw]. f_equal; lia. }
pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 52 0) HS3 ltac:(vm_compute; reflexivity) D10) as HS4.
clear HS3 Q10 D10. krp_norm HS4.
(* 0x8673c .. 0x8674c: low[ln] = 0, s7, s5, s10, s8; a plain run to KR_WORDS *)
paj_run_to_sh RUNTOP HS4 HJ KR_WORDS.
{ krp_awr U52 U2 HSTK. }
rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
(* every byte outside 96(s1) and low[ln] is kept *)
set (RW := krp_rw (mf_s1 (mv_sp v)) (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl))).
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha HnR.
  lazymatch type of HFr1 with frame_of _ ?rs _ _ =>
    refine (kept_of_frame E rs (w_H Wc) memc (ms_mem ms1) RW HFr1 _ a Ha HnR) end.
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. unfold RW, krp_rw.
  repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hr;
    first [ lia | rewrite U52 in Hr; right; lia | rewrite U2 in Hr; left; lia ] |]); destruct Hinw. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms2) a = rdW Wc (ms_mem ms1) a).
{ intros a Ha HnR.
  lazymatch type of HFr2 with frame_of _ ?rs _ _ =>
    refine (kept_of_frame E rs (w_H Wc) (ms_mem ms1) (ms_mem ms2) RW HFr2 _ a Ha HnR) end.
  intros bb wlo whi x Hinw Hr. vm_compute in Hinw. unfold RW, krp_rw.
  repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hr;
    first [ lia | rewrite U52 in Hr; right; lia | rewrite U2 in Hr; left; lia ] |]); destruct Hinw. }
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms2) a = rdW Wc memc a)
  by (intros a Ha HnR; rewrite (K2 a Ha HnR); exact (K1 a Ha HnR)).
clear K1 K2.
(* the final state: 96(s1) = line + 1, low[ln] = 0 *)
lazymatch type of HS4 with st_ok_pi _ _ _ ?ssx _ =>
  pose proof (st_ok_pi_region_nth E ssx _ 2 _ HS4 eq_refl) as HRs;
  pose proof (st_ok_pi_region_nth E ssx _ 0 _ HS4 eq_refl) as HR52 end.
cbn [restrict ms_mem] in HRs, HR52.
assert (V96 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (mf_s1 (mv_sp v) + 96) (N.to_nat 8) (line + 1)).
{ eapply (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 96 8%N _ (line + 1) HRs);
    [ exact U2 | cbn; repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia ].
  rewrite denot_lit_U. f_equal. apply (U_atom E 24 (line + 1)); [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia]. }
change (N.to_nat 8) with 8%nat in V96.
assert (V0 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl) + 0)
  (N.to_nat 1) 0).
{ eapply (field_of_region E _ 52%nat (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)) _ _ _ _ _ 0 1%N _ 0 HR52);
    [ exact U52 | cbn; repeat (first [left; reflexivity | right]) | | cbn; lia | cbn; lia ].
  first [ reflexivity | rewrite denot_lit_U, U_SLit; reflexivity ]. }
clear HRs HR52.
assert (A0 : rdW Wc (ms_mem ms2) (frame_addr lyc 1 pos + 32 + Z.of_nat (kr_ln vl)) = Some 0).
{ pose proof (V0 0%nat ltac:(cbn; lia)) as V00. cbn [Z.of_nat] in V00. rewrite !Z.add_0_r in V00.
  unfold aview. rewrite V00. vm_compute. reflexivity. }
(* low[0 .. ln] = h_fold v 64 and its NUL *)
assert (LOW' : kr_low_at lyc pos Wc (ms_mem ms2) (kr_low vv ++ [0])).
{ unfold kr_low_at, sa_zs in LOW |- *. rewrite Hlowl in LOW.
  intros i Hi. rewrite length_app, Hlowl in Hi. cbn [length] in Hi.
  destruct (Nat.ltb_spec i (kr_ln vl)) as [Hlt|Hge].
  - rewrite app_nth1 by lia. rewrite K; [apply LOW; exact Hlt | lia |].
    unfold RW, krp_rw, mf_s1. intros [Hq|Hq]; lia.
  - assert (i = kr_ln vl) by lia. subst i. rewrite app_nth2 by lia. rewrite Hlowl, Nat.sub_diag. cbn [nth].
    exact A0. }
(* the KDISP facts at the new memory (m_file_k.v's run family) *)
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a HR. unfold RW, krp_rw in HR. unfold mf_rw. destruct HR as [Ha|Ha].
  - right; right; right; right; right. unfold mf_s1 in *. lia.
  - right; right; left. lia. }
assert (RWS : mf_rws v RW).
{ intros a HR Hs. unfold RW, krp_rw in HR. destruct HR as [Ha|Ha]; [left; exact Ha|].
  exfalso. unfold mf_s1 in *. lia. }
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & Bc4096 & Bcceil & _).
pose proof CORE as (_ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms2) _ RW MF_LOW_ON (Some gi) mcc
  CX CORE CELLS HJ K RWok RWS) as (CORE' & CELLS' & LOOPf).
{ intros i Hi. apply (mf_val_keep Wc Wc memc (ms_mem ms2) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
  intros kk Hk HR. change (Z.of_nat 1) with 1 in Hk. unfold RW, krp_rw in HR.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, mf_s1 in *. lia. }
{ apply (mf_val_keep Wc Wc memc (ms_mem ms2) RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros kk Hk HR. change (Z.of_nat 8) with 8 in Hk. unfold RW, krp_rw in HR. unfold mf_s1 in *. lia. }
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms2) RW _ _ K);
    [lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
  intros a Ha HR. unfold RW, krp_rw in HR. destruct HR as [Hq|Hq]; [unfold mf_s1 in *; lia|].
  apply (mf_block_apart B lyc Sc Wc memc mdc pos bc mc a HAR Hin Hbc ltac:(unfold seg_spec.SEG_M_SIZE in *; lia)).
  unfold mf_win. left. lia. }
assert (NP' : mf_np v (ms_mem ms2) Wc (mf_next p rest)).
{ unfold mf_np in NP |- *. apply (mf_val_keep Wc Wc memc (ms_mem ms2) RW _ 8 _ K);
    [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact NP].
  intros kk Hk HR. change (Z.of_nat 8) with 8 in Hk. unfold RW, krp_rw in HR. unfold mf_s1 in *. lia. }
pose proof (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj Hn (conj Hne (conj (LOOPf _ _ _ _ _ LOOP)
  (conj KV (conj FIN (conj NP' IEQ))))))))))) as KCX'.
(* the registers at KR_WORDS *)
prreg HS4 (2%bv : bv 5) Q2. prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4. prreg HS4 (8%bv : bv 5) Q8.
prreg HS4 (9%bv : bv 5) Q9. prreg HS4 (18%bv : bv 5) Q18. prreg HS4 (19%bv : bv 5) Q19. prreg HS4 (25%bv : bv 5) Q25.
prreg HS4 (20%bv : bv 5) Q20. prreg HS4 (27%bv : bv 5) Q27.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms2 (23%bv : bv 5) HS4) as Q23.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms2 (26%bv : bv 5) HS4) as Q26.
pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ ms2 (24%bv : bv 5) HS4) as Q24.
lazymatch type of HS4 with st_ok_pi _ _ _ ?ss _ =>
  let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
  let e26 := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
  let e24 := eval vm_compute in (sr_get (ss_regs ss) (24%bv : bv 5)) in
  change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23;
  change (sr_get (ss_regs ss) (26%bv : bv 5)) with e26 in Q26;
  change (sr_get (ss_regs ss) (24%bv : bv 5)) with e24 in Q24 end.
assert (HWv : SegInstA.wordsA = 0xa1880) by reflexivity.
assert (HRv : SegInstA.rolesA = 0x211e0) by reflexivity.
pose proof (mf_denot_shx E (A_OBJ MF_WORDS_OBJ) SegInstA.wordsA 0 EW E32
  ltac:(rewrite HWv; lia) ltac:(lia) ltac:(rewrite HWv; lia)) as D24.
assert (RB' : kr_regs_b B v (ms_regs ms2)).
{ unfold kr_regs_b.
  rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q25, E32, (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl),
    (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 19%nat 19%bv eq_refl), (EE 25%nat 25%bv eq_refl).
  refine (conj R2 (conj R3 (conj R4 (conj R8 (conj R2 (conj eq_refl (conj R19 R25))))))). }
pmkst HS4.
apply (WORDS v lyc Sc Wc (ms_regs ms2) (ms_mem ms2) _ pos mcc gi line p rest ok kl ov vl k vv 0%nat KCX' RB'
  ltac:(lia) LOW' V96 (kr_word_go_0 _)).
- rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
- rewrite Q27. reflexivity.
- rewrite Q23, denot_lit_U. unfold w64. f_equal.
  transitivity SegInstA.rolesA; [exact (U_atom E _ SegInstA.rolesA ER ltac:(rewrite HRv; lia)) | lia].
- rewrite Q26, denot_lit_U. unfold w64. f_equal.
  transitivity SegInstA.wordsA; [exact (U_atom E _ SegInstA.wordsA EW ltac:(rewrite HWv; lia)) | lia].
- rewrite Q24. etransitivity; [exact D24|]. unfold w64. f_equal; cbn [Z.of_nat]; rewrite ?Z.add_0_r; reflexivity.
Qed.
End e.
End f.
End d.
About kr_s_post.
Print Assumptions kr_s_post.
