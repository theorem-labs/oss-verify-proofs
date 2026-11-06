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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 553 of its 607 lines of code are new or changed and 399 lines of the source are left out. *)
(* S_MF_ENTRY, part 3a: m_file on fuzz_segconf.asan (image A, m_file at 0x85ebc) after snprintf returns at 0x86018:
   c->gen++ (0x86018-0x86048, the checked load 0x86028), the *text test (0x8604c-0x86060, the checked load 0x86054,
   `beqz` to the release 0x86e70), the set-up of the spill slots (0x86064-0x860cc) and the hand-offs to MF_EXIT
   (empty text) and MF_HEAD (lib/A/Prog/m_file_m.v). Part 3 (m_file_s_entry_3.v) walks from the cut ENT_LBL to the
   snprintf call and steps it with m_file_s_entry_s.v's mf_snp_step, whose continuation is ent_post here.
   A lane of the G2 walk owner. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN0d YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_m m_file_s_entry_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_1 m_file_s_entry_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* the state after snprintf: the symbolic regions (atom 9 = s1, 22 = s6 = c + 0x2000, 27 = s11 = t, 32 = c->gen,
   33 = the text's first byte): the spill slots 24 .. 160 above s1, c->gen, the text's first byte *)
Definition ent_r_slots : YP09.region := YP09.mkRegion (Some 9%nat) 24 160 24 160 [].
Definition ent_r_gen : YP09.region :=
  YP09.mkRegion (Some 22%nat) 0x3b0 0x3b4 0x3b0 0x3b4 [YP09.mkChunk 0x3b0 (CVal 4 (SOff 32 0))].
Definition ent_r_txt : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ent_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF SB SB 0); (22%nat, PTR 4); (27%nat, PTR 0);
            (32%nat, mkAF 0 (2 ^ 31) 0); (33%nat, mkAF 0 256 0) ] [] [].
Definition ent_ss : sstate := mkSS (AF_m_file + 0x15c) sr_atoms [ent_r_slots; ent_r_gen; ent_r_txt] None ent_facts.
(* the shadow knowledge of the two checks: c->gen's granule (0x86028) and the text's first byte (0x86054) *)
Definition ent_SH : list shent := [ mkSHE 22 0x3b0 0x3b8; mkSHE 27 0 1 ].
Definition EntBx : sv := SOff 18 0.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the callee-saved registers at the snprintf call (ent_lbl_regs without s4, which the null-label arm sets) *)
Definition ent_snp_regs (v : mfv) (pos : Z) (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (mv_sp v) /\ getr regs 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs 18 = w64 SHADOW_OFF /\
getr regs 19 = w64 (frame_addr (mv_ly v) 1 pos) /\
getr regs 21 = w64 (mv_c v) /\ getr regs 22 = w64 (mv_c v + seg_spec.MC_N) /\
getr regs 23 = w64 (mv_c v + seg_spec.MC_READING) /\ getr regs 24 = w64 (frame_addr (mv_ly v) 1 pos) /\
getr regs 26 = w64 (SHADOW_OFF + frame_addr (mv_ly v) 1 pos / 8) /\ getr regs 27 = w64 (mv_t v).

(* the journal from the entry (m_file_k.v's JE) keeps every byte of an entry block outside the mconf block *)
Lemma ent_blk_now : forall v lyc Sc (Wc : world SEGS) mem md pos b m a,
mf_cx B v -> Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem md 0 ->
In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
~ (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) -> rdW Wc mem a = rdW (mv_W v) (mv_mem v) a.
Proof.
intros v lyc Sc Wc mem md pos b m a CX HPerm HJ Hin Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace a with (b + (a - b)) by lia.
apply (F2 b m (a - b)); [exact Hin | apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin | lia |].
intros HF. apply Hn. replace a with (b + (a - b)) by lia. exact (mf_fp_in_block B v _ CX HF).
Qed.

(* the text at any state the journal reaches: its bytes are the entry's, its slack and shadow come from AR *)
Lemma ent_txt_now : forall v lyc Sc (Wc : world SEGS) mem md pos,
mf_cx B v -> Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem md 0 ->
sa_str (rdW Wc mem) (mv_t v) (mv_s v) /\ sa_addr (rdW Wc mem) (mv_t v) (Z.of_nat (length (mv_s v)) + 1).
Proof.
intros v lyc Sc Wc mem md pos CX HPerm HJ.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTS & _ & HTH & _ & _ & HTD & _).
destruct HTH as (bt & mtn & Hbtin0 & Hbtlo & Hbthi).
assert (Hbtin : In (bt, mtn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbtin0).
pose proof (proj1 HJ) as HAR.
assert (Hr : mtn <= req_size mtn) by (unfold req_size; destruct (Z.eqb_spec mtn 0); lia).
pose proof (mfk_span_bounds (mv_t v) (mv_s v)) as HSP.
assert (KT : forall a, mv_t v <= a <= mv_t v + Z.of_nat (length (mv_s v)) -> rdW Wc mem a = rdW (mv_W v) (mv_mem v) a).
{ intros a Ha. apply (ent_blk_now v lyc Sc Wc mem md pos bt mtn a CX HPerm HJ Hbtin0); [lia|].
  unfold sa_disj in HTD. lia. }
split.
- destruct HTS as ((Hz & Hn0) & Htl). split; [split; [|exact Hn0]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KT by lia.
    apply Hz. rewrite length_app. cbn [length]. lia.
  + intros x Hx. apply (AR_block_word_vis SEGS B lyc Sc Wc mem md bt mtn (mv_t v + Z.of_nat (length (mv_s v))) x HAR
      Hbtin); lia.
- apply (mf_heap_addr SEGS B LAWS lyc Sc Wc mem md); [exact HAR | exists bt, mtn; split; [exact Hbtin | lia] | lia].
Qed.

(* the write windows of a run from ent_ss's regions: the spill slots (stack) and c->gen (M_FILE_FP's fifth range,
   inside the mconf block) *)
Ltac ent_awr v U9 U22 Hbcin :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := mf_s1 (mv_sp v) - mv_sp v);
    [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply YCbq.awr_ok_cons_gen with (k := 22%nat);
    [ reflexivity | exact U22
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
      [ eexists; split;
        [ unfold M_FILE_FP; right; right; right; right; left; reflexivity
        | cbn [fst snd]; unfold seg_spec.MC_NKEPT, seg_spec.MC_READING, seg_spec.MC_N in *; lia ]
      | eexists; eexists; split; [exact Hbcin | unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia] ] |] ].

(* the label's text has no NUL: a C string, or the literal "reac-pw.conf" *)
Lemma ent_lab_nul : forall v, mf_cx B v -> ~ In 0 (mf_lab_text (mv_lab v)).
Proof.
intros v CX. pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & _).
destruct (mv_lab v) as [l|]; cbn [mf_lab_text].
- destruct HOS as (_ & ((_ & Hn) & _)). exact Hn.
- assert (Hnb : existsb (Z.eqb 0) S_base = false) by (vm_compute; reflexivity).
  intros H. assert (Hb : existsb (Z.eqb 0) S_base = true)
    by (apply existsb_exists; exists 0; split; [exact H | reflexivity]).
  rewrite Hnb in Hb. discriminate.
Qed.

(* mf_core at the end of the segment: the cut's frame cells and saved registers kept (the runs wrote only the
   spill slots and c->gen, snprintf only c->reading and its window), 112(s1) = FB, and the block holding mf_c1 *)
Lemma ent_core_fin : forall v lyc Sc (Wc : world SEGS) memc mem2 mf mdf pos,
mf_cx B v -> lyc = mv_ly v -> In (1, pos) (frames Sc) ->
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mf mdf 0 ->
ent_lbl_mem v Wc memc pos -> sa_mconf (rdW Wc memc) (mv_c v) (mv_mc v) ->
(forall i, (i < S (length (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))])))%nat ->
   rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) =
   Some (nth i (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))] ++ [0]) 0)) ->
(forall i, (i < 96)%nat -> rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) <> None) ->
(forall a, 0 <= a < 2 ^ 64 ->
   ~ (mv_c v + seg_spec.MC_READING <= a < mv_c v + seg_spec.MC_READING + 96) ->
   ~ (mf_s1 (mv_sp v) - 2 * ESTACK <= a < mf_s1 (mv_sp v)) -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 24 <= a < mf_s1 (mv_sp v) + 160) ->
   ~ (mv_c v + seg_spec.MC_GEN <= a < mv_c v + seg_spec.MC_GEN + 4) -> rdW Wc mf a = rdW Wc mem2 a) ->
sa_val (rdW Wc mf) (mv_c v + seg_spec.MC_GEN) 4 (mc_gen (mv_mc v) + 1) ->
val_mem SEGS (mrestrict (w_H Wc) mf) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) ->
mf_core B v lyc Sc Wc mf mdf pos MF_LOW_OFF (mf_c1 (mv_mc v) (mv_lab v)).
Proof.
intros v lyc Sc Wc memc mem2 mf mdf pos CX Hly Hfin HPerm HJf HMEM HMC HBY HRD HK2 KR HG1 H112.
subst lyc.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _ & _ & Hgenb & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hsp0c).
destruct (mf_sp0 B v CX) as (_ & Hsp47 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hs1b : mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) by (destruct Hs1; lia). clear Hs1.
pose proof (proj1 HJf) as HARf.
destruct HCH as (bc & mcn & Hbcin0 & Hbclo & Hbchi).
assert (Hbcin : In (bc, mcn) (ablocks B (mv_ly v) Sc))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbcin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mcn HARf Hbcin) as (_ & Hbc4096 & Hbcceil & Hbcapp & _ & _ & _).
assert (Hr : mcn <= req_size mcn) by (unfold req_size; destruct (Z.eqb_spec mcn 0); lia).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARf Hfin) as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mcn 1 pos HARf Hbcin Hfin) as HdCF.
change (fs_frame_bytes 1) with 128 in HFceil, HdCF. unfold zdisjoint in HdCF. cbn [fst snd] in HdCF.
pose proof (mf_mconf_gen _ _ _ HMC) as [_ Hgr].
assert (Hnz : ~ In 0 (mf_lab_text (mv_lab v))) by exact (ent_lab_nul v CX).
destruct (mf_reading_bytes _ Hnz) as (_ & Htl & Htz).
set (F := frame_addr (mv_ly v) 1 pos) in *.
set (s1 := mf_s1 (mv_sp v)) in *. set (sp0 := mv_sp v) in *. set (c := mv_c v) in *.
unfold seg_spec.SEG_M_SIZE, seg_spec.MC_GEN, seg_spec.MC_READING in *. unfold in_app in Hbcapp.
assert (HF8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8) by (pose proof (Z.div_mod F 8 ltac:(lia));
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 24 <= a < s1 + 160) -> ~ (c + 9136 <= a < c + 9236) ->
  ~ (s1 - 2 * ESTACK <= a < s1) -> rdW Wc mf a = rdW Wc memc a).
{ intros a Ha H1 H2 H3. rewrite (KR a Ha H1 ltac:(lia)). apply HK2; [exact Ha | lia | exact H3]. }
unfold mf_core.
refine (conj HJf (conj HPerm (conj _ (conj _ (conj _ (conj H112 (conj _ (conj _ _)))))))).
- destruct HMEM as (VFL & _ & _).
  apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc mf (F + 120) (F + 120) 8 (flag_addr (mv_ly v) 1 pos));
    [|exact VFL].
  intros k Hk. apply KALL; unfold ESTACK; lia.
- destruct HMEM as (_ & VSH & _). intros i Hi.
  apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc mf (SHADOW_OFF + F / 8 + i) (SHADOW_OFF + F / 8 + i) 1
    MF_LOW_OFF); [|exact (VSH i Hi)].
  intros k Hk. apply KALL; unfold ESTACK, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
- destruct HMEM as (_ & _ & VSV). intros j r Hj.
  assert (Hj13 : (j < 13)%nat)
    by (change 13%nat with (length mf_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
  apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc mf (sp0 - 8 - 8 * Z.of_nat j) (sp0 - 8 - 8 * Z.of_nat j) 8
    (bv_unsigned (getr (mv_regs v) (Z_to_bv 5 r)))); [|exact (VSV j r Hj)].
  intros k Hk. apply KALL; unfold ESTACK; lia.
- unfold mf_c1.
  apply (mf_mconf_gen_reading (rdW Wc memc) (rdW Wc mf) c (mv_mc v) _ HMC);
    try unfold seg_spec.SEG_M_SIZE, seg_spec.MC_GEN, seg_spec.MC_READING in *.
  + intros a Ha H1 H2. apply KALL; unfold ESTACK; lia.
  + exact HG1.
  + lia.
  + exact Htl.
  + exact Htz.
  + intros i Hi. rewrite KR by lia. apply HBY. exact Hi.
  + intros i Hi. rewrite KR by lia. apply HRD. exact Hi.
  + intros i Hi z Hz. exact (m_file_s_entry_1.mf_aview_byte _ _ _ _ _ Hz).
- unfold seg_spec.SEG_M_SIZE.
  apply (mf_heap_addr SEGS B LAWS (mv_ly v) Sc Wc mf mdf); [exact HARf | exists bc, mcn; split; [exact Hbcin | lia]
  | lia].
- unfold seg_spec.SEG_M_SIZE. intros x Hx. fold c in Hx.
  apply (AR_block_word_vis SEGS B (mv_ly v) Sc Wc mf mdf bc mcn (c + 9236 - 1) x HARf Hbcin); lia.
Qed.

(* the values the runs leave in the chunks *)
Lemma ent_soff : forall E n k x, bv_unsigned (ew E n) = x -> 0 <= x + k < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n k)) mod 2 ^ (8 * Z.of_N 8) = x + k.
Proof.
intros E n k x H Hr. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia.
change (8 * Z.of_N 8) with 64. apply Z.mod_small. lia.
Qed.
Lemma ent_slit0 : forall E, bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 8) = 0.
Proof. intros E. reflexivity. Qed.
Lemma ent_shadow_r : forall E n k s x, bv_unsigned (ew E n) = x -> bv_unsigned (ew E s) = SHADOW_OFF ->
  0 <= x + k < 2 ^ 63 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff s 0))) mod 2 ^ (8 * Z.of_N 8) =
  SHADOW_OFF + (x + k) / 8.
Proof.
intros E n k s x Hn Hs Hr. change (8 * Z.of_N 8) with 64.
change (bv_unsigned (sv_denot E ?e)) with (U E e).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hn, Hs, Z.add_0_r.
assert (Hd : 0 <= (x + k) / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (zcanon_id (x + k)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.
Lemma ent_shadow_l : forall E n s x, bv_unsigned (ew E n) = x -> bv_unsigned (ew E s) = SHADOW_OFF ->
  0 <= x < 2 ^ 63 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff s 0) (SAlu ALU_SRL (SOff n 0) (SLit 3)))) mod 2 ^ (8 * Z.of_N 8) =
  SHADOW_OFF + x / 8.
Proof.
intros E n s x Hn Hs Hr. change (8 * Z.of_N 8) with 64.
change (bv_unsigned (sv_denot E ?e)) with (U E e).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hn, Hs, !Z.add_0_r.
assert (Hd : 0 <= x / 8 < 2 ^ 60) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.
Lemma ent_inc32 : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v -> v + 1 < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = v + 1.
Proof.
intros E k v H Hv Hv1. cbn [sv_denot]. rewrite H.
replace (bv_unsigned (Z_to_bv 64 v) + 0) with v by (rewrite unsigned_lit_small by lia; lia).
change (8 * Z.of_N 4) with 32. rewrite YN0d.ctr_chunk_mod by lia. apply Z.mod_small. lia.
Qed.
Lemma ent_sa_val_of : forall segs H mem a n v, val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* the bytes a run of ent_ss's regions keeps: all but the spill slots and c->gen *)
Ltac ent_keep v HFr Ua Ub :=
  let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros a Ha H1 H2;
  refine (kept_of_frame _ _ _ _ _
    (fun x => (mf_s1 (mv_sp v) + 24 <= x < mf_s1 (mv_sp v) + 160) \/
              (mv_c v + seg_spec.MC_GEN <= x < mv_c v + seg_spec.MC_GEN + 4)) HFr _ a Ha _);
  [ let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin' := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
    intros bb wlo whi x Hin' Hr; vm_compute in Hin';
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hr;
      first [ rewrite Ua in Hr; left; lia
            | rewrite Ub in Hr; right; unfold seg_spec.MC_GEN; lia
            | exfalso; lia ] |]);
    destruct Hin'
  | intros [Hq | Hq]; [exact (H1 Hq) | exact (H2 Hq)] ].
Ltac ent_in := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma ent_b0_nil : forall s, ~ In 0 s -> mf_b0 s = 0 -> s = [].
Proof. intros [|x s] Hn Hb; [reflexivity|]. exfalso. cbn in Hb. apply Hn. left. exact Hb. Qed.
Lemma ent_b0_cons : forall s, mf_b0 s <> 0 -> s <> [].
Proof. intros s Hb ->. apply Hb. reflexivity. Qed.

Lemma ent_post : (forall n, MF_HEAD_F B n) -> MF_EXIT_F B ->
forall v lyc Sc (Wc : world SEGS) memc (regs2 : bvmap 5 word) mem2 md2 pos,
mf_cx B v -> sa_frm0 -> lyc = mv_ly v -> (exists f, Sc = set_fs f (mv_S v)) -> In (1, pos) (frames Sc) ->
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ent_snp_regs v pos regs2 ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
ent_lbl_mem v Wc memc pos -> sa_mconf (rdW Wc memc) (mv_c v) (mv_mc v) ->
(forall i, (i < S (length (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))])))%nat ->
   rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) =
   Some (nth i (snprintf_s 96 F_s [AS (mf_lab_text (mv_lab v))] ++ [0]) 0)) ->
(forall i, (i < 96)%nat -> rdW Wc mem2 (mv_c v + seg_spec.MC_READING + Z.of_nat i) <> None) ->
(forall a, 0 <= a < 2 ^ 64 ->
   ~ (mv_c v + seg_spec.MC_READING <= a < mv_c v + seg_spec.MC_READING + 96) ->
   ~ (mf_s1 (mv_sp v) - 2 * ESTACK <= a < mf_s1 (mv_sp v)) -> rdW Wc mem2 a = rdW Wc memc a) ->
SRr SEGS Wc (mkCfg (mkst regs2 (w64 (BASE + (AF_m_file + 0x15c))) mem2 (seg_rom SEGS)) md2) (MF_POST B v).
Proof.
intros HEADS EXIT v lyc Sc Wc memc regs2 mem2 md2 pos CX HFRM Hly HSc Hfin HPerm RG HJ2 HMEM HMC HBY HRD HK2.
pose proof CX as CX0.
destruct CX as (HPRE & HROOM & HROD & HLIT & HWD & HRL & HCAT & HSSPv & H10 & Hc64 & H11 & Ht64 & H12 & Hlp64
  & HMP & HEV).
pose proof HMP as (Hc0 & Hc16 & HMC0 & HCH & HCA & HCT & Hgenb & Hrefb & Hovfb & Ht0 & HTS & Hslen & HTH & HTA
  & HTM & HTD & HOS & HLAB).
clear HROOM HROD HLIT HWD HRL HCAT HSSPv HEV HOS HLAB HMC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof YM05.alloc_ceiling_val as HAC.
destruct (mf_s1_facts B v CX0) as (Hs1 & Hs1m & Hsp0c).
destruct (mf_sp0 B v CX0) as (_ & Hsp47 & Hsp16).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof (proj1 HJ2) as HAR2.
(* the mconf block and the text block at this state *)
destruct HCH as (bc & mcn & Hbcin0 & Hbclo & Hbchi).
assert (Hbcin : In (bc, mcn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbcin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mcn HAR2 Hbcin) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hbcn).
destruct HTH as (bt & mtn & Hbtin0 & Hbtlo & Hbthi).
assert (Hbtin : In (bt, mtn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbtin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mtn HAR2 Hbtin) as (Hbt16 & Hbt4096 & Hbtceil & Hbtapp & Hbtpres & _ & Hbtn).
pose proof (req_size_pos mcn ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos mtn ltac:(lia)) as [Hrt1 Hrt2].
(* c->gen at the call (kept by snprintf) and the text's first byte *)
destruct (mf_mconf_gen _ _ _ HMC) as [HGENc HGENr].
set (gen0 := mc_gen (mv_mc v)) in *.
set (b0 := mf_b0 (mv_s v)).
assert (Hs1b : mv_sp v - 304 <= mf_s1 (mv_sp v) <= mv_sp v - 288) by (destruct Hs1; lia). clear Hs1.
assert (Hbcr : mcn <= req_size mcn) by lia.
assert (Hbtr : mtn <= req_size mtn) by lia.
(* the text at the call's return state *)
destruct (ent_txt_now v lyc Sc Wc mem2 md2 pos CX0 HPerm HJ2) as (HTS2 & HTA2).
assert (HB0 : rdW Wc mem2 (mv_t v) = Some b0).
{ pose proof HTS2 as ((Hz & _) & _). pose proof (Hz 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
pose proof (m_file_s_entry_1.mf_aview_byte SEGS (w_H Wc) mem2 _ _ HB0) as Hb0r.
(* c->gen at the return state *)
assert (HGEN2 : sa_val (rdW Wc mem2) (mv_c v + seg_spec.MC_GEN) 4 gen0).
{ intros k Hk. rewrite HK2; [exact (HGENc k Hk) | unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *; lia
  | unfold seg_spec.MC_GEN, seg_spec.MC_READING in *; lia
  | unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, ESTACK in *; lia]. }
assert (HCA2 : sa_addr (rdW Wc mem2) (mv_c v) seg_spec.SEG_M_SIZE)
  by (apply (mf_heap_addr SEGS B LAWS lyc Sc Wc mem2 md2); [exact HAR2 | exists bc, mcn; split; [exact Hbcin | lia]
      | unfold seg_spec.SEG_M_SIZE; lia]).
pose proof HTD as HTD0. unfold sa_disj in HTD0. pose proof (mfk_span_bounds (mv_t v) (mv_s v)) as HSP.
assert (Htg : mf_nam (mv_t v + 1 <= mv_c v + 0x23b0 \/ mv_c v + 0x23b4 <= mv_t v))
  by (unfold mf_nam, seg_spec.SEG_M_SIZE in *; lia).
clear HTD0.
(* the environment and the atoms' values *)
set (E := Eimg (Ereg regs2 [Z_to_bv 64 gen0; Z_to_bv 64 b0])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
assert (E32 : ew E 32 = Z_to_bv 64 gen0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (U9 : bv_unsigned (ew E 9) = mf_s1 (mv_sp v))
  by (rewrite (ER 9%nat (9%bv : bv 5) ltac:(lia) eq_refl), R9; apply mf_w64_u; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (rewrite (ER 18%nat (18%bv : bv 5) ltac:(lia) eq_refl), R18; apply mf_w64_u; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = mv_c v + 0x2000)
  by (rewrite (ER 22%nat (22%bv : bv 5) ltac:(lia) eq_refl), R22; apply mf_w64_u;
      unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia).
assert (U27 : bv_unsigned (ew E 27) = mv_t v)
  by (rewrite (ER 27%nat (27%bv : bv 5) ltac:(lia) eq_refl), R27; apply mf_w64_u; lia).
assert (U32 : bv_unsigned (ew E 32) = gen0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (UBx : U E EntBx = SHADOW_OFF)
  by (unfold EntBx; rewrite U_SOff, U18, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
(* the seed at 0x86018 *)
assert (HS : st_ok_pi SEGS VAL E ent_ss
  (restrict (w_H Wc) (mkst regs2 (Z_to_bv 64 (BASE + (AF_m_file + 0x15c))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ent_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ent_r_slots, ent_r_gen, ent_r_txt.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      apply Hpres2. rewrite HSTK. lia.
    + rewrite U22. unfold seg_spec.SEG_M_SIZE in *. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hbcpres (mv_c v + 0x2000 + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (mv_c v + 0x2000) 0x3b0 4 (SOff 32 0) gen0);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (mv_c v + 0x2000 + 0x3b0) with (mv_c v + seg_spec.MC_GEN) by (unfold seg_spec.MC_GEN; lia).
      apply mf_val_mem_of_sa. exact HGEN2.
    + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (mv_t v) 0 1 (SOff 33 0) b0);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply mf_val_mem_of_sa. apply (mf_sa_val_b0 SEGS (w_H Wc) mem2). exact (proj1 HTS2).
  - apply pairwise_disjoint_of_extents.
    unfold ent_r_slots, ent_r_gen, ent_r_txt, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U22, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (ZB : bt + req_size mtn <= alloc_ceiling /\ bc + req_size mcn <= alloc_ceiling /\ bc <= mv_c v /\
      mv_c v + 9236 <= bc + req_size mcn /\ bt <= mv_t v /\ 4096 <= bt /\ mv_t v + 1 <= bt + req_size mtn)
      by (unfold seg_spec.SEG_M_SIZE in *; lia).
    assert (ZS : alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v - 304 <= mf_s1 (mv_sp v)) by (rewrite HSTK in *; lia).
    revert ZB ZS Htg Hs1b. clear. unfold mf_nam. intros. repeat split; lia.
  - split; [|split; exact I].
    cbn [ent_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, U22, U27, U32, U33.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (H22 : (mv_c v + 0x2000) mod 16 = 0)
      by (rewrite <- Zplus_mod_idemp_l, Hc16; reflexivity).
    unfold SB, SHADOW_OFF, seg_spec.SEG_M_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS EntBx ent_SH E (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, ent_SH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UBx, U_SOff, Z.add_0_r.
  - rewrite U22, zcanon_id by (unfold M64, seg_spec.SEG_M_SIZE in *; lia). rewrite <- (aview_rd_of SEGS). split.
    + destruct HCA2 as (_ & _ & _ & HRA & _). intros x Hx. apply HRA. unfold seg_spec.SEG_M_SIZE. lia.
    + intros a Ha. cbn [Z.min Z.max] in Ha. unfold in_app in Hbcapp.
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, seg_spec.SEG_M_SIZE in *. lia.
  - rewrite U27, zcanon_id by (unfold M64; lia). rewrite <- (aview_rd_of SEGS). split.
    + destruct HTA2 as (_ & _ & _ & HRA & _). intros x Hx. apply HRA. lia.
    + intros a Ha. cbn [Z.min Z.max] in Ha. unfold in_app in Hbtapp.
      unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof HJ2 as HJ.
change (w64 (BASE + (AF_m_file + 0x15c))) with (Z_to_bv 64 (BASE + (AF_m_file + 0x15c))).
(* 0x86018 .. 0x86060: gen++, the two checks, the *text test (a branch on atom 33) *)
paj_run_tok RUN HS HJ SHOK Bspan; [ent_awr v U9 U22 Hbcin|].
rename HFr into HFr1. clear HF HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG1 : forall n, (n < 1024)%nat -> ew Ex n = ew E n)
    by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity);
  assert (HAGx : env_agree 32 (Ereg regs2 [Z_to_bv 64 gen0; Z_to_bv 64 b0]) Ex)
    by (split; [intros n Hn; rewrite AG1 by lia; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (UR : forall n (r : bv 5) z, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regs2 r = w64 z ->
    0 <= z < 2 ^ 64 -> bv_unsigned (ew Ex n) = z)
    by (intros n r z Hn Hr Hz Hzr; rewrite AG1 by lia; rewrite (ER n r Hn Hr), Hz; apply mf_w64_u; exact Hzr);
  assert (U9x : bv_unsigned (ew Ex 9) = mf_s1 (mv_sp v)) by (rewrite AG1 by lia; exact U9);
  assert (U22x : bv_unsigned (ew Ex 22) = mv_c v + 0x2000) by (rewrite AG1 by lia; exact U22);
  assert (E32x : ew Ex 32 = Z_to_bv 64 gen0) by (rewrite AG1 by lia; exact E32);
  assert (U256x : bv_unsigned (ew Ex 256) = SegInstA.wordsA)
    by (rewrite AG1 by lia; subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia);
        rewrite unsigned_lit_small by (pose proof (pa_val_range 256); lia); exact (mf_val_words VOBJS));
  assert (UB0 : U Ex (SExt false 8 (SOff 33 0)) = b0)
    by (rewrite U_zext, U_SOff, AG1, U33 by lia; rewrite Z.add_0_r, zcanon_id by (unfold M64; lia);
        change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia)
end.
subst lyc.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR2 Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
assert (U19x := UR 19%nat (19%bv : bv 5) _ ltac:(lia) eq_refl R19 ltac:(lia)).
assert (U21x := UR 21%nat (21%bv : bv 5) _ ltac:(lia) eq_refl R21 ltac:(lia)).
assert (U23x := UR 23%nat (23%bv : bv 5) _ ltac:(lia) eq_refl R23
  ltac:(unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *; lia)).
assert (U24x := UR 24%nat (24%bv : bv 5) _ ltac:(lia) eq_refl R24 ltac:(lia)).
assert (U18x := UR 18%nat (18%bv : bv 5) _ ltac:(lia) eq_refl R18 ltac:(unfold SHADOW_OFF; lia)).
assert (HF8 : 0 <= frame_addr (mv_ly v) 1 pos / 8 <= frame_addr (mv_ly v) 1 pos)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U26x := UR 26%nat (26%bv : bv 5) _ ltac:(lia) eq_refl R26 ltac:(unfold SHADOW_OFF; lia)).
clear UR.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* *text = 0: the release *)
  assert (Hb0z : b0 = 0).
  { rewrite YO0c.branch_eq in Hc. apply Z.eqb_eq in Hc.
    lazymatch type of Hc with bv_unsigned (sv_denot ?Ex ?e) = bv_unsigned (sv_denot ?Ex ?e2) =>
      change (U Ex e = U Ex e2) in Hc end.
    rewrite UB0, U_SLit in Hc. exact Hc. }
  assert (Hs0 : mv_s v = []) by (apply ent_b0_nil; [exact (proj2 (proj1 HTS)) | exact Hb0z]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_EXIT; [ent_awr v U9x U22x Hbcin|].
  rename HFr into HFr2. clear HF HG.
  lazymatch type of HFr1 with frame_of _ _ _ (mrestrict _ ?m1) =>
  lazymatch type of HFr2 with frame_of _ _ _ (mrestrict _ ?m2) =>
    assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 24 <= a < mf_s1 (mv_sp v) + 160) ->
      ~ (mv_c v + seg_spec.MC_GEN <= a < mv_c v + seg_spec.MC_GEN + 4) -> rdW Wc m2 a = rdW Wc mem2 a)
    by (intros a Ha H1 H2; transitivity (rdW Wc m1 a);
        [revert a Ha H1 H2; ent_keep v HFr2 U9x U22x | revert a Ha H1 H2; ent_keep v HFr1 U9 U22])
  end end.
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?mf) =>
    pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H Wc) mf) 1%nat _ HS eq_refl) as HRg;
    pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H Wc) mf) 0%nat _ HS eq_refl) as HRs;
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 gen0; Z_to_bv 64 b0]
      ([2; 3; 4; 8; 9; 18; 24; 26]%bv : list (bv 5)) HS HAGx ltac:(vm_compute; reflexivity)) as KRf
  end.
  cbn [restrict ms_mem] in HRg, HRs.
  pose proof (field_of_region_any _ _ 22%nat (mv_c v + 0x2000) _ _ _ _ _ 944 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) HRg U22x ltac:(ent_in) ltac:(lia)) as VG.
  rewrite (ent_inc32 _ 32 gen0 E32x ltac:(lia) ltac:(lia)) in VG. change (N.to_nat 4) with 4%nat in VG.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 112 8%N (SOff 19 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as V112.
  rewrite (ent_soff _ 19 0 _ U19x ltac:(lia)), Z.add_0_r in V112. change (N.to_nat 8) with 8%nat in V112.
  lazymatch type of KR with forall a, _ -> _ -> _ -> rdW Wc ?mf a = _ =>
    assert (HG1 : sa_val (rdW Wc mf) (mv_c v + seg_spec.MC_GEN) 4 (gen0 + 1))
      by (replace (mv_c v + seg_spec.MC_GEN) with (mv_c v + 0x2000 + 944) by (unfold seg_spec.MC_GEN; lia);
          apply ent_sa_val_of; exact VG)
  end.
  pose proof (ent_core_fin v (mv_ly v) Sc Wc memc mem2 _ _ pos CX0 eq_refl Hfin HPerm HJ HMEM HMC HBY HRD HK2 KR
    HG1 V112) as CORE.
  assert (EF : mf_final v = mf_c1 (mv_mc v) (mv_lab v)) by (unfold mf_final; rewrite Hs0; apply mf_file_nil).
  rewrite <- EF in CORE.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?mf) _ _ _) ?mdf) _ =>
    pose proof (EXIT fx v (mv_ly v) Sc Wc (ms_regs mf) (ms_mem mf) mdf pos CX0 (conj eq_refl HSc) CORE) as HX
  end.
  unfold mf_at, MF_EXIT in HX. apply HX.
  + unfold mf_regs_ex.
    repeat split; rewrite KRf by ent_in; assumption.
  + rewrite KRf by ent_in. exact R24.
- (* *text <> 0: the set-up and the head *)
  assert (Hb0n : b0 <> 0).
  { rewrite YO0c.branch_eq in Hc. apply Z.eqb_neq in Hc.
    lazymatch type of Hc with bv_unsigned (sv_denot ?Ex ?e) <> bv_unsigned (sv_denot ?Ex ?e2) =>
      change (U Ex e <> U Ex e2) in Hc end.
    rewrite UB0, U_SLit in Hc. exact Hc. }
  assert (Hsn : mv_s v <> []) by (apply ent_b0_cons; exact Hb0n).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_HEAD; [ent_awr v U9x U22x Hbcin|].
  rename HFr into HFr2. clear HF HG.
  lazymatch type of HFr1 with frame_of _ _ _ (mrestrict _ ?m1) =>
  lazymatch type of HFr2 with frame_of _ _ _ (mrestrict _ ?m2) =>
    assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 24 <= a < mf_s1 (mv_sp v) + 160) ->
      ~ (mv_c v + seg_spec.MC_GEN <= a < mv_c v + seg_spec.MC_GEN + 4) -> rdW Wc m2 a = rdW Wc mem2 a)
    by (intros a Ha H1 H2; transitivity (rdW Wc m1 a);
        [revert a Ha H1 H2; ent_keep v HFr2 U9x U22x | revert a Ha H1 H2; ent_keep v HFr1 U9 U22])
  end end.
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?mf) =>
    pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H Wc) mf) 1%nat _ HS eq_refl) as HRg;
    pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H Wc) mf) 0%nat _ HS eq_refl) as HRs;
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 gen0; Z_to_bv 64 b0]
      ([2; 3; 4; 8; 9; 18; 21; 24; 26; 27]%bv : list (bv 5)) HS HAGx ltac:(vm_compute; reflexivity)) as KRf
  end.
  prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
  cbn [restrict ms_mem] in HRg, HRs.
  pose proof (field_of_region_any _ _ 22%nat (mv_c v + 0x2000) _ _ _ _ _ 944 4%N
    (SAlu ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) HRg U22x ltac:(ent_in) ltac:(lia)) as VG.
  rewrite (ent_inc32 _ 32 gen0 E32x ltac:(lia) ltac:(lia)) in VG. change (N.to_nat 4) with 4%nat in VG.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 112 8%N (SOff 19 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as V112.
  rewrite (ent_soff _ 19 0 _ U19x ltac:(lia)), Z.add_0_r in V112. change (N.to_nat 8) with 8%nat in V112.
  lazymatch type of KR with forall a, _ -> _ -> _ -> rdW Wc ?mf a = _ =>
    assert (HG1 : sa_val (rdW Wc mf) (mv_c v + seg_spec.MC_GEN) 4 (gen0 + 1))
      by (replace (mv_c v + seg_spec.MC_GEN) with (mv_c v + 0x2000 + 944) by (unfold seg_spec.MC_GEN; lia);
          apply ent_sa_val_of; exact VG)
  end.
  pose proof (ent_core_fin v (mv_ly v) Sc Wc memc mem2 _ _ pos CX0 eq_refl Hfin HPerm HJ HMEM HMC HBY HRD HK2 KR
    HG1 V112) as CORE.
  (* the spill slots the set-up wrote *)
  unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE, seg_spec.MC_N in *.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 24 8%N (SOff 21 9100) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S24.
  rewrite (ent_soff _ 21 9100 _ U21x ltac:(lia)) in S24.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 32 8%N (SOff 22 4) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S32.
  rewrite (ent_soff _ 22 4 _ U22x ltac:(lia)) in S32.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 40 8%N (SOff 22 940) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S40.
  rewrite (ent_soff _ 22 940 _ U22x ltac:(lia)) in S40.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 48 8%N (SOff 22 944) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S48.
  rewrite (ent_soff _ 22 944 _ U22x ltac:(lia)) in S48.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 56 8%N
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 944) (SLit 3)) (SOff 18 0)) HRs U9x ltac:(ent_in) ltac:(lia)) as S56.
  rewrite (ent_shadow_r _ 22 944 18 _ U22x U18x ltac:(lia)) in S56.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 64 8%N (SOff 23 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S64.
  rewrite (ent_soff _ 23 0 _ U23x ltac:(lia)), Z.add_0_r in S64.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 72 8%N
    (SAlu ALU_ADD (SOff 18 0) (SAlu ALU_SRL (SOff 256 0) (SLit 3))) HRs U9x ltac:(ent_in) ltac:(lia)) as S72.
  rewrite (ent_shadow_l _ 256 18 _ U256x U18x ltac:(unfold SegInstA.wordsA; lia)) in S72.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 80 8%N (SOff 256 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S80.
  rewrite (ent_soff _ 256 0 _ U256x ltac:(unfold SegInstA.wordsA; lia)), Z.add_0_r in S80.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 88 8%N (SOff 22 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S88.
  rewrite (ent_soff _ 22 0 _ U22x ltac:(lia)), Z.add_0_r in S88.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 104 8%N (SOff 24 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S104.
  rewrite (ent_soff _ 24 0 _ U24x ltac:(lia)), Z.add_0_r in S104.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 120 8%N (SOff 26 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S120.
  rewrite (ent_soff _ 26 0 _ U26x ltac:(unfold SHADOW_OFF; lia)), Z.add_0_r in S120.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 128 8%N (SOff 21 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S128.
  rewrite (ent_soff _ 21 0 _ U21x ltac:(lia)), Z.add_0_r in S128.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 136 8%N (SLit 0) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S136.
  rewrite ent_slit0 in S136.
  pose proof (field_of_region_any _ _ 9%nat (mf_s1 (mv_sp v)) _ _ _ _ _ 152 8%N (SOff 19 32) HRs U9x
    ltac:(ent_in) ltac:(lia)) as S152.
  rewrite (ent_soff _ 19 32 _ U19x ltac:(lia)) in S152.
  change (N.to_nat 8) with 8%nat in S24, S32, S40, S48, S56, S64, S72, S80, S88, S104, S120, S128, S136, S152.
  lazymatch type of KR with forall a, _ -> _ -> _ -> rdW Wc ?mf a = _ =>
    assert (CELLS : mf_cells v (mv_ly v) pos mf Wc None)
  end.
  { unfold mf_cells, mf_cur_ptr, seg_spec.MC_KNOCK, seg_spec.MC_OVERFLOW, seg_spec.MC_NKEPT, seg_spec.MC_GEN,
      seg_spec.MC_READING, seg_spec.MC_N.
    replace (mv_c v + 0x2000 + 4) with (mv_c v + 8196) in S32 by lia.
    replace (mv_c v + 0x2000 + 940) with (mv_c v + 9132) in S40 by lia.
    replace (mv_c v + 0x2000 + 944) with (mv_c v + 9136) in S48, S56 by lia.
    replace (mv_c v + 0x2000) with (mv_c v + 8192) in S88 by lia.
    refine (conj S24 (conj S32 (conj S40 (conj S48 (conj S56 (conj S64 (conj S72 (conj S80 (conj S88
      (conj S104 (conj S120 (conj S128 (conj S136 S152))))))))))))). }
  destruct (ent_txt_now v (mv_ly v) Sc Wc _ _ pos CX0 HPerm HJ) as (HTSf & HTAf).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?mf) _ _ _) ?mdf) _ =>
    pose proof (HEADS (S (length (mv_s v))) fx v (mv_ly v) Sc Wc (ms_regs mf) (ms_mem mf) mdf pos
      (mf_c1 (mv_mc v) (mv_lab v)) None 0 (mv_t v) (mv_s v) CX0 (conj eq_refl HSc) HFRM CORE CELLS) as HX
  end.
  unfold mf_at, MF_HEAD in HX. apply HX.
  + unfold mf_regs_at, MF_BLANK, w64.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); 
      first [rewrite KRf by ent_in; assumption | rewrite Q19; reflexivity | rewrite Q25; reflexivity].
  + rewrite KRf by ent_in. exact R24.
  + lia.
  + exact Hsn.
  + unfold mf_loop. rewrite Nat.sub_diag. cbn [skipn].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact HTSf|]. split; [exact HTAf|].
    split; [exact I|]. unfold mv_k0, mf_c1. cbn [mc_kept mc_refused mc_overflow]. repeat split; lia.
  + symmetry. unfold mf_final. apply mf_file_lines.
  + rewrite KRf by ent_in. exact R27.
  + rewrite KRf by ent_in. exact R21.
  + rewrite Q22. reflexivity.
Qed.
End e.
End f.
End d.
