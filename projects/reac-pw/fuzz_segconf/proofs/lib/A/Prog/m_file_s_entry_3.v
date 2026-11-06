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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 280 of its 325 lines of code are new or changed and 408 lines of the source are left out. *)
(* S_MF_ENTRY, part 3: m_file on fuzz_segconf.asan (image A, m_file at 0x85ebc) from the cut ENT_LBL at the label test
   0x85ff4 (lib/A/Prog/m_file_s_entry_c.v) to the hand-offs MF_HEAD / MF_EXIT (lib/A/Prog/m_file_m.v).
     0x85ff4          `bnez s4`: s4 = lp; lp = 0 exactly when there is no label (m_file_pre's sa_ostr); the arm
                      without a label sets s4 = "reac-pw.conf" (object 13, 0x85ff8-0x85ffc);
     0x86000-0x86010  a2 = "%s" (object 14), a1 = 96, a0 = s7 = &c->reading, a3 = s4;
     0x86014          snprintf(c->reading, 96, "%s", a3): m_file_s_entry_s.v's mf_snp_step, its %s argument the
                      label (ent_lab_now: its bytes at the cut from the journal and the cut's mconf-block premise,
                      its slack and shadow from AR) or the literal (m_file_k.v's mf_lit_now_j);
     0x86018-0x860d0  m_file_s_entry_3a.v's ent_post (gen++, the *text test, the set-up, MF_EXIT / MF_HEAD).
   Each arm is walked by its own run to the call (they join only after it). A lane of the G2 walk owner. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_m m_file_s_entry_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_1 m_file_s_entry_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_s m_file_s_entry_3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma ent_denot_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

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
Hypothesis SSP : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf)
  SegInstA.gotwA SegInstA.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* the label at the cut: its bytes are the entry's (an entry block's byte by the journal or the cut's premise on
   the mconf block, an entry frame's by the journal, an image byte by mf_img_now_j), its slack and shadow come
   from AR (heap), the journal and AR (frame) or sa_pinned / sa_pinned_tail (image) *)
Lemma ent_lab_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos l,
mf_cx B v -> lyc = mv_ly v -> Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 ->
(forall a, mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE -> rdW Wc memc a = rdW (mv_W v) (mv_mem v) a) ->
mv_lab v = Some l ->
0 < mv_lp v /\ sa_str (rdW Wc memc) (mv_lp v) l /\ sa_addr (rdW Wc memc) (mv_lp v) (Z.of_nat (length l) + 1) /\
Z.of_nat (length l) <= 65535 /\
(sa_heap B lyc Sc (mv_lp v) (Z.of_nat (length l) + 1) \/ sa_fframe lyc Sc (mv_lp v) (Z.of_nat (length l) + 1) \/
 sa_img SEGS B (mv_lp v) (Z.of_nat (length l) + 1)) /\
sa_disj (mv_lp v) (seg_spec.cstr_span (mv_lp v) l) (mv_c v + seg_spec.MC_READING) 96.
Proof.
intros v lyc Sc Wc memc mdc pos l CX Hly HPerm HJ HCB Hlab. subst lyc.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlp64 & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & HLAB).
rewrite Hlab in HOS, HLAB. destruct HOS as (Hlp0 & HSTR0). destruct HLAB as (Hlen & HLOC & HADDR0 & HDJ).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HPRE) as HAR0.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
(* a byte of an entry frame, or of its shadow, reads as at the entry *)
assert (KF : forall cid posf a, In (cid, posf) (frames (mv_S v)) ->
  (in_zr a (frame_rng (mv_ly v) (cid, posf)) \/
   in_zr a (shadow_addr (frame_addr (mv_ly v) cid posf), fs_frame_bytes cid / 8)) ->
  rdW Wc memc a = rdW (mv_W v) (mv_mem v) a).
{ intros cid posf a Hin Ha.
  destruct (Z_lt_le_dec a (mv_c v)) as [Ha1 | Ha1];
    [| destruct (Z_lt_le_dec a (mv_c v + seg_spec.SEG_M_SIZE)) as [Ha2 | Ha2]; [exact (HCB a (conj Ha1 Ha2)) |]];
  (apply (F4 cid posf a Hin Ha); intros HF; pose proof (mf_fp_in_block B v a CX HF); lia). }
pose proof (mfk_span_bounds (mv_lp v) l) as HSP.
destruct HSTR0 as ((Hz & Hn0) & Htl).
split; [lia|].
destruct HLOC as [(b & m & Hin0 & Hb1 & Hb2) | [(cid & posf & Hinf & Hcid & Hf1 & Hf2) | (Himg & Hpin & Hptl)]].
- (* a heap block *)
  assert (Hin : In (b, m) (ablocks B (mv_ly v) Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin0).
  assert (Hr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (KB : forall a, b <= a < b + req_size m -> rdW Wc memc a = rdW (mv_W v) (mv_mem v) a).
  { intros a Ha.
    destruct (Z_lt_le_dec a (mv_c v)) as [Ha1 | Ha1];
      [| destruct (Z_lt_le_dec a (mv_c v + seg_spec.SEG_M_SIZE)) as [Ha2 | Ha2]; [exact (HCB a (conj Ha1 Ha2)) |]];
    (apply (ent_blk_now B v (mv_ly v) Sc Wc memc mdc pos b m a CX HPerm HJ Hin0 Ha); lia). }
  split; [split; [split; [|exact Hn0]|]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KB by lia.
    apply Hz. rewrite length_app. cbn [length]. lia.
  + intros x Hx. apply (AR_block_word_vis SEGS B (mv_ly v) Sc Wc memc mdc b m (mv_lp v + Z.of_nat (length l)) x HAR
      Hin); lia.
  + split; [apply (mf_heap_addr SEGS B LAWS (mv_ly v) Sc Wc memc mdc); [exact HAR | exists b, m; split; [exact Hin | lia]
      | lia]|].
    split; [exact Hlen|]. split; [left; exists b, m; split; [exact Hin | lia]|]. exact HDJ.
- (* an entry side-stack frame *)
  assert (Hinf' : In (cid, posf) (frames Sc)) by (rewrite Hfrs; right; exact Hinf).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid posf HAR0 Hinf) as (HFal & _ & _ & _).
  set (F := frame_addr (mv_ly v) cid posf) in *.
  assert (HFS : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; apply Z.shiftl_mul_pow2; lia).
  assert (HFS8 : fs_frame_bytes cid = 8 * (8 * 2 ^ cid)) by lia.
  assert (HF8 : F = 8 * (4 * (F / 32))) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
  assert (KFB : forall a, F <= a < F + fs_frame_bytes cid -> rdW Wc memc a = rdW (mv_W v) (mv_mem v) a)
    by (intros a Ha; apply (KF cid posf a Hinf); left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; lia).
  assert (He8 : mv_lp v + Z.of_nat (length l) =
      8 * ((mv_lp v + Z.of_nat (length l)) / 8) + (mv_lp v + Z.of_nat (length l)) mod 8 /\
    0 <= (mv_lp v + Z.of_nat (length l)) mod 8 < 8)
    by (split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia]).
  split; [split; [split; [|exact Hn0]|]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KFB by lia.
    apply Hz. rewrite length_app. cbn [length]. lia.
  + intros x Hx. assert (Hx2 : x < F + fs_frame_bytes cid) by lia.
    rewrite KFB by lia. exact (Htl x Hx).
  + split.
    * destruct HADDR0 as (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
      split.
      -- intros x Hx. destruct (A3 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
         rewrite (KF cid posf (shadow_of_addr SHADOW_OFF x) Hinf); [exact Hsv|]. right.
         unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. fold F.
         assert (D1 : F / 8 <= x / 8) by (apply Z.div_le_mono; lia).
         assert (D2 : x / 8 < F / 8 + fs_frame_bytes cid / 8).
         { rewrite HFS8, HF8. rewrite !(Z.mul_comm 8), !Z.div_mul by lia. apply Z.div_lt_upper_bound; lia. }
         lia.
      -- intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS (mv_ly v) Sc Wc memc mdc cid posf); [exact HAR | exact Hinf'
         | fold F; lia | fold F; lia | lia].
    * split; [exact Hlen|]. split; [right; left; exists cid, posf; split; [exact Hinf' | split; [exact Hcid | fold F; lia]]|].
      exact HDJ.
- (* the image *)
  split; [split; [split; [|exact Hn0]|]|].
  + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Himg (mv_lp v + Z.of_nat i) ltac:(lia)) as (I1 & I2 & I3).
    rewrite (mf_img_now_j B v (mv_ly v) Sc Wc memc mdc pos _ CX HJ I1 I2 I3).
    apply Hz. rewrite length_app. cbn [length]. lia.
  + exact (Hptl _ _ _ _ _ HAR).
  + split; [exact (Hpin _ _ _ _ _ HAR)|]. split; [exact Hlen|]. split; [right; right; exact Himg|]. exact HDJ.
Qed.

(* the call at 0x86014 from a state whose memory reads as the cut's: mf_snp_step, then ent_post at the FP state
   the wrapper returns *)
Lemma ent_call : (forall n, MF_HEAD_F B n) -> MF_EXIT_F B ->
forall v lyc Sc (Wc : world SEGS) memc (regsc : bvmap 5 word) memc' mdc pos lptr ltext,
mf_cx B v -> sa_frm0 -> lyc = mv_ly v -> (exists f, Sc = set_fs f (mv_S v)) -> In (1, pos) (frames Sc) ->
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc 0 ->
ent_lbl_mem v Wc memc pos -> sa_mconf (rdW Wc memc) (mv_c v) (mv_mc v) ->
(forall a, rdW Wc memc' a = rdW Wc memc a) ->
ent_snp_regs B v pos regsc ->
getr regsc 10 = w64 (mv_c v + seg_spec.MC_READING) -> getr regsc 11 = w64 96 ->
getr regsc 12 = w64 (SegInstA.seg_litA_fz F_s) -> getr regsc 13 = w64 lptr ->
ltext = mf_lab_text (mv_lab v) ->
0 < lptr -> sa_str (rdW Wc memc) lptr ltext -> sa_addr (rdW Wc memc) lptr (Z.of_nat (length ltext) + 1) ->
Z.of_nat (length ltext) <= 65535 ->
(sa_heap B lyc Sc lptr (Z.of_nat (length ltext) + 1) \/ sa_fframe lyc Sc lptr (Z.of_nat (length ltext) + 1) \/
 sa_img SEGS B lptr (Z.of_nat (length ltext) + 1)) ->
sa_disj lptr (seg_spec.cstr_span lptr ltext) (mv_c v + seg_spec.MC_READING) 96 ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_m_file + 0x158))) memc' (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros HEADS EXIT v lyc Sc Wc memc regsc memc' mdc pos lptr ltext CX HFRM Hly HSc Hfin HPerm HJ HMEM HMC EQV RS
  T10 T11 T12 T13 Hlt Hlp0 HSTR HADDR Hlen HLOC HDJ.
pose proof RS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & HCH & _).
assert (HHEAP : sa_heap B lyc Sc (mv_c v) seg_spec.SEG_M_SIZE).
{ destruct HCH as (bc & mcn & Hin & H1 & H2). exists bc, mcn.
  split; [apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin | lia]. }
apply (mf_snp_step B ASNPRINTF SSP v lyc Sc Wc regsc memc' mdc pos lptr ltext CX HFRM HJ R2 R3 R4 T10 T11 T12 T13
  Hlp0 (mfs_str_eq _ _ _ _ EQV HSTR) (mfs_addr_eq _ _ _ _ EQV HADDR) Hlen HLOC HDJ HHEAP
  (mf_lit_now_j B v lyc Sc Wc memc' mdc pos F_s CX HJ ltac:(left; reflexivity))
  (mf_rom_now_j B v lyc Sc Wc memc' mdc pos CX HJ)).
intros fx1 regs2 mem2 md2 Hfx HP2 HJ2 HBY HRD HK2. subst ltext.
apply (ent_post (fx := fx1) B VOBJS HEADS EXIT v lyc Sc Wc memc regs2 mem2 md2 pos CX (fxrel_frm0 fx fx1 HFRM Hfx)
  Hly HSc Hfin HPerm).
- unfold ent_snp_regs.
  repeat split;
    lazymatch goal with |- getr regs2 ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      transitivity (getr regsc r); [exact (HP2 z ltac:(unfold acallee_saved; lia)) | assumption] end.
- exact HJ2.
- exact HMEM.
- exact HMC.
- exact HBY.
- exact HRD.
- intros a Ha H1 H2. rewrite (HK2 a Ha H1 H2). apply EQV.
Qed.

(* the cut ENT_LBL at the ambient FP state *)
Lemma ent_lbl_at : (forall n, MF_HEAD_F B n) -> MF_EXIT_F B -> ENT_LBL_stmt B.
Proof.
intros HEADS EXIT. unfold ENT_LBL_stmt.
intros v lyc Sc Wc regs1 memc mdc pos CX HFRM Hly HSc Hfin HPerm HJ0 RG HMEM HMC HCB.
unfold mf_at.
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R26 & R27).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & Ht64 & _ & Hlp64 & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOS & _).
(* the seed at the label test: every register an atom, no region, no fact *)
set (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS MF_LBL sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MF_LBL)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (HAG : env_agree 32 (Ereg regs1 []) E)
  by (split; [intros k Hk; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hr).
pose proof HJ0 as HJ.
(* a register at the call, read off the symbolic state *)
Ltac ent_rg HS r Q :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Q;
  lazymatch type of Q with context [sr_get (ss_regs ?ss) ?r'] =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r') in change (sr_get (ss_regs ss) r') with e in Q end;
  cbn [ms_regs restrict mkst] in Q.
assert (UL : U E (SOff 20 0) = mv_lp v)
  by (rewrite U_SOff, (ER 20%nat (20%bv : bv 5) ltac:(lia) eq_refl), R20, Z.add_0_r, mf_w64_u by lia;
      apply zcanon_id; unfold M64; lia).
psrr_branch_pi RUNP BR HS.
- (* lp <> 0: the label *)
  assert (Hlp : mv_lp v <> 0).
  { rewrite YO0c.branch_ne in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    change (U E (SOff 20 0) <> U E (SLit 0)) in Hc. rewrite UL, U_SLit in Hc. exact Hc. }
  destruct (mv_lab v) as [l|] eqn:Hlab; [| try rewrite Hlab in HOS; cbn in HOS; contradiction].
  destruct (ent_lab_now v lyc Sc Wc memc mdc pos l CX Hly HPerm HJ0 HCB Hlab)
    as (Hlp0 & HSTR & HADDR & Hlen & HLOC & HDJ).
  paj_run_to_sh RUNTOP HS HJ MF_SNP.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a. unfold aview, mbyte, mrestrict. rewrite (HF (Z_to_bv 64 a) ltac:(intros (rr & Hin & _); exact Hin)).
    reflexivity. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 []
    ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) HS HAG ltac:(vm_compute; reflexivity)) as KR.
  ent_rg HS (10%bv : bv 5) Q10. ent_rg HS (11%bv : bv 5) Q11. ent_rg HS (12%bv : bv 5) Q12. ent_rg HS (13%bv : bv 5) Q13.
  pmkst HS.
  apply (ent_call HEADS EXIT v lyc Sc Wc memc (ms_regs ms) (ms_mem ms) _ pos (mv_lp v) l CX HFRM Hly HSc Hfin HPerm HJ
    HMEM HMC EQV).
  + unfold ent_snp_regs. repeat split; rewrite KR by (cbn [In]; tauto); assumption.
  + rewrite Q10, ent_denot_soff0, (ER 23%nat (23%bv : bv 5) ltac:(lia) eq_refl). exact R23.
  + rewrite Q11. reflexivity.
  + rewrite Q12, ent_denot_soff0. subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
    unfold w64. f_equal. exact (mf_val_fs VOBJS).
  + rewrite Q13, ent_denot_soff0, (ER 20%nat (20%bv : bv 5) ltac:(lia) eq_refl). exact R20.
  + rewrite Hlab. reflexivity.
  + exact Hlp0.
  + exact HSTR.
  + exact HADDR.
  + exact Hlen.
  + exact HLOC.
  + exact HDJ.
- (* lp = 0: the literal "reac-pw.conf" *)
  assert (Hlp : mv_lp v = 0).
  { rewrite YO0c.branch_ne in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    change (U E (SOff 20 0) = U E (SLit 0)) in Hc. rewrite UL, U_SLit in Hc. exact Hc. }
  destruct (mv_lab v) as [l|] eqn:Hlab; [try rewrite Hlab in HOS; destruct HOS as [Hn0 _]; contradiction |].
  pose proof (mf_lit_now_j B v lyc Sc Wc memc mdc pos S_base CX HJ0 ltac:(right; left; reflexivity)) as HL.
  destruct HL as (Hl0 & HLS & HLP & _ & HLI).
  pose proof (proj1 HJ0) as HAR.
  destruct HCH as (bc & mcn & Hbcin0 & Hbclo & Hbchi).
  assert (Hbcin : In (bc, mcn) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbcin0).
  pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mcn HAR Hbcin) as Hoff. unfold off_img in Hoff.
  assert (Hr : mcn <= req_size mcn) by (unfold req_size; destruct (Z.eqb_spec mcn 0); lia).
  assert (EBL : SegInstA.seg_litA_fz S_base = 0x210a0) by (vm_compute; reflexivity).
  assert (EBN : length S_base = 12%nat) by (vm_compute; reflexivity).
  pose proof (mfk_span_bounds (SegInstA.seg_litA_fz S_base) S_base) as HSP.
  paj_run_to_sh RUNTOP HS HJ MF_SNP.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
    apply awr_ok_nil. }
  assert (EQV : forall a, rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a. unfold aview, mbyte, mrestrict. rewrite (HF (Z_to_bv 64 a) ltac:(intros (rr & Hin & _); exact Hin)).
    reflexivity. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 []
    ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 26; 27]%bv : list (bv 5)) HS HAG ltac:(vm_compute; reflexivity)) as KR.
  ent_rg HS (10%bv : bv 5) Q10. ent_rg HS (11%bv : bv 5) Q11. ent_rg HS (12%bv : bv 5) Q12. ent_rg HS (13%bv : bv 5) Q13.
  pmkst HS.
  apply (ent_call HEADS EXIT v lyc Sc Wc memc (ms_regs ms) (ms_mem ms) _ pos (SegInstA.seg_litA_fz S_base) S_base
    CX HFRM Hly HSc Hfin HPerm HJ HMEM HMC EQV).
  + unfold ent_snp_regs. repeat split; rewrite KR by (cbn [In]; tauto); assumption.
  + rewrite Q10, ent_denot_soff0, (ER 23%nat (23%bv : bv 5) ltac:(lia) eq_refl). exact R23.
  + rewrite Q11. reflexivity.
  + rewrite Q12, ent_denot_soff0. subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
    unfold w64. f_equal. exact (mf_val_fs VOBJS).
  + rewrite Q13, ent_denot_soff0. subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia).
    unfold w64. f_equal. exact (mf_val_base VOBJS).
  + rewrite Hlab. reflexivity.
  + exact Hl0.
  + exact HLS.
  + exact (HLP _ _ _ _ _ HAR).
  + rewrite EBN. lia.
  + right; right. exact HLI.
  + unfold sa_disj, seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *. rewrite EBL in *. rewrite EBN in HSP.
    cbn [Z.of_nat Pos.of_succ_nat] in HSP. lia.
Qed.
End e.
End f.
End d.

(* the cut at every FP state *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf)
  SegInstA.gotwA SegInstA.guardA.

Lemma ent_lbl : (forall n, MF_HEAD_F B n) -> MF_EXIT_F B -> ENT_LBL_F B.
Proof.
intros HEADS EXIT fx0. exact (ent_lbl_at (fx := fx0) B VOBJS SSP ASNPRINTF HEADS EXIT).
Qed.
End i.
End h.
End g.

About ent_lbl.
Print Assumptions ent_lbl.
