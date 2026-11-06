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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 327 of its 371 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the three kinds of CALL piece KWOK of segment A7 of
   reac_segconf_parse_file's walk makes, each as one step lemma from the cut facts at the callee's entry to the
   cut facts at its return (segment A7's proof, piece KWOK, 2026-10-30). The walk lib/A/Prog/pf_a7_w3.v applies
   them at
     0x88310  trim(body + 7)                         w3_trim_step    (trim_contract, PaNoChain.cl_callS_wide:
                                                                      trim writes one byte of the class-5 frame)
     0x88338  strlen(name)                           w3_strlen_step  (RtString.astrlen_realizes, PaArt.aj_art_at)
     0x8835c  refuse(c, lineno, F_toolong, name, 15) w3_refuse_step  (refuse_contract, PaFx.cl_callSF)
     0x88794  refuse(c, lineno, F_noname)            w3_refuse_step
   Each step's premises at the call come from the cut's pf_base (pf_pieces.v) and pf_a7_s.v's closed site lemmas
   (rule 1j-bis) or pf_a7_r.v's strlen bundle; the cut facts after the call are rebuilt by the shared kits:
   pf_a5_k.v's a5_move0 after trim and strlen (their writes miss A5's write set a5_Wrx: one byte of buf, the
   callee's window below s1), pf_a6_k.v's a6_keeps_refuse / a6_base_move after refuse (refuse writes the block c).
   No instruction of parse_file is walked here.

   Section hypotheses: TRIM, REF (the callee contracts at image A's numbers, every FP state), ASTRLEN (row 16 at
   the listing's strlen trampoline, every FP state), TL (the listing's runtime record: the errno cell PaArt needs),
   and VRO and SSPX, which ONLY w3_refuse_step uses, because pf_a6_k.v's a6_base_move takes them: after refuse the
   journal keeps an image byte only when it is not an owned static (YCbq.v ajournal's image clause), whether the
   stack-protector cells are owned statics is a record fact of listing stage 2 (SegRecCells.seg_rec_cells), and
   arodata_okP after refuse needs pa_relro_img (VRO). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_q pf_a7_s pf_a7_r
  pf_a7_w3_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* a reader reads an address modulo 2 ^ 64 *)
Lemma w3_view_wrap : forall segs H mem a, aview segs H mem a = aview segs H mem (a mod 2 ^ 64).
Proof.
  intros segs H mem a. unfold aview, mbyte.
  replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zmod_mod. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The cut facts and the shape A7's call sites state them in *)
(* pf_base names six registers only (sp, gp, tp, s0, s1, s6): another register file that agrees on them *)
Lemma w3_base_regs : forall v pos lyc Sc Wc rX rX' memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> pf_rg rX' (a5_FI B v) -> pf_base B v pos lyc Sc Wc rX' memc mdc sc.
Proof.
  intros v pos lyc Sc Wc rX rX' memc mdc sc (CX & (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) & OBJ & SL & FSH) HR.
  exact (conj CX (conj (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 HR))))))) (conj OBJ (conj SL FSH)))).
Qed.

(* the registers of pf_fi at a call (pf_rg states them at Z_to_bv 5 r, the code at the bv literal) *)
Lemma w3_fi_get : forall v rX, pf_rg rX (a5_FI B v) ->
  getr rX 2 = w64 (pf_s1 v) /\ getr rX 3 = w64 (as_gp B) /\
  getr rX 4 = w64 (as_tp B) /\ getr rX 8 = w64 (pf_sp0 v).
Proof.
  intros v rX H.
  pose proof (a5_rg_get rX _ 2 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E2.
  pose proof (a5_rg_get rX _ 3 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E3.
  pose proof (a5_rg_get rX _ 4 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E4.
  pose proof (a5_rg_get rX _ 8 _ H ltac:(unfold a5_FI; cbn [In]; tauto)) as E8.
  assert (Q2 : Z_to_bv 5 2 = (2%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q3 : Z_to_bv 5 3 = (3%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q4 : Z_to_bv 5 4 = (4%bv : bv 5)) by (apply bv_eq; reflexivity).
  assert (Q8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite Q2 in E2. rewrite Q3 in E3. rewrite Q4 in E4. rewrite Q8 in E8.
  exact (conj E2 (conj E3 (conj E4 E8))).
Qed.

(* c's bytes and cur_name kept off A5's write set (pf_a5_k.v a5_keep_st, without cur) *)
Lemma w3_keep_st0 : forall v pos lyc Sc Wc memc mdc (Wc' : world SEGS) memc' cf nm k,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc' memc' a = rdW Wc memc a) ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos (rdW Wc' memc') cf nm k.
Proof.
  intros v pos lyc Sc Wc memc mdc Wc' memc' cf nm k G HAR Hin Hly HK (b & m & Hb & H1 & H2)
    ((bs & Hbs & Henc) & (f & Hf & Hfe) & HN).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
  pose proof asan_consts as (AC1 & _).
  split; [|split; [|exact HN]].
  - exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as [Hl _].
    rewrite HK; [exact (Hbs i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia |].
    refine (a5_heap_out B v pos lyc Sc Wc memc mdc b m _ G HAR Hin Hly Hb _). unfold seg_spec.SEG_C_SIZE in *. lia.
  - exists f. split; [|exact Hfe]. intros i Hi. destruct Hfe as [Hl _].
    pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    pose proof STK_values as (_ & _ & _ & SPF & _).
    rewrite HK; [exact (Hf i Hi) | unfold PF_O_CN; lia |].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9.
    unfold a5_Wrx, a5_buf, PF_O_BUF, PF_O_CN. rewrite SPF in *. unfold kLowMemEnd, kHighShadowEnd in *.
    intros [W | [W | [W | W]]]; [lia | destruct W as [_ W]; lia | lia | destruct W as [_ W]; lia].
Qed.

(* a keep clause off a window [lo, s1) inside parse_file's own window and off one byte e of buf is a keep off
   every A5 write set *)
Lemma w3_keepW : forall v pos lo e (rd rd' : reader) sl shw,
  pf_sp0 v - STK_reac_segconf_parse_file <= lo -> a5_buf v pos <= e < a5_buf v pos + 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < pf_s1 v) -> ~ a = e -> rd' a = rd a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rd' a = rd a.
Proof.
  intros v pos lo e rd rd' sl shw Hlo He HK a Ha HW. apply HK; [exact Ha | |].
  - intros Hw. apply HW. left. lia.
  - intros ->. apply HW. right. right. left. exact He.
Qed.

Section calls.
(* the callee contracts (pf_pieces.v's list for A7), at image A's numbers, at every FP state *)
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
(* the listing's runtime record (the errno cell aj_art_at keeps apart) *)
Hypothesis TL : PALib B.
(* forced by pf_a6_k.v's a6_base_move after a refuse call, and used nowhere else (see the head comment) *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(** ** trim(body + 7) at 0x88310 *)
Lemma w3_trim_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw cf nm k bp body
  (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  pf_st0 v pos (rdW Wc memc) cf nm k ->
  sa_str (rdW Wc memc) bp body -> pf_inb (pf_F v pos + PF_O_BUF) bp body -> ~ In 0 body -> (7 <= length body)%nat ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  getr regsc 10 = w64 (bp + 7) ->
  (forall S2 (W2 : world SEGS) regs2 mem2 md2,
     pf_base B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE ->
     aregs_preserved regsc regs2 ->
     getr regs2 10 = w64 (w3_np bp body) ->
     pf_st0 v pos (rdW W2 mem2) cf nm k ->
     sa_str (rdW W2 mem2) (w3_np bp body) (a7_name body) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + AF_trim) regsc memc mdc) Q.
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw cf nm k bp body Q HB HST HS HI HN H7 R1 Hraw Hra4 R10 KC.
  pose proof (a5_geo B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & _).
  pose proof (a7_st_of_base B v pos lyc Sc Wc regsc memc mdc HB) as Hst.
  pose proof (a5_fi_regs B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as HRG.
  destruct (w3_fi_get v regsc HRG) as (R2 & R3 & R4 & R8).
  destruct (a7_stk B v pos lyc Sc Wc memc mdc Hst) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1 & Ho16).
  pose proof STK_values as (ST & _ & _ & SPF & _).
  destruct (a7_win B v pos lyc Sc Wc memc mdc STK_trim Hst ltac:(rewrite ST; unfold ESTACK; lia))
    as (Wn1 & Wn2 & Wn3).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof HB as (_ & (HJ & _) & HOBJ & _ & HFSH).
  pose proof HOBJ as (_ & _ & _ & _ & HCH & _).
  pose proof alloc_ceiling_lt as Hac.
  (* trim's premises (pf_a7_s.v's site lemma at 0x88310) *)
  destruct (a7_trim_site_ok B v pos lyc Sc Wc memc mdc regsc (bp + 7) (skipn 7 body) Hst R10
    (w3_skip7_str _ bp body HS H7)
    ltac:(destruct HI as [HI1 HI2]; unfold a7_buf, pf_inb; rewrite length_skipn; lia))
    as (HROD & _ & Hp64 & HTP & HEV).
  (* the frame chain at s1 *)
  destruct (a5_chain B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as [ch1 HCH1].
  (* where trim writes its NUL *)
  destruct (w3_name_facts body HN) as (HL & _ & _). rewrite length_skipn in HL.
  set (e := trim_end_addr (bp + 7) (skipn 7 body)).
  assert (He : bp + 7 <= e <= bp + Z.of_nat (length body)).
  { unfold e, trim_end_addr. change (r_trim (skipn 7 body)) with (a7_name body). lia. }
  destruct HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
  assert (Hsp : spZ regsc = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
  { unfold spZ. rewrite R2. rewrite a6_w64_u by lia. lia. }
  unfold cfg_at.
  eapply SRr_bind.
  { apply (cl_callS_wide B LAWS Wc regsc memc (w64 (BASE + AF_trim)) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      STK_trim [(e, e + 1)] EV_trim (pf_s1 v - pf_sp0 v) raw ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         getr regs2 10 = w64 (bp + 7 + Z.of_nat (seg_spec.trim_lead (skipn 7 body))) /\
         sa_bytes (rdW W2 mem2) (bp + 7)
           (seg_spec.zb (firstn (seg_spec.trim_lead (skipn 7 body) + length (r_trim (skipn 7 body)))
              (skipn 7 body)) ++ [seg_spec.ZERO]) /\
         sa_kept SEGS Wc memc W2 mem2 regsc STK_trim (fun a => a = e) /\
         sa_noalloc B lyc Sc ly2 S2) HJ Hsp Ho16).
    - lia.
    - rewrite ST. lia.
    - exact Wn3.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact Hraw.
    - exact Hra4.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite R8, a6_w64_u by lia. exact HCH1.
    - intros HPRE1. eapply SRr_mono.
      { exact (TRIM fx lyc Sc Wc regsc memc mdc ch1 (bp + 7) (skipn 7 body) HPRE1 HROD R10 Hp64 HTP HEV). }
      cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
      exists ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
      split; [exact HJ'|]. split; [exact HP' | exact HQ'].
    - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite Hly. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos).
      change (fs_frame_bytes 5) with 2048. lia.
    - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      exfalso. rewrite SPF in G1, Hw. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP & (H10' & HBY & HKP & HNA)).
  destruct HNA as (HPerm & -> & HSf).
  change (0 + EV_trim) with 0 in HJo.
  (* what trim kept: every byte off its window [s1 - STK_trim, s1) and off its NUL e *)
  assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) -> ~ a = e ->
    rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha Hw Hne. apply HKP; [exact Ha | | exact Hne]. unfold spZ in *. rewrite R2, a6_w64_u by lia. exact Hw. }
  assert (HeB : a5_buf v pos <= e < a5_buf v pos + 512) by (unfold a5_buf, PF_O_BUF; lia).
  assert (HKW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rdW W2 mem2 a = rdW Wc memc a).
  { intros sl shw. apply (w3_keepW v pos (pf_s1 v - STK_trim) e); [lia | exact HeB | exact HK0]. }
  (* every mapped byte stays mapped: the window by the callee's journal, e by trim's post, the rest kept *)
  assert (HV : forall a, rdW Wc memc a <> None -> rdW W2 mem2 a <> None).
  { assert (HV0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW W2 mem2 a <> None).
    { intros a Ha Hs.
      destruct (Z_lt_le_dec a (pf_s1 v - STK_trim)) as [Hlo | Hlo];
        [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
      3: { destruct (Z.eq_dec a e) as [-> | Hne]; [lia|]. rewrite (HK0 a Ha ltac:(lia) Hne). exact Hs. }
      1: { destruct (Z.eq_dec a e) as [-> | Hne].
           - assert (Hix : (seg_spec.trim_lead (skipn 7 body) + length (r_trim (skipn 7 body)) <
                 length (seg_spec.zb (firstn (seg_spec.trim_lead (skipn 7 body) + length (r_trim (skipn 7 body)))
                   (skipn 7 body)) ++ [seg_spec.ZERO]))%nat).
             { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn, length_skipn. cbn [length].
               change (r_trim (skipn 7 body)) with (a7_name body). lia. }
             pose proof (HBY _ Hix) as Ee. unfold e, trim_end_addr.
             rewrite Ee. discriminate.
           - rewrite (HK0 a Ha ltac:(lia) Hne). exact Hs. }
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      apply (aview_some_of_apresent SEGS). apply Hpres. lia. }
    intros a Hs. rewrite w3_view_wrap. rewrite w3_view_wrap in Hs.
    apply HV0; [apply Z.mod_pos_bound; lia | exact Hs]. }
  assert (HRG2 : pf_rg regs2 (a5_FI B v)) by exact (a5_rg_pres regsc regs2 _ HP (a5_FI_cs B v) HRG).
  assert (HFSH2 : pf_fsh (rdW W2 mem2) (pf_SH v pos) PF_SC_LINE)
    by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G (HKW true false) HFSH).
  pose proof (a5_move0 B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE S2 W2 regs2 mem2 md2 PF_SC_LINE HB HJo HSf HPerm
    (HKW true true) HV HRG2 HFSH2) as HB2.
  apply (KC S2 W2 regs2 mem2 md2 HB2 HP).
  - unfold w3_np. exact H10'.
  - exact (w3_keep_st0 v pos lyc Sc Wc memc mdc W2 mem2 cf nm k G HAR Hin Hly (HKW true true) HCH HST).
  - apply (w3_name_str SEGS (w_H Wc) memc (w_H W2) mem2 bp body HS H7 HBY).
    intros a Ha1 Ha2. unfold w3_np in Ha1. apply HK0.
    + split; [lia|]. lia.
    + lia.
    + unfold e, trim_end_addr. change (r_trim (skipn 7 body)) with (a7_name body). lia.
Qed.

(** ** strlen(name) at 0x88338 *)
Lemma w3_strlen_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw np nm'
  (Q : world SEGS -> config -> Prop),
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  getr regsc 1 = raw -> YK0s.ret_ok raw ->
  getr regsc 10 = w64 np ->
  sa_str (rdW Wc memc) np nm' -> pf_inb (pf_F v pos + PF_O_BUF) np nm' ->
  (forall regs2 mem2 md2,
     pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE ->
     aregs_preserved regsc regs2 ->
     getr regs2 10 = w64 (Z.of_nat (length nm')) ->
     (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc mem2 a = rdW Wc memc a) ->
     SRr SEGS Wc (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIG SS___interceptor_trampoline_strlen)) memc (seg_rom SEGS)) mdc) Q.
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw np nm' Q HB R1 Hraw R10 HS HI KC.
  pose proof (a5_geo B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & _).
  pose proof (a7_st_of_base B v pos lyc Sc Wc regsc memc mdc HB) as Hst.
  pose proof (a5_fi_regs B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as HRG.
  destruct (w3_fi_get v regsc HRG) as (R2 & R3 & R4 & R8).
  destruct (a7_stk B v pos lyc Sc Wc memc mdc Hst) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1 & Ho16).
  pose proof STK_values as (ST & _ & _ & SPF & _).
  destruct (a7_win B v pos lyc Sc Wc memc mdc ESTACK Hst ltac:(unfold ESTACK; lia)) as (Wn1 & Wn2 & Wn3).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof HB as (_ & (HJ & _) & _ & _ & HFSH).
  pose proof alloc_ceiling_lt as Hac.
  assert (Hsp1 : spZ regsc = pf_s1 v) by (unfold spZ; rewrite R2; apply a6_w64_u; lia).
  assert (Hsp : spZ regsc = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by lia.
  destruct (a7_strlen_pre_88338 B v pos lyc Sc Wc memc mdc regsc np nm' Hst Hsp1 ltac:(rewrite R1; exact Hraw)
    R3 R4 R10 HS HI) as (PRE & R10' & Hnp & STR & RD & TV & ROM).
  eapply SRr_bind.
  { apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False)
      (SIG SS___interceptor_trampoline_strlen) Wc regsc memc STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      (pf_s1 v - pf_sp0 v) raw (fun regs' _ => getr regs' 10 = w64 (astr_len (seg_spec.zb nm')))
      HJ Hsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) Wn3 R1 (fun a (H : False) => False_ind _ H)).
    exact (ASTRLEN fx lyc Sc Wc regsc memc mdc np (seg_spec.zb nm') PRE R10' Hnp STR RD TV ROM). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
  assert (HK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha Hw. apply HK2; [exact Ha | | tauto]. replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    exact Hw. }
  assert (HKW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rdW Wc mem2 a = rdW Wc memc a).
  { intros sl shw a Ha HW. apply HK0; [exact Ha|]. intros Hw. apply HW. left. rewrite SPF. unfold ESTACK in *.
    rewrite SPF in Wn3. lia. }
  assert (HV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
  { assert (HV0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
    { intros a Ha Hs.
      destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [Hlo | Hlo];
        [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
      - rewrite (HK0 a Ha ltac:(lia)). exact Hs.
      - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
        apply (aview_some_of_apresent SEGS). apply Hpres. unfold ESTACK in *. rewrite SPF in Wn3 |- *. lia.
      - rewrite (HK0 a Ha ltac:(lia)). exact Hs. }
    intros a Hs. rewrite w3_view_wrap. rewrite w3_view_wrap in Hs.
    apply HV0; [apply Z.mod_pos_bound; lia | exact Hs]. }
  assert (HRG2 : pf_rg regs2 (a5_FI B v)) by exact (a5_rg_pres regsc regs2 _ HP2 (a5_FI_cs B v) HRG).
  assert (HFSH2 : pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_LINE)
    by exact (a5_keep_fsh v pos _ _ true PF_SC_LINE G (HKW true false) HFSH).
  assert (HSf : exists f, Sc = set_fs f Sc) by (exists (st_fs Sc); destruct Sc; reflexivity).
  pose proof (a5_move0 B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2 HSf
    (Permutation_refl _) (HKW true true) HV HRG2 HFSH2) as HB2.
  apply (KC regs2 mem2 md2 HB2 HP2).
  - rewrite Ha02. unfold astr_len, seg_spec.zb. rewrite length_map. reflexivity.
  - intros a Ha Hlo. apply HK0; [exact Ha|]. unfold ESTACK in *. lia.
Qed.

(** ** refuse(c, lineno, f, ...) at 0x8835c and 0x88794 *)
Lemma w3_refuse_step : forall v pos lyc Sc Wc (regsc : bvmap 5 word) memc mdc raw cf nm ln f args st o,
  pf_base B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE ->
  a7_refuse_call B v lyc Sc Wc memc regsc cf ln f args ->
  pf_nm (rdW Wc memc) (pf_F v pos + PF_O_CN) nm ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall (fx1 : YK11.FPState) S2 (W2 : world SEGS) regs2 mem2 md2, fxrel fx fx1 ->
     pf_base (fx := fx1) B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE ->
     aregs_preserved regsc regs2 ->
     sa_rconf (rdW W2 mem2) (p_c v) (SegModel.refuse cf (ln + 1) f args) ->
     pf_nm (rdW W2 mem2) (pf_F v pos + PF_O_CN) nm ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2) (pf_postm (fx := fx1) B v st o ln)) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + AF_refuse) regsc memc mdc) (pf_postm B v st o ln).
Proof.
  intros v pos lyc Sc Wc regsc memc mdc raw cf nm ln f args st o HB HRC HNM R1 Hraw Hra4 KC.
  pose proof (a5_geo B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & _).
  pose proof (a7_st_of_base B v pos lyc Sc Wc regsc memc mdc HB) as Hst.
  pose proof (a5_fi_regs B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as HRG.
  destruct (w3_fi_get v regsc HRG) as (R2 & R3 & R4 & R8).
  destruct (a7_stk B v pos lyc Sc Wc memc mdc Hst) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1 & Ho16).
  pose proof STK_values as (_ & SR & _ & SPF & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
  pose proof HB as (_ & (HJ & _) & HOBJ & _ & _).
  pose proof HOBJ as (_ & _ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
  pose proof alloc_ceiling_lt as Hac.
  destruct HRC as (HROD & R10 & Hc64 & R11 & Hl64 & R12 & Hf64 & HPRE & HROOM & HEV).
  destruct (a5_chain B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE HB) as [ch1 HCH1].
  assert (Hsp : spZ regsc = pf_sp0 v + (pf_s1 v - pf_sp0 v)) by (unfold spZ; rewrite R2, a6_w64_u by lia; lia).
  unfold cfg_at.
  eapply SRr_bind.
  { apply (cl_callSF B LAWS Wc regsc memc (w64 (BASE + AF_refuse)) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc 0
      STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) raw ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         sa_rconf (rdW W2 mem2) (p_c v) (SegModel.refuse cf (ln + 1) f args) /\ sa_noalloc B lyc Sc ly2 S2)
      HJ Hsp Ho16).
    - lia.
    - rewrite SR. unfold ESTACK. lia.
    - rewrite SR, SPF. unfold ESTACK. lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact Hraw.
    - exact Hra4.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite R8, a6_w64_u by lia. exact HCH1.
    - intros HPRE1. eapply SRr_mono.
      { exact (REF fx lyc Sc Wc regsc memc mdc ch1 (p_c v) (ln + 1) (seg_litA_rc f) (ln + 1) cf f args HPRE1 HROD
          R10 Hc64 R11 Hl64 R12 Hf64 HPRE HROOM HEV). }
      cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
      apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hbc|].
      pose proof (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hm).
      pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
      unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJo & HJi & HP & (HRCN & HNA)).
  destruct HNA as (HPerm & -> & HSf).
  change (0 + EV_refuse) with 0 in HJo.
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJi by lia.
  pose proof (a6_keeps_refuse B v pos lyc Sc Wc regsc memc mdc PF_SC_LINE cf lyc S2 W2 mem2 md2 EV_refuse HB HJi HPerm)
    as HKS.
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 22] -> getr regs2 (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
  { intros r Hr. apply HP. unfold acallee_saved. cbn [In] in Hr. lia. }
  pose proof (a6_base_move B VRO SSPX fx1 v pos lyc Sc Wc regsc memc mdc PF_SC_LINE lyc S2 W2 regs2 mem2 md2 HB Hfx1
    HJo eq_refl HSf HPerm HKS KR) as HB2.
  pose proof HKS as (_ & _ & _ & K4).
  pose proof (a6_nm_move v pos _ _ nm HNM (fun a Ha => K4 a (or_introl Ha))) as HNM2.
  pose proof (KC fx1 S2 W2 regs2 mem2 md2 Hfx1 HB2 HP HRCN HNM2) as HC.
  unfold pf_postm, PF_POSTr in HC |- *.
  exact (srr_apost_baseF_lift SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ _ Hfx1 HC).
Qed.
End calls.
End e.
End f.
End d.
