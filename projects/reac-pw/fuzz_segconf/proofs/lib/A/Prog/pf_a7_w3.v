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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 90 of its 127 lines of code are new or changed and 416 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_l.v, with its module names changed; 212 of its 260 lines of code are new or changed and 79 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the piece KWOK of segment A7 of reac_segconf_parse_file's walk,
   `a7_w3 : A7_S_KWOK B` (lib/A/Prog/pf_a7_m.v). Segment A7's proof (piece KWOK), 2026-10-30.

   KWOK 0x882f0 (BASE + A7_KWOK): the header's body begins with "segment" (s3 = bp = the body):
     0x882f0 addi a0, s3, 7 ; 0x882f4 .. 0x88300  inline check #20 on body + 7 -- decided by pf_a7_w3_s.v's shadow
                                                  entry w3_SH 19 7 (the byte is in buf); its slow block 0x88acc and
                                                  the error path 0x88d50 are not reached
     0x88304 lbu a1, 0(a0)                         body[7] (pf_a7_w3_s.v's byte seed on atom 19, offset 7)
     0x88308 beq a1, s9, 0x88310 ; 0x8830c bne a1, s4, 0x880e4
                                  body[7] is neither '\t' (s9 = 9) nor ' ' (s4 = 0x20): UNK 0x880e4 (HA_UNK, the
                                  step by pf_a7_w3_k.v w3_post_unk), with s3 still the body;
                                  else the jal at 0x88310: trim(body + 7) through pf_a7_w3_c.v w3_trim_step, then
                                  pf_a7_w3_n.v w3_after_trim at 0x88314 (the name, F_noname, strlen, SEG, F_toolong).
   The piece walks 35 instructions of A7 (0x882f0 .. 0x88360 and 0x88784 .. 0x88798, in pf_a7_w3.v, pf_a7_w3_n.v and
   pf_a7_w3_l.v); the slow blocks of checks #20 / #21 (0x88acc .. 0x88ae0) and their error paths (0x88d50, 0x88d54)
   are decided unreachable by the shadow entries.

   Section hypotheses (each the callee or listing fact its step needs):
     TRIM     trim_contract at image A's numbers (0x88310)
     REF      refuse_contract at image A's numbers (0x8835c, 0x88794)
     ASTRLEN  RtString.astrlen_realizes at the listing's strlen trampoline (0x88338), the interceptor owner's row 16
     TL       PALib B, the runtime record's errno cell PaArt.aj_art_at asks (0x88338)
     SIGP     SegObj.seg_sig_prog (the call targets pa_sigma SS_trim / SS_refuse are BASE + AF_trim / AF_refuse)
     OBJ      SegObj.seg_val_objs (A_OBJ 49 = F_toolong at 0x88344, A_OBJ 66 = F_noname at 0x88784)
     VRO, SSPX  FORCED by pf_a6_k.v's a6_base_move after the two refuse calls, and used nowhere else: refuse's post
              gives only its journal, which keeps an image byte only when it is not an owned static (YCbq.v ajournal),
              and arodata_okP there needs pa_relro_img. Listing stage 2 (SegRecCells.seg_rec_cells, after the
              image-A owner's AF0m) discharges both, in lib/A/Prog/reac_segconf_parse.v's SSPX shape. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_d pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_m pf_a7_q pf_a7_s
  pf_a7_w3_k pf_a7_w3_c pf_a7_w3_s pf_a7_w3_l pf_a7_w3_n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a branch between two atoms of known value *)
Lemma w3_br_eqa : forall E n m x y b, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = b -> (x =? y) = b.
Proof.
  intros E n m x y b Hn Hm Hx Hy Hc. rewrite branch_eq_U, (U_atom E n x Hn Hx), (U_atom E m y Hm Hy) in Hc. exact Hc.
Qed.
Lemma w3_br_nea : forall E n m x y b, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = b -> negb (x =? y) = b.
Proof.
  intros E n m x y b Hn Hm Hx Hy Hc. rewrite branch_ne_U, (U_atom E n x Hn Hx), (U_atom E m y Hm Hy) in Hc. exact Hc.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after the refuse calls (w3_refuse_step), used nowhere else *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section y.
Context {fx : YK11.FPState}.

(** ** 0x88310: trim(body + 7), then w3_after_trim at its return *)
Lemma w3_kw_trim : forall n v pos lyc Sc Wc rS mem md cf nm o ln d ci bp,
  HA_FUN B n -> H_SEG B n ->
  pf_base B v pos lyc Sc Wc rS mem md PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st0 v pos (rdW Wc mem) cf nm (length (skipn o (p_s v))) ->
  strchr (pf_tline (p_s v) o) RBR = Some ci -> nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 9 ->
  sa_str (rdW Wc mem) bp (a7_body (pf_tline (p_s v) o) ci) ->
  pf_inb (pf_F v pos + PF_O_BUF) bp (a7_body (pf_tline (p_s v) o) ci) ->
  getr rS 1 = Z_to_bv 64 (BASE + A7_RET_TRIM) -> getr rS 10 = w64 (bp + 7) ->
  pf_rg rS ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + AF_trim) rS mem md)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
intros n v pos lyc Sc Wc rS mem md cf nm o ln d ci bp HFUN HSEG HB HMID HST HCL HNUL HKW H7 HSTR HINB R1 R10 HRG.
set (body := a7_body (pf_tline (p_s v) o) ci) in *.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB1 & HB2 & HB3).
assert (HN : ~ In 0 body) by apply a7_body_nul.
pose proof (a7_kw_len7 body HN HKW) as H7l.
apply (w3_trim_step B TRIM v pos lyc Sc Wc rS mem md (Z_to_bv 64 (BASE + A7_RET_TRIM)) cf nm _ bp body _
  HB HST HSTR HINB HN H7l R1).
- apply ret_ok_codeptr_v; [unfold A7_RET_TRIM, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
- rewrite unsigned_lit_small by (unfold A7_RET_TRIM, AF_reac_segconf_parse_file; lia).
  unfold A7_RET_TRIM, AF_reac_segconf_parse_file. lia.
- exact R10.
- intros S2 W2 regs2 mem2 md2 HBr HP2 H10' HST2 HSTR2.
  apply (w3_after_trim B REF ASTRLEN TL SIGP OBJ VRO SSPX n v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d ci
    (w3_np bp body) HFUN HSEG HBr HMID HST2 HCL HNUL HKW H7 H10' HSTR2).
  + exact (w3_name_inb _ bp body HINB HN H7l).
  + apply (a5_rg_pres rS regs2 _ HP2); [|exact HRG].
    apply Forall_app; split; [|apply a5_RM_cs].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

(** ** KWOK 0x882f0: body[7], then UNK or the trim call *)
Lemma w3_kwok : forall n, HA_FUN B n -> HA_UNK B n -> HA_SEG B n -> H_KWOK B n.
Proof.
intros n HFUN HUNK HSEG. unfold H_KWOK.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci bp HINV.
destruct HINV as (HB & HMID & HST & HLEN & HCL & HNUL & HKW & HSTR & HINB & HRG).
set (body := a7_body (pf_tline (p_s v) o) ci) in *.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _) & _).
pose proof HINB as (HI1 & HI2).
pose proof (proj1 (a5_rg_app _ _ _) HRG) as (HR6 & HRM).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB1 & HB2 & HB3).
pose proof alloc_ceiling_lt as Hac.
destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB))
  as (HF1 & HF2 & HF3 & HF4).
assert (HN : ~ In 0 body) by apply a7_body_nul.
pose proof (a7_kw_len7 body HN HKW) as H7l.
assert (R19 : getr rX (19%bv : bv 5) = w64 bp) by exact (a5_rg_get rX _ 19 _ HR6 ltac:(w3_in)).
(* body[7] *)
set (z := nth 7 body 0) in *.
pose proof (w3_byte7 _ bp body HSTR H7l) as Hz.
assert (Hz256 : 0 <= z < 256).
{ destruct (aview_byte SEGS (w_H Wc) memc _ _ Hz) as (_ & _ & _ & Hr). exact Hr. }
assert (Hq0 : a7_buf v pos <= bp) by (unfold a7_buf; lia).
assert (Hqd : bp + 7 < a7_buf v pos + 512) by (unfold a7_buf; lia).
assert (Hbp64 : 0 <= bp < 2 ^ 64) by (unfold PF_O_BUF in *; lia).
pose proof (w3_seed B v pos lyc Sc Wc rX memc mdc A7_KWOK 19%nat (19%bv : bv 5) bp 7 z HB
  ltac:(lia) eq_refl R19 Hq0 ltac:(lia) Hqd Hz) as HS.
pose proof (w3_shok B v pos lyc Sc Wc rX memc mdc 19%nat (19%bv : bv 5) bp 7 z HB
  ltac:(lia) eq_refl R19 Hq0 ltac:(lia) Hqd) as SHOK.
assert (HEI : img_env VAL A_LIM (w3_E rX v pos z)) by apply w3_E_img.
assert (E47 : ew (w3_E rX v pos z) 47 = Z_to_bv 64 z) by apply w3_ew_47.
assert (E25 : ew (w3_E rX v pos z) 25 = Z_to_bv 64 9)
  by (rewrite (w3_ewr rX v pos z 25 25%bv ltac:(lia) eq_refl); exact (a5_rg_get rX _ 25 _ HR6 ltac:(w3_in))).
assert (E20 : ew (w3_E rX v pos z) 20 = Z_to_bv 64 32)
  by (rewrite (w3_ewr rX v pos z 20 20%bv ltac:(lia) eq_refl); exact (a5_rg_get rX _ 20 _ HR6 ltac:(w3_in))).
assert (HA0 := w3_E_agree rX v pos z).
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + A7_KWOK)) with (Z_to_bv 64 (BASE + A7_KWOK)).
(* 0x882f0 .. 0x88308 *)
(* the trim call, from either arm that reaches 0x88310 *)
assert (TRIMC : nth 7 body 0 = 32 \/ nth 7 body 0 = 9 ->
  forall ms mdq, ms_mem ms = memc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdq 0 ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
     getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A7_RET_TRIM) -> getr (ms_regs ms) 10 = w64 (bp + 7) ->
  SRr SEGS Wc (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_trim)) (ms_mem ms) (seg_rom SEGS)) mdq)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln)).
{ intros H7 ms mdq Hm HJq KEEP R1 R10. rewrite Hm.
  pose proof (w3_pres_of_keep rX (ms_regs ms) KEEP) as HPR.
  apply (w3_kw_trim n v pos lyc Sc Wc (ms_regs ms) memc mdq cf nm o ln d ci bp HFUN (HSEG fx)).
  - exact (w3_base_step B fx v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJq
      (a5_rg_pres rX (ms_regs ms) _ HPR (a5_FI_cs B v) HFI)).
  - exact HMID.
  - exact HST.
  - exact HCL.
  - exact HNUL.
  - exact HKW.
  - exact H7.
  - exact HSTR.
  - exact HINB.
  - exact R1.
  - exact R10.
  - apply (a5_rg_pres rX (ms_regs ms) _ HPR).
    + apply Forall_app; split; [|apply a5_RM_cs].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
    + apply (proj2 (a5_rg_app _ _ _)). split; [|exact HRM].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      * exact (a5_rg_get rX _ 18 _ HR6 ltac:(w3_in)).
      * exact (a5_rg_get rX _ 24 _ HR6 ltac:(w3_in)).
      * exact (a5_rg_get rX _ 27 _ HR6 ltac:(w3_in)). }
paj_run_tok RUN HS HJ SHOK Bspan.
all: try w3_side.
w3_memf Hmem. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* body[7] = '\t': 0x88310 jal trim *)
  pose proof (w3_br_eqa _ 47 25 z 9 true E47 E25 ltac:(lia) ltac:(lia) Hc) as H9. apply Z.eqb_eq in H9. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try w3_side.
  w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
  pmkst HS. rewrite Hmem2 in HJ.
  lazymatch type of HS with st_ok _ ?En _ _ =>
    assert (HA1 : env_agree 32 (Ereg rX (a7_extra v pos ++ [Z_to_bv 64 z])) En) by (env_agree_chain HA0) end.
  pose proof (w3_kept_st fx _ _ _ rX _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HA1
    ltac:(vm_compute; reflexivity)) as KEEP.
  cbn [ms_regs restrict] in KEEP.
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10.
  rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
  apply (TRIMC (or_intror H9) _ _ Hmem2 HJ KEEP).
  + rewrite N1. unfold A7_RET_TRIM, AF_reac_segconf_parse_file. reflexivity.
  + rewrite N10, (w3_ewr rX v pos z 19 19%bv ltac:(lia) eq_refl), R19. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
- pose proof (w3_br_eqa _ 47 25 z 9 false E47 E25 ltac:(lia) ltac:(lia) Hc) as H9. apply Z.eqb_neq in H9. clear Hc.
  (* 0x88308 not taken, to the bne at 0x8830c *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try w3_side.
  w3_memf HmemB. rewrite Hmem in HmemB. clear HFr HG Hmem. rename HmemB into Hmem.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* neither blank: UNK 0x880e4 *)
    pose proof (w3_br_nea _ 47 20 z 32 true E47 E20 ltac:(lia) ltac:(lia) Hc) as H32.
    apply Bool.negb_true_iff, Z.eqb_neq in H32. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A7_UNK.
    all: try w3_side.
    w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
    pmkst HS. rewrite Hmem2 in HJ |- *.
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      assert (HA1 : env_agree 32 (Ereg rX (a7_extra v pos ++ [Z_to_bv 64 z])) En) by (env_agree_chain HA0) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HA1
      ltac:(vm_compute; reflexivity)) as KEEP0.
    cbn [ms_regs restrict] in KEEP0.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mm) _ => set (rS := rg) in *; set (mdS := mm) in * end.
    assert (KEEP : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
      getr rS (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k))
      by (intros k Hk; exact (KEEP0 (Z_to_bv 5 k) (in_map _ _ _ Hk))).
    pose proof (w3_pres_of_keep rX rS KEEP) as HPR.
    apply (HUNK fx v pos lyc Sc Wc rS memc mdS cf nm o ln d bp body).
    split; [exact (w3_base_step B fx v pos lyc Sc Wc rX rS memc mdc mdS PF_SC_LINE HB HJ
      (a5_rg_pres rX rS _ HPR (a5_FI_cs B v) HFI))|].
    split; [exact HMID|]. split; [exact HST|]. split; [exact HSTR|]. split; [exact HINB|].
    split; [exact (w3_post_unk cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL H32 H9)|].
    apply (a5_rg_pres rX rS _ HPR).
    * apply Forall_app; split; [|apply a5_RM_cs].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
    * apply (proj2 (a5_rg_app _ _ _)). split; [|exact HRM].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      -- exact (a5_rg_get rX _ 18 _ HR6 ltac:(w3_in)).
      -- exact (a5_rg_get rX _ 24 _ HR6 ltac:(w3_in)).
      -- exact (a5_rg_get rX _ 27 _ HR6 ltac:(w3_in)).
      -- exact (a5_rg_get rX _ 19 _ HR6 ltac:(w3_in)).
  + (* body[7] = ' ' *)
    pose proof (w3_br_nea _ 47 20 z 32 false E47 E20 ltac:(lia) ltac:(lia) Hc) as H32.
    apply Bool.negb_false_iff, Z.eqb_eq in H32. clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    all: try w3_side.
    w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
    pmkst HS. rewrite Hmem2 in HJ.
    lazymatch type of HS with st_ok _ ?En _ _ =>
      assert (HA1 : env_agree 32 (Ereg rX (a7_extra v pos ++ [Z_to_bv 64 z])) En) by (env_agree_chain HA0) end.
    pose proof (w3_kept_st fx _ _ _ rX _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HA1
      ltac:(vm_compute; reflexivity)) as KEEP.
    cbn [ms_regs restrict] in KEEP.
    prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10.
    rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
    replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
    apply (TRIMC (or_introl H32) _ _ Hmem2 HJ KEEP).
    * rewrite N1. unfold A7_RET_TRIM, AF_reac_segconf_parse_file. reflexivity.
    * rewrite N10, (w3_ewr rX v pos z 19 19%bv ltac:(lia) eq_refl), R19. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity.
Qed.
End y.

(** ** The piece, as pf_a7_m.v states it *)
Theorem a7_w3 : A7_S_KWOK B.
Proof. intros f0 n HFUN HUNK HSEG. exact (w3_kwok (fx := f0) n HFUN HUNK HSEG). Qed.

End e.
End f.
End d.
