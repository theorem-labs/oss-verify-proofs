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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 824 of its 867 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_b.v, with its module paths and module names changed; 223 of its 259 lines of code are new or changed and 831 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the middle of piece KWOK of segment A7 of
   reac_segconf_parse_file's walk, from trim's return to strlen's return or the F_noname refusal (segment A7's
   proof, 2026-10-30).
     w3_after_trim  0x88314  mv s9, a0                       s9 = np, the name trim left (pf_a7_w3_k.v w3_name_str)
                    0x88318 .. 0x88324  inline check #21 on np (decided by pf_a7_w3_s.v's shadow entry w3_SH 10 0)
                    0x88328  lbu a0, 0(s9)                   name[0] (pf_a7_w3_s.v's byte seed on atom 10, offset 0)
                    0x8832c  ld s3, 0x98(s1)                 s3 = pf_SH + 8 again (pf_a7_q.v's slot region a7_slot_r)
                    0x88330  beqz a0, 0x88784
                      empty name: 0x88784 .. 0x88794  a2 = F_noname's literal (listing object 66), a0 = c,
                        a1 = lineno, refuse (pf_a7_w3_c.v w3_refuse_step with pf_a7_s.v a7_refuse_site_88794), then
                        pf_a7_w3_l.v w3_to_fun at 0x88798 at refuse's FP state (the step by w3_post_noname);
                      else: 0x88334 mv a0, s9; 0x88338 jal strlen (pf_a7_w3_c.v w3_strlen_step), then
                        pf_a7_w3_l.v w3_after_strlen at 0x8833c.
   Section hypotheses: REF (refuse), ASTRLEN (row 16 at the listing's strlen trampoline) and TL (the runtime record
   PaArt asks), SIGP and OBJ (the listing's call targets and object atoms), VRO and SSPX only for w3_refuse_step's
   a6_base_move after the refuse calls (pf_a7_w3_c.v's head comment). *)
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
  pf_a7_w3_k pf_a7_w3_c pf_a7_w3_s pf_a7_w3_l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* trim's return at 0x88310 (listing offset) *)
Definition A7_RET_TRIM : Z := AF_reac_segconf_parse_file + 0x89c.   (* 0x88314 *)

(* a branch on an atom against zero *)
Lemma w3_br_eq0 : forall E n x b, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (x =? 0) = b.
Proof.
  intros E n x b H Hx Hc. rewrite branch_eq_U, (U_atom E n x H Hx), U_lit in Hc by lia. exact Hc.
Qed.
(* the run's obligations and write check, when there are none *)
Ltac w3_side :=
  first [ lazymatch goal with |- Forall _ (sh_obls _) => cbn [sh_obls]; constructor end
        | lazymatch goal with |- Forall _ [] => constructor end
        | lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => w3_awr end ].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a register atom of w3_E is the seed's register *)
Lemma w3_ewr : forall rX v pos z n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (w3_E rX v pos z) n = getr rX r.
Proof. intros rX v pos z n r Hn Hr. rewrite (w3_ew_lt47 rX v pos z n) by lia. exact (a7_ew_reg rX v pos n r Hr). Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after a refuse call (w3_refuse_step), used nowhere else *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section y.
Context {fx : YK11.FPState}.
(* the cut's c and cur_name below the allocator's ceiling: kept by a call that keeps every byte there *)
Lemma w3_st0_low : forall v pos lyc Sc Wc rX memc mdc (W' : world SEGS) mem' cf nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  (forall a, 0 <= a < alloc_ceiling -> rdW W' mem' a = rdW Wc memc a) ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos (rdW W' mem') cf nm k.
Proof.
  intros v pos lyc Sc Wc rX memc mdc W' mem' cf nm k HB K (HRC & HNM & HCNT).
  pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & _).
  pose proof HB as (_ & _ & HOBJ & _).
  pose proof HOBJ as (_ & _ & _ & _ & HCH & _).
  destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB))
    as (HF1 & HF2 & _ & _).
  split; [|split; [|exact HCNT]].
  - apply (reac_segconf_parse.sa_rconf_low (rdW Wc memc) (rdW W' mem') (p_c v) cf HRC);
      [unfold seg_spec.SEG_C_SIZE in *; lia | unfold seg_spec.SEG_C_SIZE in *; lia | exact K].
  - apply (a6_nm_move v pos (rdW Wc memc) (rdW W' mem') nm HNM).
    intros a Ha. change (fs_frame_bytes 5) with 2048 in Ha. apply K. lia.
Qed.


(** ** 0x88314: trim's return, name[0], the empty name or strlen *)
Lemma w3_after_trim : forall n v pos lyc Sc Wc regs mem md cf nm o ln d ci np,
  HA_FUN B n -> H_SEG B n ->
  pf_base B v pos lyc Sc Wc regs mem md PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st0 v pos (rdW Wc mem) cf nm (length (skipn o (p_s v))) ->
  strchr (pf_tline (p_s v) o) RBR = Some ci -> nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (a7_body (pf_tline (p_s v) o) ci) 0 = 9 ->
  getr regs 10 = w64 np ->
  sa_str (rdW Wc mem) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  pf_inb (pf_F v pos + PF_O_BUF) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  pf_rg regs ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + A7_RET_TRIM)) mem (seg_rom SEGS)) md)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Proof.
intros n v pos lyc Sc Wc regs mem md cf nm o ln d ci np HFUN HSEG HB HMID HST HCL HNUL HKW H7 H10 HSTR HINB HRG.
set (name := a7_name (a7_body (pf_tline (p_s v) o) ci)) in *.
pose proof (a5_geo B v pos lyc Sc Wc regs mem md PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc regs mem md PF_SC_LINE HB) as HFI.
pose proof HB as (_ & (HJ & _ & _ & _ & _ & _ & HFRM & _) & _).
pose proof HMID as (Ho & _ & _).
pose proof HST as (HRC & HNM & HCNT).
pose proof HINB as (HI1 & HI2).
pose proof (proj1 (a5_rg_app _ _ _) HRG) as (HR3 & HRM).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB1 & HB2 & HB3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
destruct (a7_frame_rng B v pos lyc Sc Wc mem md (a7_st_of_base B v pos lyc Sc Wc regs mem md HB))
  as (HF1 & HF2 & HF3 & HF4).
(* name[0] *)
pose proof (w3_name_hd _ np name HSTR) as Hz.
assert (Hz256 : 0 <= hd0 name < 256).
{ destruct (aview_byte SEGS (w_H Wc) mem np _ Hz) as (_ & _ & _ & Hr). exact Hr. }
rewrite <- (Z.add_0_r np) in Hz.
assert (Hq0 : a7_buf v pos <= np) by (unfold a7_buf; lia).
assert (Hqd : np + 0 < a7_buf v pos + 512) by (unfold a7_buf; lia).
pose proof (w3_seed B v pos lyc Sc Wc regs mem md A7_RET_TRIM 10%nat (10%bv : bv 5) np 0 (hd0 name) HB
  ltac:(lia) eq_refl H10 Hq0 ltac:(lia) Hqd Hz) as HS.
pose proof (w3_shok B v pos lyc Sc Wc regs mem md 10%nat (10%bv : bv 5) np 0 (hd0 name) HB
  ltac:(lia) eq_refl H10 Hq0 ltac:(lia) Hqd) as SHOK.
assert (HEI : img_env VAL A_LIM (w3_E regs v pos (hd0 name))) by apply w3_E_img.
assert (E47 : ew (w3_E regs v pos (hd0 name)) 47 = Z_to_bv 64 (hd0 name)) by apply w3_ew_47.
assert (HA0 := w3_E_agree regs v pos (hd0 name)).
pose proof (paj_run B LAWS) as RUN. pose proof (paj_branch (PI := PI)) as BR.
(* 0x88314 .. 0x88330 *)
paj_run_tok RUN HS HJ SHOK Bspan.
all: try w3_side.
w3_memf Hmem. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the name is empty: the F_noname refusal, 0x88784 .. 0x88794 *)
  pose proof (w3_br_eq0 _ 47 _ true E47 ltac:(lia) Hc) as Hz0. apply Z.eqb_eq in Hz0. clear Hc.
  rewrite (w3_post_noname cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW H7 Hz0).
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try w3_side.
  w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
  pmkst HS. rewrite Hmem2 in HJ |- *.
  lazymatch type of HS with st_ok _ ?En _ _ =>
    assert (HA1 : env_agree 32 (Ereg regs (a7_extra v pos ++ [Z_to_bv 64 (hd0 name)])) En) by (env_agree_chain HA0) end.
  pose proof (w3_kept_st fx _ _ _ regs _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 26; 27] HS HA1
    ltac:(vm_compute; reflexivity)) as KEEP.
  cbn [ms_regs restrict] in KEEP.
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
  prreg HS (12%bv : bv 5) N12. prreg HS (19%bv : bv 5) N19.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mm) _ => set (rS := rg) in *; set (mdS := mm) in * end.
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  assert (HPR1 : forall z, In z (map fst (a5_FI B v)) -> getr rS (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z))
    by (intros z Hz'; apply KEEP; cbn [a5_FI map fst In] in Hz' |- *; tauto).
  assert (HFI1 : pf_rg rS (a5_FI B v)).
  { unfold pf_rg in HFI |- *. rewrite Forall_forall in HFI |- *. intros [k x] Hk.
    cbn [fst snd]. rewrite (HPR1 k (in_map fst _ (k, x) Hk)). exact (HFI (k, x) Hk). }
  assert (HBc : pf_base B v pos lyc Sc Wc rS mem mdS PF_SC_LINE)
    by exact (w3_base_step B fx v pos lyc Sc Wc regs rS mem md mdS PF_SC_LINE HB HJ HFI1).
  assert (R10 : getr rS 10 = w64 (p_c v)).
  { rewrite N10, (w3_ewr regs v pos _ 24 24%bv ltac:(lia) eq_refl). exact (a5_rg_get regs _ 24 _ HR3 ltac:(w3_in)). }
  assert (R11 : getr rS 11 = w64 (ln + 1)).
  { rewrite N11, (w3_ewr regs v pos _ 26 26%bv ltac:(lia) eq_refl). exact (a5_rg_get regs _ 26 _ HRM ltac:(w3_in)). }
  assert (R12 : getr rS 12 = w64 (seg_litA_rc F_noname)).
  { rewrite N12. change 307%nat with (A_OBJ 66). exact (w3_lit_noname OBJ _ HEI). }
  assert (R1 : getr rS 1 = Z_to_bv 64 (BASE + A7_RET_NONAME)).
  { rewrite N1. unfold A7_RET_NONAME, AF_reac_segconf_parse_file. reflexivity. }
  assert (R19 : getr rS 19 = w64 (pf_SH v pos + 8)).
  { rewrite N19, (w3_ew_lt47 regs v pos _ 33) by lia. rewrite a7_ew_SH.
    rewrite unsigned_lit_small by (unfold kLowMemEnd, kHighShadowEnd in *; lia). reflexivity. }
  assert (HRS : pf_rg rS (PF_RL v pos ++ PF_RM v o ln)).
  { unfold PF_RL, PF_RM, pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 18 _ HR3 ltac:(w3_in)).
    - exact R19.
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 24 _ HR3 ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 27 _ HR3 ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 21 _ HRM ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 26 _ HRM ltac:(w3_in)). }
  pose proof (a7_st_of_base B v pos lyc Sc Wc rS mem mdS HBc) as HA7.
  pose proof (a7_refuse_site_88794 B v pos lyc Sc Wc mem mdS rS cf o ln d n HA7 HRC
    (a7_cnt_zero cf (p_s v) o Ho HCNT) HMID HFRM R10 R11 R12) as HCALL.
  apply (w3_refuse_step B REF VRO SSPX v pos lyc Sc Wc rS mem mdS (Z_to_bv 64 (BASE + A7_RET_NONAME))
    cf nm ln F_noname [] _ o HBc HCALL HNM R1).
  + apply ret_ok_codeptr_v; [unfold A7_RET_NONAME, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  + rewrite unsigned_lit_small by (unfold A7_RET_NONAME, AF_reac_segconf_parse_file; lia).
    unfold A7_RET_NONAME, AF_reac_segconf_parse_file. lia.
  + intros fx1 S2 W2 regs2 mem2 md2 Hfx1 HBr HP2 HRC2 HNM2.
    apply (w3_to_fun B (fx := fx1) n A7_RET_NONAME v pos lyc S2 W2 regs2 mem2 md2 _ nm o ln d
      (or_intror eq_refl) (HFUN fx1) HBr HMID).
    * split; [exact HRC2|]. split; [exact HNM2|].
      exact (a7_cnt_refuse_next cf (ln + 1) F_noname [] (p_s v) o Ho HCNT).
    * exact (a5_rg_pres rS regs2 _ HP2 (w3_fun_cs v pos o ln) HRS).
- (* a name: 0x88334 mv a0, s9; 0x88338 jal strlen *)
  pose proof (w3_br_eq0 _ 47 _ false E47 ltac:(lia) Hc) as Hz0. apply Z.eqb_neq in Hz0. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  all: try w3_side.
  w3_memf Hmem2. rewrite Hmem in Hmem2. clear HFr HG.
  pmkst HS. rewrite Hmem2 in HJ |- *.
  lazymatch type of HS with st_ok _ ?En _ _ =>
    assert (HA1 : env_agree 32 (Ereg regs (a7_extra v pos ++ [Z_to_bv 64 (hd0 name)])) En) by (env_agree_chain HA0) end.
  pose proof (w3_kept_st fx _ _ _ regs _ [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 26; 27] HS HA1
    ltac:(vm_compute; reflexivity)) as KEEP.
  cbn [ms_regs restrict] in KEEP.
  prreg HS (1%bv : bv 5) N1. prreg HS (10%bv : bv 5) N10. prreg HS (19%bv : bv 5) N19.
  prreg HS (25%bv : bv 5) N25.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) ?mm) _ => set (rS := rg) in *; set (mdS := mm) in * end.
  assert (HPR1 : forall z, In z (map fst (a5_FI B v)) -> getr rS (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z))
    by (intros z Hz'; apply KEEP; cbn [a5_FI map fst In] in Hz' |- *; tauto).
  assert (HFI1 : pf_rg rS (a5_FI B v)).
  { unfold pf_rg in HFI |- *. rewrite Forall_forall in HFI |- *. intros [k x] Hk.
    cbn [fst snd]. rewrite (HPR1 k (in_map fst _ (k, x) Hk)). exact (HFI (k, x) Hk). }
  assert (HBc : pf_base B v pos lyc Sc Wc rS mem mdS PF_SC_LINE)
    by exact (w3_base_step B fx v pos lyc Sc Wc regs rS mem md mdS PF_SC_LINE HB HJ HFI1).
  assert (R10 : getr rS 10 = w64 np) by (rewrite N10, (w3_ewr regs v pos _ 10 10%bv ltac:(lia) eq_refl); exact H10).
  assert (R1 : getr rS 1 = Z_to_bv 64 (BASE + A7_RET_STRLEN)).
  { rewrite N1. unfold A7_RET_STRLEN, AF_reac_segconf_parse_file. reflexivity. }
  assert (R19 : getr rS 19 = w64 (pf_SH v pos + 8)).
  { rewrite N19, (w3_ew_lt47 regs v pos _ 33) by lia. rewrite a7_ew_SH.
    rewrite unsigned_lit_small by (unfold kLowMemEnd, kHighShadowEnd in *; lia). reflexivity. }
  assert (R25 : getr rS 25 = w64 np) by (rewrite N25, (w3_ewr regs v pos _ 10 10%bv ltac:(lia) eq_refl); exact H10).
  assert (HRS : pf_rg rS (PF_RL v pos ++ PF_RM v o ln ++ [(25, np)])).
  { unfold PF_RL, PF_RM, pf_rg. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 18 _ HR3 ltac:(w3_in)).
    - exact R19.
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 24 _ HR3 ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 27 _ HR3 ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 21 _ HRM ltac:(w3_in)).
    - rewrite KEEP by w3_in. exact (a5_rg_get regs _ 26 _ HRM ltac:(w3_in)).
    - exact R25. }
  apply (w3_strlen_step B ASTRLEN TL v pos lyc Sc Wc rS mem mdS (Z_to_bv 64 (BASE + A7_RET_STRLEN)) np name _
    HBc R1).
  + apply ret_ok_codeptr_v; [unfold A7_RET_STRLEN, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  + exact R10.
  + exact HSTR.
  + exact HINB.
  + intros regs2 mem2 md2 HBr HP2 H10' HKm.
    assert (KLOW : forall a, 0 <= a < alloc_ceiling -> rdW Wc mem2 a = rdW Wc mem a).
    { intros a Ha. apply HKm; [lia | left; lia]. }
    apply (w3_after_strlen B REF SIGP OBJ VRO SSPX n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d ci np HFUN HSEG HBr
      HMID).
    * exact (w3_st0_low v pos lyc Sc Wc rS mem mdS Wc mem2 cf nm _ HBc KLOW HST).
    * exact HCL.
    * exact HNUL.
    * exact HKW.
    * exact H7.
    * exact Hz0.
    * assert (Hnp0 : 0 <= np) by (unfold PF_O_BUF in *; lia).
      assert (Hnp1 : np + Z.of_nat (length name) < alloc_ceiling) by (unfold PF_O_BUF in *; lia).
      exact (reac_segconf_parse.sa_str_low (rdW Wc mem) (rdW Wc mem2) np name HSTR Hnp0 Hnp1 KLOW).
    * exact HINB.
    * exact (a5_rg_pres rS regs2 _ HP2 (w3_seg_cs v pos o ln np) HRS).
    * exact H10'.
Qed.
End y.
End e.
End f.
End d.
