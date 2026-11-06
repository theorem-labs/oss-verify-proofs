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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 211 of its 251 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the LONG walk of segment A6 of reac_segconf_parse_file's walk
   AFTER the strspn call, 0x87e38 .. the REF3 cut 0x87e74 (lib/A/Prog/pf_pieces.v H_REF3). Segment A6's proof
   (its LONG walk), 2026-10-30.
     0x87e38 bgeu a0, s7, 0x87e64   span >= len: to 0x87e64 (s4 kept)
     0x87e3c add a0, s9, a0          a0 = at + span
     0x87e40 srli a1, a0, 3 ; 0x87e44 add a1, a1, s6 ; 0x87e48 lb a1, 0(a1) ; 0x87e4c bnez a1, errpath
                                     check #3: the shadow byte of at[span], decided by the shadow entry of the text
     0x87e50 lbu a0, 0(a0) ; 0x87e54 addi a0, a0, -0x5b ; 0x87e58 seqz ; 0x87e5c addi -1 ; 0x87e60 and s4, a0, s4
                                     s4 = (at[span] = '[') ? 0 : cur (pf_a6_k.v A6_MASK, a6_mask_U)
     0x87e64 addi a3, zero, 0x1ff ; 0x87e68 mv a0, s8 ; 0x87e6c mv a1, s10 ; 0x87e70 ld a2, 0xa0(s1)
   then the cut REF3 at 0x87e74 with F_long, 511 and cur' (pfA_facts.r_line_long_rest), where H_REF3 applies.
   a6l_after: from the cut facts at 0x87e38 (pf_base, the line's spine, a0 = span = strspn_blank of the rest of the
   text, s7 = len, s9 = at, s4 = cur) to H_LONG's post. The span >= len arm runs the plain executor from
   pf_a6_l_q.v's a6l_seedA; the span < len arm runs the token executor from a6l_seedB (Bx = s6, the shadow entry of
   at[span] from the text's range_addressable in pf_obj's sa_addr). No memory is written (no region of either seed
   has a write window), so the state at REF3 has the cut's memory, and pf_base there is the cut's with the run's
   journal and register file. No Section hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a6_k pf_a6_l_q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma a6l_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0 = nth (k + i) l 0.
Proof.
induction l as [|x l IH]; intros k i.
- destruct k; cbn; destruct i; reflexivity.
- destruct k as [|k]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

(* the runs write nothing: every region of the seeds is read-only *)
Local Ltac a6l_awr := lazymatch goal with |- awr_ok ?sg ?b ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg b Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Local Ltac a6l_mem HF :=
  apply functional_extensionality; let x := fresh "x" in intros x; unfold frame_of in HF; rewrite HF; [reflexivity|];
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); vm_compute in Hr;
  repeat (let Hq := fresh "Hq" in destruct Hr as [Hq | Hr]; [subst r; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]);
  destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the token run's environment after two token atoms (1024, 1025) agrees with the registers below 32 *)
Lemma a6l_agree2 : forall rX ex w w0,
  env_agree 32 (Ereg rX ex) (ewset (ewset (a6l_E rX ex) 1024 w) 1025 w0).
Proof.
intros rX ex w w0. split.
- intros k Hk. rewrite !ew_ewset_other by lia. exact (proj1 (a6l_E_agree rX ex) k Hk).
- rewrite !ed_ewset. exact (proj2 (a6l_E_agree rX ex)).
Qed.
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* pf_base names six registers only, and its journal at the cut's memory: another register file that agrees on them
   and the journal a run returned *)
Lemma a6l_base_at : forall v pos lyc Sc Wc rX rX' memc mdc mdc' sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc mdc' sc.
Proof.
intros v pos lyc Sc Wc rX rX' memc mdc mdc' sc (CX & (_ & H2 & H3 & H4 & H5 & H6 & H7 & _) & OBJ & SL & FSH) HJ' HR.
exact (conj CX (conj (conj HJ' (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 HR))))))) (conj OBJ (conj SL FSH)))).
Qed.
(* a register list over registers a run kept *)
Lemma a6l_rg_keep : forall (rX rX' : bvmap 5 word) L,
  pf_rg rX L -> (forall rv, In rv L -> getr rX' (Z_to_bv 5 (fst rv)) = getr rX (Z_to_bv 5 (fst rv))) ->
  pf_rg rX' L.
Proof.
intros rX rX' L H K. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (K rv Hin). exact (H rv Hin).
Qed.

Theorem a6l_after : forall n, H_REF3 B n ->
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) ->
  (512 <= length (pf_line (p_s v) o))%nat ->
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, pf_cur_ptr (p_c v) cur); (25, p_t v + Z.of_nat o); (23, Z.of_nat (length (pf_line (p_s v) o)))]) ->
  getr rX 10 = w64 (Z.of_nat (strspn_blank (skipn o (p_s v)))) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (PF_LONG + 12)) rX memc mdc)
    (pf_postm B v (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) o ln).
Proof.
intros n HREF3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HB HMID HST HL HRG R10.
pose proof (a5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HNZ & HLS & HSTR & HADDR & HHT & HHC).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _).
pose proof HMID as (Ho & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (r_line_long_rest cf cur nm (ln + 1) (p_s v) o HNZ HL).
(* the line, the span and their lengths *)
assert (HLr : (length (pf_line (p_s v) o) <= length (skipn o (p_s v)))%nat) by apply pf_line_len_le.
assert (HLs : length (skipn o (p_s v)) = (length (p_s v) - o)%nat) by apply pfa_len_skipn.
pose proof (O2_strspn_rest_holds (skipn o (p_s v)) (nulfree_skipn o (p_s v) HNZ)) as (HNLc & HSPeq).
assert (HSPle : (strspn_blank (skipn o (p_s v)) <= length (pf_line (p_s v) o))%nat).
{ rewrite HSPeq. unfold pf_line, strspn_blank.
  pose proof (cut_nul_len (fst (break_nl (skipn o (p_s v))))).
  pose proof (pfa_takewhile_len blank (cut_nul (fst (break_nl (skipn o (p_s v)))))). lia. }
set (sp := strspn_blank (skipn o (p_s v))) in *.
set (L := length (pf_line (p_s v) o)) in *.
assert (HLSz : Z.of_nat (length (p_s v)) <= 65535) by (apply Nat2Z.inj_le in HLS; exact HLS).
(* the registers the cut names *)
assert (R23 : getr rX 23 = w64 (Z.of_nat L))
  by exact (a5_rg_get rX _ 23 (Z.of_nat L) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
assert (R25 : getr rX 25 = w64 (p_t v + Z.of_nat o))
  by exact (a5_rg_get rX _ 25 (p_t v + Z.of_nat o) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
assert (R24 : getr rX 24 = w64 (p_c v))
  by exact (a5_rg_get rX _ 24 (p_c v) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
assert (R26 : getr rX 26 = w64 (ln + 1))
  by exact (a5_rg_get rX _ 26 (ln + 1) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
assert (R20 : getr rX 20 = w64 (pf_cur_ptr (p_c v) cur))
  by exact (a5_rg_get rX _ 20 (pf_cur_ptr (p_c v) cur) HRG
    ltac:(unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right]))).
assert (R22 : getr rX 22 = w64 SHADOW_OFF)
  by exact (a5_rg_get rX _ 22 SHADOW_OFF HFI
    ltac:(unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right]))).
(* the text's block *)
destruct HADDR as (A0 & A1 & A2 & A3 & A4).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (pf_len v) HAR HHT ltac:(unfold pf_len; lia))
  as (bt & mt & Hbin & Hb1 & Hb2 & Hb3 & Hb4 & Hbapp).
unfold pf_len in Hb2.
change (cfg_at SEGS (BASE + (PF_LONG + 12)) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + (PF_LONG + 12))) memc (seg_rom SEGS)) mdc).
destruct (Nat.lt_ge_cases sp L) as [Hlt | Hge].
- (* span < len: check #3 and the '[' mask *)
  set (b := nth sp (skipn o (p_s v)) 0) in *.
  assert (Hrd : rdW Wc memc (p_t v + Z.of_nat o + Z.of_nat sp) = Some b).
  { destruct HSTR as ((HZS & _) & _).
    replace (p_t v + Z.of_nat o + Z.of_nat sp) with (p_t v + Z.of_nat (o + sp)) by lia.
    rewrite (HZS (o + sp)%nat) by (rewrite length_app; cbn [length]; lia).
    unfold b. rewrite a6l_nth_skipn. f_equal. apply app_nth1. lia. }
  destruct (aview_byte SEGS (w_H Wc) memc _ _ Hrd) as (_ & _ & _ & Hbr).
  pose proof (a6l_seedB B v pos lyc Sc Wc rX memc mdc (Z.of_nat sp) (Z.of_nat L) (p_t v + Z.of_nat o) b HB
    R10 R23 R25 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrd Hbr) as HS.
  set (ex := [Z_to_bv 64 (p_t v + Z.of_nat o + Z.of_nat sp); Z_to_bv 64 b]) in *.
  assert (HEI : img_env VAL A_LIM (a6l_E rX ex)) by apply a6l_E_img.
  assert (SHOK : sh_ok SEGS a6l_Bx a6l_SH (a6l_E rX ex) (mrestrict (w_H Wc) memc)).
  { unfold sh_ok, a6l_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H Wc) memc (a6l_E rX ex) a6l_Bx 32%nat (p_t v) (Z.of_nat (length (p_s v)) + 1)
      (p_t v + Z.of_nat o + Z.of_nat sp) 0 1 A3).
    - unfold a6l_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
      rewrite (a6l_ew_reg rX ex 22 (Z_to_bv 5 22) eq_refl). exact R22.
    - apply U_atom; [exact (a6l_ew_extra rX ex 0 ltac:(unfold A_TEXT; lia)) | lia].
    - lia.
    - lia.
    - intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_REF3.
  { a6l_awr. }
  assert (Hmem : ms_mem ms = memc) by a6l_mem HF.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *. clear HF HFr HG.
  (* the registers *)
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX ex
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 26; 27]) HS (a6l_agree2 rX ex _ _)
    ltac:(vm_compute; reflexivity)) as HK0.
  assert (HK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
  { intros k Hk. apply HK0. apply in_map. exact Hk. }
  prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 12) Q12. prreg HS (Z_to_bv 5 13) Q13.
  pose proof (st_ok_pi_restrict_reg (w_H Wc) _ _ ms (Z_to_bv 5 20) HS) as Q20.
  lazymatch type of Q20 with _ = sv_denot ?Ex ?t =>
    let e := eval vm_compute in t in change t with e in Q20;
    change e with A6_MASK in Q20;
    assert (U33 : U Ex (SOff 33 0) = b);
    [ apply U_atom; [rewrite !ew_ewset_other by lia; exact (a6l_ew_extra rX ex 1 ltac:(unfold A_TEXT; lia)) | lia] |];
    assert (U20 : U Ex (SOff 20 0) = bv_unsigned (getr rX 20));
    [ rewrite U_SOff, !ew_ewset_other by lia; rewrite (a6l_ew_reg rX ex 20 20%bv eq_refl), Z.add_0_r;
      apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr rX 20)) as Rg; change (bv_modulus 64) with M64 in Rg;
      lia |];
    pose proof (a6_mask_U Ex b (bv_unsigned (getr rX 20)) U33 Hbr U20
      ltac:(pose proof (bv_unsigned_in_range 64 (getr rX 20)) as Rg; change (bv_modulus 64) with (2 ^ 64) in Rg; lia))
      as HMU;
    rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot Ex A6_MASK)) in Q20;
    change (bv_unsigned (sv_denot Ex A6_MASK)) with (U Ex A6_MASK) in Q20;
    rewrite HMU in Q20
  end.
  lazymatch goal with |- SRr ?s ?w _ ?Q => change (SRr s w (cfg_at SEGS (BASE + PF_REF3) (ms_regs ms) memc mdq) Q) end.
  apply (HREF3 v pos lyc Sc Wc (ms_regs ms) memc mdq cf (if b =? 91 then None else cur) nm o ln d F_long
    (seg_litA_rc F_long) [AI 511] 511).
  split; [|split; [exact HMID|split; [|split]]].
  + apply (a6l_base_at v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ).
    apply (a6l_rg_keep rX (ms_regs ms) _ HFI). intros rv Hin. apply HK.
    unfold a5_FI in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; repeat (first [left; reflexivity | right]) |]). destruct Hin.
  + destruct HST as (S1 & S2 & S3 & S4). split; [exact S1|]. split; [|exact (conj S3 S4)].
    destruct (b =? 91); [exact I | exact S2].
  + left. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  + unfold pf_rg, PF_RL, PF_RM. cbn [app].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    all: first
      [ rewrite Q10, (a6l_ew_reg rX ex 24 (Z_to_bv 5 24) eq_refl); exact R24
      | rewrite Q11, (a6l_ew_reg rX ex 26 (Z_to_bv 5 26) eq_refl); exact R26
      | rewrite Q12, a6l_lit_long; reflexivity
      | rewrite Q13; reflexivity
      | rewrite Q20; destruct (b =? 91); [reflexivity | rewrite Z_to_bv_bv_unsigned; exact R20]
      | rewrite HK by (cbn [In]; repeat (first [left; reflexivity | right]));
        eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right])] ].
- (* span >= len: the span reaches the line's end, the byte there is '\n' or the NUL, s4 kept *)
  assert (Heq : sp = L) by lia.
  assert (Hnot : (nth sp (skipn o (p_s v)) 0 =? 91) = false).
  { rewrite Heq. unfold L, pf_line. destruct HNLc as [HN | HN].
    - rewrite HN. reflexivity.
    - rewrite HN, nth_overflow by lia. reflexivity. }
  rewrite Hnot.
  pose proof (a6l_seedA B v pos lyc Sc Wc rX memc mdc (Z.of_nat sp) (Z.of_nat L) HB R10 R23 ltac:(lia) ltac:(lia)
    ltac:(lia)) as HS.
  assert (HEI : img_env VAL A_LIM (a6l_E rX [])) by apply a6l_E_img.
  paj_run_to_shc (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ PF_REF3.
  { a6l_awr. }
  assert (Hmem : ms_mem ms = memc) by a6l_mem HF.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
  pmkst HS. rewrite Hmem in HJ |- *. clear HF HFr HG.
  pose proof (a6l_regs_kept rX [] _ (w_H Wc) ms [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] HS
    ltac:(vm_compute; reflexivity)) as HK.
  prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 12) Q12. prreg HS (Z_to_bv 5 13) Q13.
  lazymatch goal with |- SRr ?s ?w _ ?Q => change (SRr s w (cfg_at SEGS (BASE + PF_REF3) (ms_regs ms) memc mdq) Q) end.
  apply (HREF3 v pos lyc Sc Wc (ms_regs ms) memc mdq cf cur nm o ln d F_long (seg_litA_rc F_long) [AI 511] 511).
  split; [|split; [exact HMID|split; [exact HST|split]]].
  + apply (a6l_base_at v pos lyc Sc Wc rX (ms_regs ms) memc mdc mdq PF_SC_LINE HB HJ).
    apply (a6l_rg_keep rX (ms_regs ms) _ HFI). intros rv Hin. apply HK.
    unfold a5_FI in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; repeat (first [left; reflexivity | right]) |]). destruct Hin.
  + left. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  + unfold pf_rg, PF_RL, PF_RM. cbn [app].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    all: first
      [ rewrite Q10, (a6l_ew_reg rX [] 24 (Z_to_bv 5 24) eq_refl); exact R24
      | rewrite Q11, (a6l_ew_reg rX [] 26 (Z_to_bv 5 26) eq_refl); exact R26
      | rewrite Q12, a6l_lit_long; reflexivity
      | rewrite Q13; reflexivity
      | rewrite HK by (cbn [In]; repeat (first [left; reflexivity | right]));
        eapply a5_rg_get; [exact HRG | unfold PF_RL, PF_RM; cbn [app In]; repeat (first [left; reflexivity | right])] ].
Qed.

End e.
End f.
End d.
