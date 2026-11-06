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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 276 of its 321 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_10 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): J9 0x885c4 -> KREF 0x889a0, the
   arguments of the shared key refusal. A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_10 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_d.v (A9's K5 -> K9 dispatch, its knock / nokey half)
   and the image-B forms of lib/B/Prog/pf_seg_B9_s1.v (the B9 segment lane: a cut unpacked, a seed, a run, the next cut
   rebuilt by b9_move0) and the B5 piece pf_seg_B5_r2.v (the B5 segment lane: a seed, psrr_branch_pi, paj_run_to_sh),
   re-derived on image B's code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     J9    0x885c4 beqz a0,0x88988         a0 = strcasecmp(key, "knock") (INV_JC's iff with k = 3)
     knock 0x88988 auipc a0 ; 0x8898c addi a2,a0,-8     a2 = 0x21980 = seg_litA_rc F_knock (listing object 61)
           0x88990 ld a0,200(s1)           a0 = c       (pf_fi's slot 0xc8)
           0x88994 mv a1,s6                a1 = ln + 1  (PF_RM)
           0x88998 ld a3,64(s1)            a3 = F + 0x20 = cur_name (PF_SL's slot 0x40)
           0x8899c ld a4,112(s1)           a4 = vp      (INV_JC's slot 0x70)      falls into KREF 0x889a0
     nokey 0x885c8 auipc a0 ; 0x885cc addi a2,a0,1144   a2 = 0x21a40 = seg_litA_rc F_nokey (listing object 47)
           0x885d0 ld a0,200(s1) ; 0x885d4 mv a1,s6 ; 0x885d8 ld a3,64(s1)
           0x885dc mv a4,s7                a4 = kp (the key)                     0x885e0 j KREF 0x889a0
   14 instructions walked: 0x885c4 .. 0x885e0 (8) and 0x88988 .. 0x8899c (6). No call, no inline check, no UBSan
   trap. The step: the earlier three strcasecmp answers are not 0 (INV_JC's conjunct), so r_key gives the knock
   refusal [AS nm; AS val] when the key is "knock" (pf_seg_B9_f.v b9_rkey_knock) and the nokey refusal
   [AS nm; AS key] otherwise (b9_rkey_nokey): H_KREF (pf_pieces.v) with f = F_knock / F_nokey (pf_kref).
   The proof: a seed at J9 (every register its own atom; the slots 0x40, 0x70, 0xc8 of s1 a read-only region on
   atom 9 whose chunks are the extra atoms 33, 32, 34), the branch split by psrr_branch_pi (its condition is a0's
   value, which INV_JC ties to the knock compare), one run to KREF on each side (it writes nothing, so the memory is
   the cut's: kept_of_frame), pf_base by b9_move0, the registers read off the run.
   Section hypothesis: OBJ (the listing's object atoms, for the two literal addresses the code forms). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Lemma b9s10_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* a beq branch's condition as the values of its operands *)
Lemma b9s10_br_eq : forall E a b x z t, U E a = x -> U E b = z ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = t -> (x =? z) = t.
Proof. intros E a b x z t Ha Hb Hc. rewrite branch_eq_U, Ha, Hb in Hc. exact Hc. Qed.
Ltac b9s10_in := cbn [In app]; repeat first [left; reflexivity | right].
(* a register of the state after a run, as the executor wrote it (pf_seg_B5_r2.v b5r2_rreg) *)
Ltac b9s10_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b9s10_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* the seed at J9: every register its own atom; s1's slots 0x40 (cur_name), 0x70 (val), 0xc8 (c) a read-only region
   on atom 9, holding the extra atoms 33, 32, 34 *)
Definition b9s10_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x40 0xd0 0 0
     [YP09.mkChunk 0x40 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 32 0));
      YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0))]].
Definition b9s10_ss : sstate := mkSS B9_J9 sr_atoms b9s10_regions None (mkFacts [] [] []).
(* the registers the run from J9 to KREF does not write *)
Definition B9S10_KEPT : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 25; 26].

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
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* the two refusal literals the code forms: listing objects 61 (.str.24, 0x21980) and 47 (.str.25, 0x21a40) *)
Lemma b9s10_lit_knock : forall E, img_env VAL A_LIM E -> ew E 302%nat = w64 (seg_litA_rc F_knock).
Proof.
intros E HE. rewrite (img_env_atomP E 302%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 302%nat with (A_OBJ 61). rewrite (OBJ 61%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma b9s10_lit_nokey : forall E, img_env VAL A_LIM E -> ew E 288%nat = w64 (seg_litA_rc F_nokey).
Proof.
intros E HE. rewrite (img_env_atomP E 288%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 288%nat with (A_OBJ 47). rewrite (OBJ 47%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* pf_base at the same frame state after a run that wrote nothing (b9_move0 with Sc' = Sc) *)
Lemma b9s10_base_same : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (b9_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' HB HJ' KM KV HRG.
pose proof (b9_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (_ & _ & _ & G & _).
pose proof HB as (_ & _ & _ & _ & HFSH).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc memc' a = rdW Wc memc a)
  by (intros a Ha _; exact (KM a Ha)).
eapply (b9_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ');
  [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | exact HRG |].
eapply b9_keep_fsh; [exact G | exact KW | exact HFSH].
Qed.

(** ** Stretch SB9_10: from J9 the walk reaches B9's goal through KREF *)
Lemma b9_s10 : SB9_10 B.
Proof.
unfold SB9_10, from_JC, b9_from.
intros n HKREF x ei kp vp gi lyc Sc Wc rX memc mdc HI.
destruct x as [v pos cf cur nm o ln d lp].
unfold INV_JC, b9_core, b9_inbuf, B9_R in HI.
change (b9_line (mkB9X v pos cf cur nm o ln d lp)) with (pf_tline (p_s v) o) in HI.
change (b9_key (mkB9X v pos cf cur nm o ln d lp) ei) with (r_trim (firstn ei (pf_tline (p_s v) o))) in HI.
change (b9_val (mkB9X v pos cf cur nm o ln d lp) ei)
  with (r_unquote (r_trim (skipn (S ei) (pf_tline (p_s v) o)))) in HI.
change (b9_buf (mkB9X v pos cf cur nm o ln d lp)) with (pf_F v pos + PF_O_BUF) in HI.
change (b9_k (mkB9X v pos cf cur nm o ln d lp)) with (length (skipn o (p_s v))) in HI.
change (y_v (mkB9X v pos cf cur nm o ln d lp)) with v in HI.
change (y_pos (mkB9X v pos cf cur nm o ln d lp)) with pos in HI.
change (y_o (mkB9X v pos cf cur nm o ln d lp)) with o in HI.
change (y_ln (mkB9X v pos cf cur nm o ln d lp)) with ln in HI.
change (y_d (mkB9X v pos cf cur nm o ln d lp)) with d in HI.
change (y_cf (mkB9X v pos cf cur nm o ln d lp)) with cf in HI.
change (y_cur (mkB9X v pos cf cur nm o ln d lp)) with cur in HI.
change (y_nm (mkB9X v pos cf cur nm o ln d lp)) with nm in HI.
destruct HI as ((HB & HMID & HST & HLEN & HD0 & HDL) & Hcur & HCH & (HKS & HKI) & (HVS & HVI) & HS70 & HNE & HA0Q
  & HRG).
subst cur.
change (b9_goal B (mkB9X v pos cf (Some gi) nm o ln d lp))
  with (pf_postm B v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).
change (B9_JC 3) with B9_J9.
set (key := r_trim (firstn ei (pf_tline (p_s v) o))) in *.
set (val := r_unquote (r_trim (skipn (S ei) (pf_tline (p_s v) o)))) in *.
(* the earlier three compares are not 0 *)
pose proof (HNE 0%nat ltac:(lia)) as N1. pose proof (HNE 1%nat ltac:(lia)) as N2.
pose proof (HNE 2%nat ltac:(lia)) as N3. cbn [nth b9_lits] in N1, N2, N3.
cbn [nth b9_lits] in HA0Q.
(* the cut's facts *)
pose proof (b9_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & HC8 & HRG0).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
unfold pf_inb, PF_O_BUF in HKI, HVI.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
(* the three slot words *)
assert (S40 : rdword (rdW Wc memc) (pf_s1 v + 0x40) = Some (pf_F v pos + PF_O_CN)).
{ exact (proj1 (Forall_forall _ _) HSL (0x40, pf_F v pos + PF_O_CN) ltac:(unfold PF_SL; b9s10_in)). }
assert (SC8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)).
{ exact (proj1 (Forall_forall _ _) HC8 (0xc8, p_c v) ltac:(b9s10_in)). }
assert (S70 : rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some vp).
{ exact (proj1 (Forall_forall _ _) HS70 (0x70, vp) ltac:(b9s10_in)). }
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b9_rg_get rX _ 9 _ HRG0); b9s10_in).
(* the seed *)
set (E := Eimg (Ereg rX [w64 vp; w64 (pf_F v pos + PF_O_CN); w64 (p_c v)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat ->
  ew E (32 + j) = nth j [w64 vp; w64 (pf_F v pos + PF_O_CN); w64 (p_c v)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. clear EX.
assert (E9 : ew E 9 = w64 (pf_s1 v)) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E b9s10_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J9)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b9s10_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold b9s10_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    repeat constructor.
    + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x40 8 (SOff 33 0) (pf_F v pos + PF_O_CN));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold PF_O_CN; lia);
         reflexivity
        | unfold PF_O_CN; lia | lia | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S40)].
    + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x70 8 (SOff 32 0) vp);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S70)].
    + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0xc8 8 (SOff 34 0) (p_c v));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
        | lia | lia | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ SC8)].
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
(* a0's value: INV_JC ties it to the knock compare *)
assert (E10 : ew E 10 = Z_to_bv 64 (bv_unsigned (getr rX 10))).
{ rewrite (EE 10%nat 10%bv eq_refl). symmetry. apply Z_to_bv_bv_unsigned. }
pose proof (bv_unsigned_in_range 64 (getr rX 10)) as R10r. change (bv_modulus 64) with (2 ^ 64) in R10r.
unfold cfg_at. change (w64 (BASE + B9_J9)) with (Z_to_bv 64 (BASE + B9_J9)).
(* 0x885c4 beqz a0 *)
psrr_branch_pi RUNP BR HS.
- (* taken: the key is "knock"; 0x88988 .. 0x8899c, falls into KREF *)
  lazymatch type of Hc with branch_taken BC_EQ (sv_denot _ ?a) (sv_denot _ ?b) = _ =>
    pose proof (b9s10_br_eq E a b _ 0 true ltac:(apply (U_atom E 10 _ E10); lia) ltac:(apply U_lit; lia) Hc) as L0
  end.
  apply Z.eqb_eq in L0. clear Hc.
  assert (A0 : getr rX 10 = w64 0).
  { apply bv_eq. rewrite L0. reflexivity. }
  pose proof (proj1 HA0Q A0) as K4.
  rewrite (b9_rkey_knock cf gi nm (ln + 1) (pf_tline (p_s v) o) ei HCH N1 N2 N3 K4).
  paj_run_to_sh RUNTO HS HJ PF_KREF.
  { intros a (r & Hr & Ha). cbn [add_cond b9s10_ss b9s10_regions ss_mem In] in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b9s10_clear_md.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
        [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
  clear HFr HG HF.
  (* the registers at KREF *)
  assert (QK : forall r, In r B9S10_KEPT -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold B9S10_KEPT in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s10_rreg HS; rewrite b9s10_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c v)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact E34. }
  assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (ln + 1)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl).
    apply (b9_rg_get rX _ 22 _ HRG); b9s10_in. }
  assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_knock)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact (b9s10_lit_knock E HEI). }
  assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (pf_F v pos + PF_O_CN)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact E33. }
  assert (Q14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 vp).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact E32. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_KREF) rg mm mdx) end.
  apply (HKREF v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf (Some gi) nm o ln d F_knock
    (seg_litA_rc F_knock) [AS nm; AS val] vp).
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a Ha _; exact (K1 a Ha)).
  split; [|split; [exact HMID | split; [|split]]].
  + apply (b9s10_base_same v pos lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HB HJ K1 KV).
    unfold pf_rg, b9_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG0); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
  + eapply (b9_keep_st B v pos lyc Sc Wc memc mdc (rdW Wc (ms_mem ms)));
      first [exact G | exact HAR | exact Hin | exact Hly | exact KW | exact KV | exact HC5 | exact HST].
  + split; [left; reflexivity|]. split; [reflexivity|].
    exists val. split; [reflexivity|]. split; [|unfold pf_inb, PF_O_BUF; lia].
    apply (reac_segconf_parse.sa_str_low _ _ _ _ HVS); [lia | lia |].
    intros a Ha. apply K1. lia.
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        first [exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14].
- (* not taken: the key is no key B9 knows; 0x885c8 .. 0x885e0, `j` KREF *)
  lazymatch type of Hc with branch_taken BC_EQ (sv_denot _ ?a) (sv_denot _ ?b) = _ =>
    pose proof (b9s10_br_eq E a b _ 0 false ltac:(apply (U_atom E 10 _ E10); lia) ltac:(apply U_lit; lia) Hc) as L0
  end.
  apply Z.eqb_neq in L0. clear Hc.
  assert (K4 : strcasecmp key S_knock <> 0).
  { intros K4. apply L0. pose proof (proj2 HA0Q K4) as A0. rewrite A0. reflexivity. }
  rewrite (b9_rkey_nokey cf gi nm (ln + 1) (pf_tline (p_s v) o) ei HCH N1 N2 N3 K4).
  paj_run_to_sh RUNTO HS HJ PF_KREF.
  { intros a (r & Hr & Ha). cbn [add_cond b9s10_ss b9s10_regions ss_mem In] in Hr.
    destruct Hr as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b9s10_clear_md.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
        [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
    by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
  clear HFr HG HF.
  assert (QK : forall r, In r B9S10_KEPT -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. unfold B9S10_KEPT in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b9s10_rreg HS; rewrite b9s10_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c v)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact E34. }
  assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (ln + 1)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl).
    apply (b9_rg_get rX _ 22 _ HRG); b9s10_in. }
  assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_nokey)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact (b9s10_lit_nokey E HEI). }
  assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (pf_F v pos + PF_O_CN)).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. exact E33. }
  assert (Q14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 kp).
  { b9s10_rreg HS. rewrite b9s10_den_atom0. rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl).
    apply (b9_rg_get rX _ 23 _ HRG); b9s10_in. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_KREF) rg mm mdx) end.
  apply (HKREF v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf (Some gi) nm o ln d F_nokey
    (seg_litA_rc F_nokey) [AS nm; AS key] kp).
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
    by (intros a Ha _; exact (K1 a Ha)).
  split; [|split; [exact HMID | split; [|split]]].
  + apply (b9s10_base_same v pos lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv HB HJ K1 KV).
    unfold pf_rg, b9_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG0); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
  + eapply (b9_keep_st B v pos lyc Sc Wc memc mdc (rdW Wc (ms_mem ms)));
      first [exact G | exact HAR | exact Hin | exact Hly | exact KW | exact KV | exact HC5 | exact HST].
  + split; [right; left; reflexivity|]. split; [reflexivity|].
    exists key. split; [reflexivity|]. split; [|unfold pf_inb, PF_O_BUF; lia].
    apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS); [lia | lia |].
    intros a Ha. apply K1. lia.
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s10_in | unfold B9S10_KEPT; b9s10_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        first [exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14].
Qed.

End e.
End f.
End d.
