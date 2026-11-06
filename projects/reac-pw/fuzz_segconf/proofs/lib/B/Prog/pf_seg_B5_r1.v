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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 179 of its 221 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece R1 -> Q3 / R2 (a B5 sub-lane of the image-B G3 walk owner, 2026-10-30): b5_r1_ok : H_Q3 B n -> H_R2 B n -> H_R1 B n.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk: segment B5's R1 piece; the
   function's rule-24 record is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A piece lib/A/Prog/pf_a5_h.v (commit 6a900018c704, a5_r1_ok)
   and the unit owner's UBSan piece lib/U/Prog/pf_p2.v (the same C-level pointer check of `nl`), re-derived on image B's
   code over B's kit lib/B/Prog/pf_seg_B5_k.v and the helpers of lib/B/Prog/pf_seg_B5_hd.v:
     R1 0x88204 `beqz a0,0x8821c`   a0 = strchr's answer b5_nl v o (INV_R1)
        a0 <> 0 (a '\n' ends the line, nl = t + o + LEN, o + LEN < length s):
          0x88208 `bne a0,s10,0x88210`   UBSan trap T03 (s10 = -1: the pointer `nl + 1` overflows, reac_segconf.c:135);
                                         its not-taken side 0x8820c `j 0x891c8` (the `unimp`) is refuted: nl <= t +
                                         length s < 2 ^ 47 (pf_obj's text block below alloc_ceiling), so nl <> 2 ^ 64 - 1
          0x88210 `sub s7,a0,s11`        s7 = nl - p = LEN
          0x88214 `addi s9,a0,1`         s9 = nl + 1 = t + pf_next s o (pfA_facts.L_next_holds)
          0x88218 `j 0x88238`            Q3
        a0 = 0 (no '\n': the line ends the text, o + LEN = length s):
          0x8821c `mv a0,s11`; 0x88220 `jal` the strlen trampoline (the listing's pa_sigma
          SS___interceptor_trampoline_strlen, image B 0x43a98; call C6, RtString.astrlen_realizes, window ESTACK at
          s1); return 0x88224 = R2 with a0 = strlen(p) = length s - o = LEN.
   Each path: the seed at R1 (every register its own atom, no region; pf_seg_B5_hd.v b5hd_seed), the branch by
   psrr_branch_tok, token runs (SegPaLib.v paj_run_tok / paj_run_to_tok), the call through PaArt.v aj_art_at with
   the string premises of b5hd_str_pre, and the next point's INV rebuilt by b5hd_step (the kit's b5_move and
   b5_keep_st). 7 of B5's 116 instructions walked (0x88204 .. 0x88220 except the trap jump 0x8820c), trap T03
   discharged, no check, one call (C6).
   Section hypotheses: TL (PALib: the errno cell's place, which aj_art_at needs), ASTRLEN (RtString.astrlen_realizes
   at the listing's strlen trampoline). No SSPX, no VRO. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun PaSB PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B5_d pf_seg_B5_k pf_seg_B5_hd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the trap T03 (0x88208 `bne a0,s10`, s10 = -1): its not-taken side needs a0 = 2 ^ 64 - 1 *)
Lemma b5r1_t03 : forall x, 0 <= x < 2 ^ 64 - 1 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false -> False.
Proof.
intros x Hx H.
assert (Em : Z_to_bv 64 (-1) = Z_to_bv 64 (2 ^ 64 - 1)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
rewrite Em, b5hd_br_ne in H by lia.
apply Bool.negb_false_iff, Z.eqb_eq in H. lia.
Qed.

Ltac b5r1_in := unfold b5_FI, PF_RL; cbn [In app]; repeat first [left; reflexivity | right].

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
(* the listing's runtime record (SegPaLib.v PALib): aj_art_at needs its errno cell, pal_env *)
Hypothesis TL : PALib B.
(* the image-A wrapper-layer owner's row 16 at the listing's strlen trampoline (image B 0x43a98) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Ltac b5r1_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  apply awr_ok_nil.
(* a register the run left as its own atom, read from the seed's list R *)
Ltac b5r1_atom HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let H := fresh "Hr" in prreg HS (Z_to_bv 5 k) H; rewrite H; clear H;
    transitivity (getr rX (Z_to_bv 5 k)); [apply EE; reflexivity | apply (b5_rg rX _ k _ R); b5r1_in] end.
(* the same after a call that preserves the callee-saved registers *)
Ltac b5r1_cs HP HS EE rX R :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (HP k ltac:(unfold acallee_saved; lia)); b5r1_atom HS EE rX R end.
(* a register's term after the run *)
Ltac b5r1_get HS :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let H := fresh "Hv" in prreg HS (Z_to_bv 5 k) H; rewrite H; clear H end.

(* ======================= R1 0x88204 -> Q3 0x88238 or R2 0x88224 (strlen, C6) ======================= *)
Lemma b5_r1_ok : forall n, H_Q3 B n -> H_R2 B n -> H_R1 B n.
Proof.
intros n HQ3 HR2 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
destruct HI as (HB & HLN & HRG).
pose proof HLN as (_ & Ho & _ & _).
pose proof HB as (HCX & HFI & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HFR).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (b5hd_tpos B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD HB) as (Ht0 & Ht47).
assert (Hnlr : 0 <= b5_nl v o < 2 ^ 64 - 1).
{ unfold b5_nl. destruct (o + b5_len v o <? length (p_s v))%nat eqn:E; cbv iota; [apply Nat.ltb_lt in E|]; lia. }
assert (RA : pf_rg rX (b5_FI B v ++ PF_RL v pos ++
    [(27, p_t v + Z.of_nat o); (24, ln); (10, b5_nl v o)])) by (apply b5_rg_app; split; assumption).
assert (Hal16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (b5_m16 _ _ G6 G3).
pose proof (b5hd_seed B5_R1 rX Wc memc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (E2 : ew E 2 = Z_to_bv 64 (pf_s1 v))
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl); apply (b5_rg rX _ 2 _ RA); b5r1_in).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B))
  by (rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); apply (b5_rg rX _ 3 _ RA); b5r1_in).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B))
  by (rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); apply (b5_rg rX _ 4 _ RA); b5r1_in).
assert (E10 : ew E 10 = Z_to_bv 64 (b5_nl v o))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); apply (b5_rg rX _ 10 _ RA); b5r1_in).
assert (E26 : ew E 26 = Z_to_bv 64 (-1))
  by (rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl); apply (b5_rg rX _ 26 _ RA); b5r1_in).
assert (E27 : ew E 27 = Z_to_bv 64 (p_t v + Z.of_nat o))
  by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply (b5_rg rX _ 27 _ RA); b5r1_in).
assert (SHOK : sh_ok SEGS b5hd_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at, w64.
(* 0x88204 beqz a0 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 = 0: the line ends the text; 0x8821c mv a0,s11; 0x88220 jal the strlen trampoline *)
  prreg_norm Hc. rewrite E10 in Hc. rewrite b5hd_br_eq in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hnl0.
  assert (Hend : (o + b5_len v o = length (p_s v))%nat) by (apply (b5hd_nl0 v o Hnl0); lia).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { b5r1_awr. }
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10.
  rewrite E2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E27 in Q10.
  assert (R1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B5_R2)) by (rewrite R1; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
    by (rewrite R1'; apply ret_ok_codeptr_v; [unfold B5_R2, AF_reac_segconf_parse_file; lia | reflexivity]).
  assert (Hsp1 : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
    by (unfold spZ; rewrite Q2; rewrite unsigned_lit_small by lia; lia).
  assert (RFI1 : pf_rg (ms_regs ms) (b5_FI B v)).
  { unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; b5r1_atom HS EE rX RA. }
  destruct (b5hd_step B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdB 0 HB HJ
    ltac:(rewrite HES; lia) ltac:(intros a Ha _; exact (KM1 a Ha)) RFI1) as (HB1 & HLN1).
  destruct (b5hd_str_pre B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB PF_SC_HEAD o ESTACK HB1 Ho
    ltac:(rewrite HES; lia)) as (Hx0 & HSTR1 & HRD1 & HMR1 & HTV1 & HROM1 & HLS & HZS).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False)
      (SIG SS___interceptor_trampoline_strlen) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdB 0
      (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B5_R2)) _ HJ Hsp1 Hal16 ltac:(lia) ltac:(rewrite HES; lia)
      ltac:(rewrite SPF, HES; lia) R1' (fun a (H : False) => False_ind _ H)).
    apply (ASTRLEN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB (p_t v + Z.of_nat o) (skipn o (seg_spec.zb (p_s v)))).
    - exact (ecall_pre_stk_at SEGS B ESTACK STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
        (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem ms) mdB 0 (ms_regs ms)
        (pf_s1 v - pf_sp0 v) HJ Hsp1 Hal16 ltac:(lia) ltac:(lia) ltac:(rewrite SPF, HES; lia) HraT Q3 Q4).
    - rewrite Q10. reflexivity.
    - exact Hx0.
    - exact HSTR1.
    - exact HRD1.
    - exact HTV1.
    - exact HROM1. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B5_R2)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + B5_R2) regs2 mem2 md2).
  destruct (b5hd_step B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdB PF_SC_HEAD regs2 mem2 md2 ESTACK HB1 HJ2
    ltac:(rewrite HES; lia) ltac:(intros a Ha Hn'; apply HK2; [exact Ha | lia | cbv beta; tauto])
    (b5_rg_pres _ _ _ HP2 (b5_FI_cs B v) RFI1)) as (HB2 & HLN2).
  apply (HR2 v pos lyc Sc Wc regs2 mem2 md2 cf cur nm o ln d).
  split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ (HLN1 _ _ _ _ _ _ _ HLN))|]. split; [exact Hend|].
  apply b5_rg_app. split.
  + unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; b5r1_cs HP2 HS EE rX RA.
  + repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    1-2: b5r1_cs HP2 HS EE rX RA.
    (* a0 = strlen(p) = LEN *)
    rewrite HLS in Ha02.
    replace (Z.of_nat (b5_len v o)) with (Z.of_nat (length (p_s v)) - Z.of_nat o) by lia.
    eapply b5hd_bvr2; [exact Ha02 | reflexivity].
- (* a0 <> 0: a '\n' ends the line *)
  prreg_norm Hc. rewrite E10 in Hc. rewrite b5hd_br_eq in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (b5hd_nl1 v o Hc) as (Hlt & Hnlv). clear Hc.
  (* 0x88204 beqz (not taken), up to 0x88208 bne a0,s10 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { b5r1_awr. }
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
      [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  clear HFr HG HF.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msA end.
  set (mdA := with_vm_backing _ _ _) in *; clearbody mdA.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a0 <> -1: 0x88210 sub s7,a0,s11; 0x88214 addi s9,a0,1; 0x88218 j Q3 *)
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B5_Q3.
    { b5r1_awr. }
    assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc (ms_mem msA) a).
    { intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ (w_H Wc) (ms_mem msA) (ms_mem ms) (fun _ => False) HFr);
        [|exact Ha | tauto].
      intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
    clear HFr HG HF.
    set (mdB := with_vm_backing _ _ _) in *; clearbody mdB.
    pmkst HS.
    assert (RFI : pf_rg (ms_regs ms) (b5_FI B v)).
    { unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; b5r1_atom HS EE rX RA. }
    destruct (b5hd_step B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms) (ms_mem ms) mdB 0 HB HJ
      ltac:(rewrite HES; lia) ltac:(intros a Ha _; rewrite (KM2 a Ha); exact (KM1 a Ha)) RFI) as (HB2 & HLN2).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
      apply (HQ3 v pos lyc Sc Wc rg mm mdn cf cur nm o ln d) end.
    split; [exact HB2|]. split; [exact (HLN2 _ _ _ _ _ _ _ HLN)|].
    apply b5_rg_app. split.
    * unfold pf_rg, PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; b5r1_atom HS EE rX RA.
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      1-2: b5r1_atom HS EE rX RA.
      -- (* s9 = nl + 1 = t + pf_next s o *)
         b5r1_get HS. rewrite E10, Hnlv. rewrite unsigned_lit_small by lia.
         rewrite (b5hd_next v o Ho).
         replace ((o + b5_len v o <? length (p_s v))%nat) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
         unfold w64. f_equal. lia.
      -- (* s7 = nl - p = LEN *)
         b5r1_get HS. rewrite E10, E27, Hnlv. rewrite b5hd_subm by lia.
         unfold w64. f_equal. lia.
  + (* a0 = -1: the trap T03, refuted (nl < 2 ^ 47) *)
    exfalso. prreg_norm Hc. rewrite E10, E26 in Hc. exact (b5r1_t03 _ Hnlr Hc).
Qed.
End e.
End f.
End d.
