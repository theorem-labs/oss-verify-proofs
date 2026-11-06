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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 883 of its 935 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1.v, with its module paths, module names and numbers changed; 172 of its 229 lines of code are new or changed and 878 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_1 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): KEY 0x883f8 -> J1 0x88404, the call
   strchr(line, '='). The B9 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_1 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_d.v (A9's stretch SA9_A, its strchr half) and the image-B
   art-call form of lib/B/Prog/trim_s.v, re-derived on image B's code:
     0x883f8 li a1,61; 0x883fc mv a0,s7 (s7 = lp, the trimmed line in buf); 0x88400 jal strchr (trampoline
     SS___interceptor_trampoline_strchr); return 0x88404 = B9_J1.
   The proof: a seed at KEY (every register its own atom, no region), one token run to the call, the call by aj_art_at
   with RtSeg.astrchr_realizes (window 2 * ESTACK at s1; premises from pf_seg_B9_c.v b9_strchr_pre_88400), and J1's
   predicate at the return state: pf_base by b9_move0 (the run writes nothing, the entry writes only its window below
   s1), the line kept (buf lies in the side-stack frame below alloc_ceiling), and strchr's answer as SegModel.strchr
   (pf_seg_B9_f.v b9_strchr_none / b9_strchr_of_first). Instructions 0x883f8 .. 0x88400 (3). No check, no trap.
   Section hypotheses: ASTRCHR (the strchr carrier at the listing's trampoline), TL (PALib: the errno cell's place,
   which the art step needs). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Lemma b9s1_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b9s1_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b9s1_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
(* a reader at a reads the byte at a mod 2 ^ 64 (mbyte goes through Z_to_bv 64) *)
Lemma b9s1_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
Ltac b9s1_in := cbn [In app]; repeat first [left; reflexivity | right].

(* the seed at KEY: every register its own atom, no region, no fact *)
Definition b9s1_ss : sstate := mkSS PF_KEY sr_atoms [] None (mkFacts [] [] []).
(* the registers the run from KEY to the call does not write (callee-saved ones and gp / tp / sp) *)
Definition b9s1_kept : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis TL : PALib B.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run (fx := fx) B LAWS.

Lemma b9_s1 : SB9_1 B.
Proof.
unfold SB9_1, H_KEY. intros n FJ1 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HKEY.
destruct (b9_of_KEY B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HKEY) as (HC & HL & HRG).
change (pf_postm B v (r_key cf cur nm (ln + 1) (pf_tline (p_s v) o)) o ln)
  with (b9_goal B (mkB9X v pos cf cur nm o ln d lp)).
unfold b9_core in HC. unfold b9_inbuf in HL. unfold B9_R in HRG.
change (b9_line (mkB9X v pos cf cur nm o ln d lp)) with (pf_tline (p_s v) o) in HC, HL.
change (b9_buf (mkB9X v pos cf cur nm o ln d lp)) with (pf_F v pos + PF_O_BUF) in HL.
change (b9_k (mkB9X v pos cf cur nm o ln d lp)) with (length (skipn o (p_s v))) in HC.
change (y_v (mkB9X v pos cf cur nm o ln d lp)) with v in HC, HRG.
change (y_pos (mkB9X v pos cf cur nm o ln d lp)) with pos in HC, HRG.
change (y_o (mkB9X v pos cf cur nm o ln d lp)) with o in HC, HRG.
change (y_ln (mkB9X v pos cf cur nm o ln d lp)) with ln in HC, HRG.
change (y_d (mkB9X v pos cf cur nm o ln d lp)) with d in HC.
change (y_cf (mkB9X v pos cf cur nm o ln d lp)) with cf in HC.
change (y_cur (mkB9X v pos cf cur nm o ln d lp)) with cur in HC.
change (y_nm (mkB9X v pos cf cur nm o ln d lp)) with nm in HC.
destruct HC as (HB & HMID & HST & HLEN & HD0 & HDL).
destruct HL as [HLS HLI].
pose proof (b9_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _ & _ & HRG0).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
unfold pf_inb in HLI. unfold PF_O_BUF in HLI.
assert (HLp0 : 0 <= lp) by lia.
assert (HLp1 : lp + Z.of_nat (length (pf_tline (p_s v) o)) < alloc_ceiling) by lia.
(* the seed *)
set (E := Eimg (Ereg rX [])).
assert (HS : st_ok_pi SEGS VAL E b9s1_ss (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KEY)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b9s1_ss. apply pa_entry_st_ok_full;
    [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
    | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_KEY)) with (Z_to_bv 64 (BASE + PF_KEY)).
(* 0x883f8 li a1,61; 0x883fc mv a0,s7; 0x88400 jal strchr *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the registers at the call *)
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b9s1_kept) HS HA0 ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
assert (Rz : forall k z, In k b9s1_kept -> getr rX (Z_to_bv 5 k) = w64 z -> getr (ms_regs ms) (Z_to_bv 5 k) = w64 z).
{ intros k z Hk Hz. rewrite (HK (Z_to_bv 5 k)); [exact Hz | apply in_map; exact Hk]. }
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
pmkst HS.
unfold PF_RL, PF_RM in HRG.
assert (R2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ apply (b9s1_bvr _ 2%bv 2); [reflexivity|]. apply Rz; [b9s1_in|]. exact (b9_rg_get rX _ 2 _ HRG0 ltac:(b9s1_in)). }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ apply (b9s1_bvr _ 3%bv 3); [reflexivity|]. apply Rz; [b9s1_in|]. exact (b9_rg_get rX _ 3 _ HRG0 ltac:(b9s1_in)). }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ apply (b9s1_bvr _ 4%bv 4); [reflexivity|]. apply Rz; [b9s1_in|]. exact (b9_rg_get rX _ 4 _ HRG0 ltac:(b9s1_in)). }
assert (R23 : getr rX 23 = w64 lp).
{ apply (b9s1_bvr _ 23%bv 23); [reflexivity|]. apply (b9_rg_get rX _ 23 _ HRG); b9s1_in. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by (apply b9s1_m16; [exact G5 | exact G3]).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R10' : getr (ms_regs ms) 10 = w64 lp) by (rewrite R10, (EE 23%nat 23%bv eq_refl); exact R23).
pose proof (b9_keep_art B v pos lyc Sc Wc memc mdc (ms_mem ms) mdv 0 0 HST0 HJ ltac:(rewrite SPF; lia)
  (fun a Ha _ _ => KM1 a Ha)) as HST1.
assert (HLS1 : sa_str (rdW Wc (ms_mem ms)) lp (pf_tline (p_s v) o)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS HLp0 HLp1). intros a Ha. apply KM1. lia. }
destruct (b9_strchr_pre_88400 B v pos lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) lp (pf_tline (p_s v) o) HST1
  ltac:(rewrite Hsp; lia) HraT R3 R4 R10' ltac:(rewrite R11; reflexivity) HLS1
  ltac:(unfold pf_inb, PF_O_BUF; lia))
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strchr) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B9_J1)) _ HJ Hsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(rewrite SPF; unfold ESTACK; lia) ltac:(rewrite R1; reflexivity) (fun a (H : False) => False_ind _ H)).
  exact (ASTRCHR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv lp 61 (seg_spec.zb (pf_tline (p_s v) o)) P1 P2 P3 P4 P5
    P6 P7 P8 P9 P10). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B9_J1)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B9_J1) regs2 mem2 md2).
apply (FJ1 (mkB9X v pos cf cur nm o ln d lp) (strchr (pf_tline (p_s v) o) EQ) lyc Sc Wc regs2 mem2 md2).
(* the memory after the call: the cut's off strchr's window [s1 - 2 * ESTACK, s1) *)
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite HK2; [exact (KM1 a Ha) | exact Ha | lia | tauto]. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw. apply KM2; [exact Ha|]. intros Hn. apply Hw. left. rewrite SPF in G1 |- *. unfold ESTACK in Hn. lia. }
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
{ intros a0 Hv0. rewrite b9s1_aview_mod in Hv0 |- *.
  pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
  remember (a0 mod 2 ^ 64) as a eqn:Ea. clear Ea. rename Hv0 into Hv.
  destruct (Z_lt_le_dec a (pf_s1 v - 2 * ESTACK)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
  - rewrite KM2; [exact Hv | exact Ha | lia].
  - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF in *. unfold ESTACK in Hlo. lia.
  - rewrite KM2; [exact Hv | exact Ha | lia]. }
assert (Hpre : forall k z, In k b9s1_kept -> getr rX (Z_to_bv 5 k) = w64 z -> getr regs2 (Z_to_bv 5 k) = w64 z).
{ intros k z Hk Hz. rewrite (HP2 k); [exact (Rz k z Hk Hz)|].
  unfold b9s1_kept in Hk. cbn [In] in Hk. unfold acallee_saved.
  repeat (destruct Hk as [<- | Hk]; [lia |]). destruct Hk. }
assert (HFI2 : pf_rg regs2 (b9_FI B v)).
{ unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (apply Hpre; [b9s1_in | apply (b9_rg_get rX _ _ _ HRG0); b9s1_in]). }
assert (HB2 : pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE).
{ eapply (b9_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2);
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | exact HFI2 |].
  eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
unfold INV_J1, b9_core, b9_inbuf, B9_R.
change (b9_line (mkB9X v pos cf cur nm o ln d lp)) with (pf_tline (p_s v) o).
change (b9_buf (mkB9X v pos cf cur nm o ln d lp)) with (pf_F v pos + PF_O_BUF).
change (b9_k (mkB9X v pos cf cur nm o ln d lp)) with (length (skipn o (p_s v))).
change (y_v (mkB9X v pos cf cur nm o ln d lp)) with v.
change (y_pos (mkB9X v pos cf cur nm o ln d lp)) with pos.
change (y_o (mkB9X v pos cf cur nm o ln d lp)) with o.
change (y_ln (mkB9X v pos cf cur nm o ln d lp)) with ln.
change (y_d (mkB9X v pos cf cur nm o ln d lp)) with d.
change (y_cf (mkB9X v pos cf cur nm o ln d lp)) with cf.
change (y_cur (mkB9X v pos cf cur nm o ln d lp)) with cur.
change (y_nm (mkB9X v pos cf cur nm o ln d lp)) with nm.
change (y_lp (mkB9X v pos cf cur nm o ln d lp)) with lp.
split; [|split; [|split]].
- (* b9_core *)
  split; [exact HB2|]. split; [exact HMID|].
  split; [eapply b9_keep_st; eassumption|].
  split; [exact HLEN|]. split; [exact HD0 | exact HDL].
- (* the line, kept *)
  split; [|unfold pf_inb, PF_O_BUF; lia].
  apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS HLp0 HLp1).
  intros a Ha. apply KM2; [lia|]. rewrite SPF in G1. unfold ESTACK. lia.
- reflexivity.
- (* the registers: B9_R and s7 kept, a0 = strchr's answer *)
  destruct (b9_astr_of_sa Wc (ms_mem ms) lp (pf_tline (p_s v) o) HLS1) as (_ & _ & _ & HZS & _).
  destruct HLS as ((_ & HNZ) & _).
  assert (HA : getr regs2 (Z_to_bv 5 10) =
    w64 (match strchr (pf_tline (p_s v) o) EQ with None => 0 | Some ei => lp + Z.of_nat ei end)).
  { apply (b9s1_bvr' _ 10%bv 10); [reflexivity|].
    change (map (fun b : byte => bv_unsigned b) (seg_spec.zb (pf_tline (p_s v) o)))
      with (seg_spec.zs (seg_spec.zb (pf_tline (p_s v) o))) in HQ.
    rewrite HZS in HQ. destruct HQ as [(Q0 & Qn) | (j & Qj & Q0)].
    - rewrite (b9_strchr_none (pf_tline (p_s v) o) 61 ltac:(lia) Qn). exact Q0.
    - rewrite (b9_strchr_of_first (pf_tline (p_s v) o) 61 j ltac:(lia) HNZ Qj). exact Q0. }
  unfold PF_RL, PF_RM, pf_rg. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [ exact HA | apply Hpre; [b9s1_in | apply (b9_rg_get rX _ _ _ HRG); b9s1_in] ].
Qed.
End x.
End d.
