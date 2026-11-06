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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1.v, with its module paths and module names changed; 189 of its 245 lines of code are new or changed and 879 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_4 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): J3 0x88438 -> J4 0x88440, the call
   strlen(v0). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_4 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_s2.v (image A's stretch SA9_B, its strlen half) and
   from the proved image-B stretch lib/B/Prog/pf_seg_B9_s1.v (the same art-call form: seed, run, aj_art_at, the
   next cut), over image B's kit (pf_seg_B9_k.v, pf_seg_B9_c.v).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; reac_segconf.c:223):
     0x88438 mv   s3,a0    s3 = vp0 (trim #2's answer, the trimmed value in buf; a0 keeps it)
     0x8843c jal  43a98    the strlen trampoline (SS___interceptor_trampoline_strlen), a0 = vp0;
                           return 0x88440 = B9_J4
   2 instructions walked (0x88438 .. 0x8843c). No inline check, no UBSan trap.

   THE PROOF: a seed at J3 (every register its own atom, no region), one plain run to the call, the call by
   aj_art_at with RtString.astrlen_realizes (window ESTACK at s1; the premises from pf_seg_B9_c.v
   b9_strlen_pre_8843c), and J4's predicate at the return: pf_base by b9_move0 (the entry writes only its window
   below s1, which lies above alloc_ceiling, so every byte of the frame and of the heap is kept), pf_st by
   b9_keep_st, the key and the value kept (they lie in buf, inside the class-5 frame below alloc_ceiling), and
   a0 = |v0| from the contract's answer (astr_len (zb l) = |l|).
   Section hypotheses: ASTRLEN (the strlen carrier at the listing's trampoline), TL (PALib: the errno cell's
   place, which the art step needs). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
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

(* ---------- small tools (pf_seg_B9_s1.v's) ---------- *)
Lemma b9s4_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b9s4_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b9s4_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b9s4_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma b9s4_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
Lemma b9s4_J4 : B9_J4 = 0x3680.
Proof. vm_compute. reflexivity. Qed.
Ltac b9s4_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b9s4_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?b9s4_w64_off, ?alu64_add_lit, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [reflexivity | f_equal; lia].

(* the seed at J3: every register its own atom, no region, no fact *)
Definition b9s4_ss : sstate := mkSS B9_J3 sr_atoms [] None (mkFacts [] [] []).
(* the registers the run J3 -> the strlen call does not write (it writes ra and s3) *)
Definition b9s4_kept : list Z := [2; 3; 4; 8; 9; 10; 18; 20; 21; 22; 23; 24; 25; 26; 27].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TL : PALib B.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

Lemma b9_s4 : SB9_4 B.
Proof.
unfold SB9_4, from_J3, b9_from. intros n FJ4 x ei kp vp0 lyc Sc Wc rX memc mdc HI.
unfold INV_J3 in HI. destruct HI as (HC & HSC & HKEY & HKLT & HVAL & HRG).
unfold b9_core in HC. destruct HC as (HB & HMID & HST & HLEN & HD0 & HDL).
unfold b9_inbuf, b9_buf in HKEY, HVAL.
destruct HKEY as [HKS HKI]. destruct HVAL as [HVS HVI].
unfold pf_inb, PF_O_BUF in HKI, HVI. destruct HKI as [HKI1 HKI2]. destruct HVI as [HVI1 HVI2].
pose proof (b9_geo B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_st_of_base B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _ & _ & HRG0).
pose proof STK_values as (STR & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_lt as HCL.
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE)
  by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
(* the registers of the cut *)
unfold B9_R, PF_RL, PF_RM in HRG.
assert (R10 : getr rX 10%bv = w64 vp0).
{ apply (b9s4_bvr _ 10%bv 10); [reflexivity|]. apply (b9_rg_get rX _ 10 _ HRG); b9s4_in. }
(* the seed at J3 *)
set (E := Eimg (Ereg rX [])).
assert (HS : st_ok_pi SEGS VAL E b9s4_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_J3)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b9s4_ss. apply pa_entry_st_ok_full;
    [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
    | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 vp0) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
unfold cfg_at. change (w64 (BASE + B9_J3)) with (Z_to_bv 64 (BASE + B9_J3)).
(* 0x88438 mv s3,a0; 0x8843c jal the strlen trampoline *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdv := dM) in *; clearbody mdv end.
pmkst HS.
(* the registers at the call *)
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b9s4_kept) HS HA0
  ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (Rz : forall k z, In k b9s4_kept -> getr rX (Z_to_bv 5 k) = w64 z ->
  getr (ms_regs ms) (Z_to_bv 5 k) = w64 z).
{ intros k z Hk Hz. rewrite (HK (Z_to_bv 5 k)); [exact Hz | apply in_map; exact Hk]. }
prreg HS (1%bv : bv 5) P1. prreg HS (19%bv : bv 5) P19.
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 (y_v x))).
{ apply (b9s4_bvr _ 2%bv 2); [reflexivity|]. apply Rz; [b9s4_in|].
  exact (b9_rg_get rX _ 2 _ HRG0 ltac:(b9s4_in)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ apply (b9s4_bvr _ 3%bv 3); [reflexivity|]. apply Rz; [b9s4_in|].
  exact (b9_rg_get rX _ 3 _ HRG0 ltac:(b9s4_in)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ apply (b9s4_bvr _ 4%bv 4); [reflexivity|]. apply Rz; [b9s4_in|].
  exact (b9_rg_get rX _ 4 _ HRG0 ltac:(b9s4_in)). }
assert (C10 : getr (ms_regs ms) 10 = w64 vp0).
{ apply (b9s4_bvr _ 10%bv 10); [reflexivity|]. apply Rz; [b9s4_in|].
  apply (b9s4_bvr' _ 10%bv 10); [reflexivity | exact R10]. }
assert (D19 : getr (ms_regs ms) 19 = w64 vp0) by (rewrite P19; b9s4_den).
assert (Hsp1 : spZ (ms_regs ms) = pf_s1 (y_v x)).
{ unfold spZ. rewrite C2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 (y_v x) + (pf_s1 (y_v x) - pf_sp0 (y_v x))) by (rewrite Hsp1; lia).
assert (Ho16 : (pf_s1 (y_v x) - pf_sp0 (y_v x)) mod 16 = 0) by (apply b9s4_m16; [exact G5 | exact G3]).
assert (C1r : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + B9_J4)) by (rewrite P1; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the state at the call: the run wrote nothing *)
pose proof (b9_keep_art B (y_v x) (y_pos x) lyc Sc Wc memc mdc (ms_mem ms) mdv 0 0 HST0 HJ
  ltac:(rewrite SPF; lia) (fun a Ha _ _ => KM1 a Ha)) as HST1.
assert (HQ0 : 0 <= kp) by lia.
assert (HQ1 : kp + Z.of_nat (length (b9_key x ei)) < alloc_ceiling) by lia.
assert (HV0 : 0 <= vp0) by lia.
assert (HV1 : vp0 + Z.of_nat (length (b9_v0 x ei)) < alloc_ceiling) by lia.
assert (HVS1 : sa_str (rdW Wc (ms_mem ms)) vp0 (b9_v0 x ei)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HVS HV0 HV1). intros a Ha. apply KM1. lia. }
(* the strlen call's premises (pf_seg_B9_c.v b9_strlen_pre_8843c) *)
destruct (b9_strlen_pre_8843c B (y_v x) (y_pos x) lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) vp0 (b9_v0 x ei)
  HST1 Hsp1 HraT C3 C4 C10 HVS1 ltac:(unfold pf_inb, PF_O_BUF; lia))
  as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False)
    (SIG SS___interceptor_trampoline_strlen) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file
    (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x))
    (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc mdv 0
    (pf_s1 (y_v x) - pf_sp0 (y_v x)) (Z_to_bv 64 (BASE + B9_J4)) _ HJ Hsp Ho16 ltac:(lia)
    ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia) C1r
    (fun a (H : False) => False_ind _ H)).
  exact (ASTRLEN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv vp0 (seg_spec.zb (b9_v0 x ei))
    Q1 Q2 Q3 Q4 Q5 Q6 Q7). }
(* back at 0x88440 = J4 *)
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & HK3).
change (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + B9_J4)) mem3 (seg_rom SEGS)) md3)
  with (cfg_at SEGS (BASE + B9_J4) regs3 mem3 md3).
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 (y_v x) - ESTACK <= a < pf_s1 (y_v x)) ->
  rdW Wc mem3 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite HK3; [exact (KM1 a Ha) | exact Ha | lia | tauto]. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW Wc mem3 a = rdW Wc memc a).
{ intros a Ha Hw. apply KM2; [exact Ha|]. intros Hn. apply Hw. left.
  rewrite SPF in G1 |- *. unfold ESTACK in Hn. lia. }
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> rdW Wc mem3 a = rdW Wc memc a).
{ intros a Ha. apply KM2; [lia|]. rewrite SPF in G1. unfold ESTACK. lia. }
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc mem3 a <> None).
{ intros a0 Hv0. rewrite b9s4_aview_mod in Hv0 |- *.
  pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
  destruct (Z_lt_le_dec (a0 mod 2 ^ 64) (pf_s1 (y_v x) - ESTACK)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec (a0 mod 2 ^ 64) (pf_s1 (y_v x))) as [Hhi | Hhi]].
  - rewrite (KM2 (a0 mod 2 ^ 64) Ha ltac:(lia)). exact Hv0.
  - pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
    apply (aview_some_of_apresent SEGS). apply Hpres3. rewrite SPF in *. unfold ESTACK in Hlo. lia.
  - rewrite (KM2 (a0 mod 2 ^ 64) Ha ltac:(lia)). exact Hv0. }
(* the registers after the call *)
assert (Hpre : forall k z, In k b9s4_kept -> acallee_saved k -> getr rX (Z_to_bv 5 k) = w64 z ->
  getr regs3 (Z_to_bv 5 k) = w64 z).
{ intros k z Hk Hcs Hz. rewrite (HP3 k Hcs). exact (Rz k z Hk Hz). }
assert (D19' : getr regs3 (Z_to_bv 5 19) = w64 vp0).
{ rewrite (HP3 19 ltac:(unfold acallee_saved; lia)).
  apply (b9s4_bvr' _ 19%bv 19); [reflexivity | exact D19]. }
assert (HLn : astr_len (seg_spec.zb (b9_v0 x ei)) = Z.of_nat (length (b9_v0 x ei)))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
assert (C10' : getr regs3 (Z_to_bv 5 10) = w64 (Z.of_nat (length (b9_v0 x ei)))).
{ apply (b9s4_bvr' _ 10%bv 10); [reflexivity|]. rewrite <- HLn. exact Ha03. }
assert (HFI3 : pf_rg regs3 (b9_FI B (y_v x))).
{ unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (apply Hpre; [b9s4_in | unfold acallee_saved; lia | apply (b9_rg_get rX _ _ _ HRG0); b9s4_in]). }
assert (HB3 : pf_base B (y_v x) (y_pos x) lyc Sc Wc regs3 mem3 md3 PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc regs3 mem3 md3 PF_SC_LINE
    HB HJ3); [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV
    | exact HFI3 |].
  eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
assert (HST3 : pf_st (y_v x) (y_pos x) (rdW Wc mem3) (y_cf x) (y_cur x) (y_nm x) (b9_k x)).
{ first
    [ exact (b9_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc (rdW Wc mem3) G HAR Hin Hly KW
               (y_cf x) (y_cur x) (y_nm x) (b9_k x) HC5 HST)
    | exact (b9_keep_st B (y_v x) (y_pos x) lyc Sc Wc memc mdc (rdW Wc mem3) G HAR Hin Hly KW KV
               (y_cf x) (y_cur x) (y_nm x) (b9_k x) HC5 HST)
    | (eapply b9_keep_st; eassumption) ]. }
assert (HKS3 : sa_str (rdW Wc mem3) kp (b9_key x ei)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS HQ0 HQ1). exact KLOW. }
assert (HVS3 : sa_str (rdW Wc mem3) vp0 (b9_v0 x ei)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HVS HV0 HV1). exact KLOW. }
unfold from_J4, b9_from in FJ4.
apply (FJ4 x ei kp vp0 lyc Sc Wc regs3 mem3 md3).
unfold INV_J4, b9_core, b9_inbuf, b9_buf, pf_inb, PF_O_BUF.
split; [|split; [|split; [|split; [|split]]]].
- (* b9_core *)
  split; [exact HB3|]. split; [exact HMID|]. split; [exact HST3|].
  split; [exact HLEN|]. split; [exact HD0 | exact HDL].
- exact HSC.
- split; [exact HKS3 | lia].
- lia.
- split; [exact HVS3 | lia].
- unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [ exact D19' | exact C10'
          | apply Hpre; [b9s4_in | unfold acallee_saved; lia | apply (b9_rg_get rX _ _ _ HRG); b9s4_in] ].
Qed.

End x.
End d.
