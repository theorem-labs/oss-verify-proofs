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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 513 of its 553 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s12.v, with its module paths and module names changed; 415 of its 459 lines of code are new or changed and 509 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segment S03 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
   lt_seg_S03_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, from the cut K8507c (calloc(1, 9236) returned m)
   to the head of file turn 0, K85110 (f = 0). 39 instructions (0x8507c .. 0x8510c and the two abort jumps).

   What the code does (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s, sha256 be3c0d79cc92):
   0x8507c sd s5,168(s1) (c); 0x85080 bnez s5 / 0x85084 j 0x85fcc (c NULL: abort edge); 0x85088 mv s6,a0 (m);
   0x8508c bnez a0 / 0x85090 j 0x85fcc (m NULL: abort edge); 0x85094 .. 0x850cc the slots 64 FR+32, 88 FR+96,
   112 FR+176, 120 FR+192, 16 FR, 48 FR+256, 40 cap (lbu 56(s1)), 216 m+0x2000 (s2 = m + 0x2000);
   0x850d0 ld a0,168(s1); 0x850d4 jal reac_segconf_init; 0x850d8 .. 0x8510c s9 = 0, s5 = m & 3, 208 ~m, 80 m+0x10,
   72 m+0x20, a4 = 1, 176 1, 192 m, s2 = nfiles (ld 104(s1)), 96 s5. No instrumented check and no UBSan trap
   branch in this stretch (map section 10 lists none for S03).

   THE PROOF (the image-B harness walk's form, plugin-hostd/fuzz_command lib/B/Prog/LLVMFuzzerTestOneInput_s10.v,
   _s65.v and _s70.v at origin/ossv/recipes 3abc3740de97; no image-A twin file was pushed when this was written):
   - s13_call: the symbolic run from K8507c (seed s13_ss1: every register its own atom, seven regions on
     atom 9 = s1, the slots the run writes and the cap word at 56(s1) as a read-only chunk; the facts c, m >= 4096
     decide both NULL tests inside the run, so the two abort edges are never stepped), to the jal; the call through
     PaNoChain.cl_callS_wide with reac_segconf_init's contract (its footprint the block c, a block made since the
     entry; the frame chain at the callee from achain_any over astack_pres carried by astack_pres_journal: s0 =
     SP0 is a frame pointer); the post's sa_kept keeps every byte outside the callee's window and c's block, so the
     frame, its shadow, the saved registers, the slots, m's zeros and the image facts carry over (sep_block_frame,
     sep_blocks, blk_off_imgP, the shadow band of application addresses).
   - s13_ret: the run from the return pc 0x850d8 (seed s13_ss2: the nfiles word at 104(s1) as a chunk, m 16-aligned,
     so andi s5,s6,3 is 0 in the run) to K85110 (paj_run_to_tok, stop 0x350); the reader model: c holds rconf0
     (reac_segconf_init's post), m's 9236 zero bytes encode mconf0 (seg_spec.mconf_enc_zero), seg_run at 0 is
     (rconf0, mconf0, true), so returned = 1 and every counter is 0.
   Section hypotheses (LAWS is the kit's YG0q.AR_laws_ok, a Let): MTFL (the meter's fake-stack laws: the call's post
   S' = set_fs f S), HREAC_SEGCONF_INIT (the callee's contract at its call target pa_sigma SS_reac_segconf_init and
   SegInstB.STK_reac_segconf_init). *)

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_init_c
  LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s13k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaLibF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Ltac s13_ck HS E9 i off :=
  eapply (s13_chunk_rd _ _ _ _ i _ 9 off _ _ _ HS); [reflexivity | reflexivity | cbn; tauto | exact E9 | | ].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis HREAC_SEGCONF_INIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (SIG SS_reac_segconf_init) STK_reac_segconf_init.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Definition s13_RET_stmt : Prop :=
  forall cx ly S (W : world SEGS) regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 ->
  lt_core B MT cx ly S W regs mem md k acc (6 + 2 * x_nf cx) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  zero_atA (rdW W mem) m seg_spec.SEG_M_SIZE -> sa_rconf (rdW W mem) c SegModel.rconf0 ->
  getr regs 20 = w64 (x_curn cx 0) -> getr regs 22 = w64 m -> getr regs 24 = w64 (x_cur cx 0) ->
  lt_slots cx (rdW W mem) (LT_LH cx ++
    [(16, x_fr cx); (40, x_cap cx); (48, x_fr cx + FO_N); (64, x_fr cx + FO_V); (88, x_fr cx + FO_LABEL);
     (112, x_fr cx + FO_R); (120, x_fr cx + FO_PROBE); (168, c); (216, m + seg_spec.MC_N)]) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x318) regs mem md) (lt_post B MT cx).

Lemma s13_call : s13_RET_stmt -> LT_K8507c_stmt B MT.
Proof.
intros HRET cx ly S W regs mem md k acc c m HB HFRM HCORE Hhc Hhm HZ R10 R18 R19 R20 R21 R24 HSL.
pose proof HB as HB0. unfold lt_base in HB0.
destruct HB0 as (HPRE & HSTP & HROD & HIMG0 & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & Hsp & Hgp & Htp & H8 & H9 & Hsv & Hw0 & Hw8 & Hw16 & HwF & H200 & Hzs & H184).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hhc as (Hcin & Hc4 & Hc16 & Hcad). pose proof Hhm as (Hmin & Hm4 & Hm16 & Hmad).
pose proof Hcad as (Hc0 & Hc63 & _). pose proof Hmad as (Hm0 & Hm63 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite WS in Hslo, Hbot.
pose proof (s13_cap_range (x_pl cx)) as Hcap. pose proof (s13_nfiles_range (x_pl cx)) as Hnf.
assert (Hs1 : x_sp0 cx - 383 <= x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0).
{ unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)). split; [lia|].
  rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
assert (Hsp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.

unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hc63, Hm63.
assert (H56 : rdword (rdW W mem) (x_s1 cx + 56) = Some (x_cap cx)) by (apply HSL; cbn; tauto).
assert (H104 : rdword (rdW W mem) (x_s1 cx + 104) = Some (x_nf cx)) by (apply HSL; cbn; tauto).
assert (H24 : rdword (rdW W mem) (x_s1 cx + 24) = Some (x_fr cx)) by (apply HSL; cbn; tauto).
assert (H32 : rdword (rdW W mem) (x_s1 cx + 32) = Some (x_flags cx)) by (apply HSL; cbn; tauto).
pose proof (s13_seed1 W regs mem (x_s1 cx) c m (x_cap cx) H9 R21 R10 ltac:(lia) Hc16 ltac:(lia) Hm16
  ltac:(unfold x_cap; lia) H56 ltac:(intros a Ha; apply Hpres; rewrite WS; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (SHOK : sh_ok SEGS s13_Bx [] (s13_E regs (x_cap cx)) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s13_E regs (x_cap cx))) by (unfold s13_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (s13_E regs (x_cap cx)) n = ew (Ereg regs [Z_to_bv 64 (x_cap cx)]) n)
  by (intros n Hn; unfold s13_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s13_E regs (x_cap cx)) n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew (s13_E regs (x_cap cx)) 32 = Z_to_bv 64 (x_cap cx))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : bv_unsigned (ew (s13_E regs (x_cap cx)) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
remember (s13_E regs (x_cap cx)) as E eqn:HE. clear HE EL.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK s13_Bspan.

{ change (ss_mem s13_ss1) with s13_rs1. unfold s13_rs1.
  repeat first [ apply awr_ok_nil
    | apply (awr_ok_cons_stack_off SEGS B E _ _ _ _ _ _ _ _ _ _ 9 (x_s1 cx - x_sp0 cx));
      [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | ] ]. }

pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (20%bv : bv 5) P20. prreg HS (22%bv : bv 5) P22. prreg HS (24%bv : bv 5) P24.

rewrite (EEo 2%nat 2%bv eq_refl), Hsp in P2. rewrite (EEo 3%nat 3%bv eq_refl), Hgp, Hgp0 in P3.
rewrite (EEo 4%nat 4%bv eq_refl), Htp, Htp0 in P4. rewrite (EEo 8%nat 8%bv eq_refl), H8 in P8.
rewrite (EEo 9%nat 9%bv eq_refl), H9 in P9. rewrite (EEo 21%nat 21%bv eq_refl), R21 in P10.
rewrite (EEo 20%nat 20%bv eq_refl), R20 in P20. rewrite (EEo 10%nat 10%bv eq_refl), R10 in P22.
rewrite (EEo 24%nat 24%bv eq_refl), R24 in P24.
pose proof pa_B_ok as (HBA0 & HBA1 & HBA2). pose proof pa_base_lo as HBLO.
assert (Hspc : spZ (ms_regs ms) = x_s1 cx) by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
assert (Hs0c : s0Z (ms_regs ms) = x_sp0 cx) by (unfold s0Z; rewrite P8; apply unsigned_lit_small; lia).

assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((x_s1 cx + 16 <= a < x_s1 cx + 24) \/ (x_s1 cx + 40 <= a < x_s1 cx + 56) \/ (x_s1 cx + 64 <= a < x_s1 cx + 72) \/
     (x_s1 cx + 88 <= a < x_s1 cx + 96) \/ (x_s1 cx + 112 <= a < x_s1 cx + 128) \/
     (x_s1 cx + 168 <= a < x_s1 cx + 176) \/ (x_s1 cx + 216 <= a < x_s1 cx + 224)) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ apply (kept_of_frame (segs := SEGS) E (ss_mem s13_ss1) (w_H W) mem (ms_mem ms) _ HFr).
  intros b wlo whi a Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite E9 in Hrr; lia|]).
  destruct Hin. }
assert (HSTP1 : astack_pres ly (w_H W) (ms_mem ms) (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ apply (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [rewrite <- Hsp0 in HSTP; exact HSTP|].
  intros a (r & Hr & Ha) Ha2. unfold ltoi_PG in Hr. cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  exfalso. unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
assert (HRD1 : astack_rd ly (rdW W (ms_mem ms)) (x_s1 cx)).
{ apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [rewrite WS; lia|].
  apply astack_rd_of_pres. exact HSTP1. }
destruct (achain_any ly (rdW W (ms_mem ms)) (x_s1 cx) (x_sp0 cx) HRD1 ltac:(right; right; right; lia)) as (ch1 & Hch1).

pose proof (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof (al_frames _ _ LAWS ly S W mem md _ _ HAR HinF) as (Hfr32 & Hfapp & Hfpres & Hfsh).
assert (EFR : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr; rewrite Efa; reflexivity).
rewrite EFR in Hfr32, Hfapp, Hfpres, Hfsh.
assert (Hfb : fs_frame_bytes LT_FCLS = 512) by reflexivity.
rewrite Hfb in Hfapp, Hfpres, Hfsh.
pose proof Hfapp as (HFR4 & HFRa).
assert (HFRc : x_fr cx + 512 <= alloc_ceiling) by (unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFRa; lia).
assert (E19 : ew E 19 = Z_to_bv 64 (x_fr cx)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 c) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
assert (E10 : ew E 10 = Z_to_bv 64 m) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = Z_to_bv 64 seg_spec.MC_N) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (Q16 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 16) = Some (x_fr cx)).
{ s13_ck HS E9 0%nat 16; [apply (s13_denot_off E 19 0 (x_fr cx)) in E19; [rewrite Z.add_0_r in E19; exact E19 | lia | lia] | lia]. }

assert (Q40 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 40) = Some (x_cap cx)).
{ s13_ck HS E9 1%nat 40; [rewrite denot_lit_U, (U_atom E 32 (x_cap cx) E32) by (unfold x_cap; lia); reflexivity | unfold x_cap; lia]. }
assert (Q48 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 48) = Some (x_fr cx + FO_N)).
{ s13_ck HS E9 1%nat 48; [apply s13_denot_off; [exact E19 | lia | unfold FO_N; lia] | unfold FO_N; lia]. }
assert (Q64 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 64) = Some (x_fr cx + FO_V)).
{ s13_ck HS E9 2%nat 64; [apply s13_denot_off; [exact E19 | lia | unfold FO_V; lia] | unfold FO_V; lia]. }
assert (Q88 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 88) = Some (x_fr cx + FO_LABEL)).
{ s13_ck HS E9 3%nat 88; [apply s13_denot_off; [exact E19 | lia | unfold FO_LABEL; lia] | unfold FO_LABEL; lia]. }
assert (Q112 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 112) = Some (x_fr cx + FO_R)).
{ s13_ck HS E9 4%nat 112; [apply s13_denot_off; [exact E19 | lia | unfold FO_R; lia] | unfold FO_R; lia]. }
assert (Q120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some (x_fr cx + FO_PROBE)).
{ s13_ck HS E9 4%nat 120; [apply s13_denot_off; [exact E19 | lia | unfold FO_PROBE; lia] | unfold FO_PROBE; lia]. }
assert (Q168 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 168) = Some c).
{ s13_ck HS E9 5%nat 168; [rewrite denot_lit_U, (U_atom E 21 c E21) by lia; reflexivity | lia]. }
assert (Q216 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)).
{ s13_ck HS E9 6%nat 216; [apply s13_denot_add; [exact E10 | exact E18 | lia | unfold seg_spec.MC_N; lia | unfold seg_spec.MC_N; lia]
  | unfold seg_spec.MC_N; lia]. }

assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 792))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 792))) by (rewrite unsigned_lit_small; lia).
assert (Hal1 : (x_s1 cx - x_sp0 cx) mod 16 = 0) by (rewrite Hsp0 in *; lia).
assert (HND : List.NoDup (ablocks B ly S)).
{ destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR Hcin) as (_ & _ & _ & _ & _ & Hpw & _).
  apply s13_pw_nodup; [exact Hpw|]. apply Forall_forall. intros [p0 n0] Hpq.
  destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hpq) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia. }
assert (HND2 := Permutation_NoDup HBL HND).
assert (Hcb0 : ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx)).
{ intros Hx. cbn [app] in HND2. apply NoDup_cons_iff in HND2 as [_ HND2]. apply NoDup_cons_iff in HND2 as [Hn _].
  exact (Hn Hx). }
destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR Hcin) as (_ & _ & Hcceil & Hcapp & _).
change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hcceil, Hcapp.
assert (Hcad1 : sa_addr (rdW W (ms_mem ms)) c seg_spec.SEG_C_SIZE).
{ apply (s13_sa_addr_kept (rdW W mem)); [exact Hcad | exact Hcapp | unfold seg_spec.SEG_C_SIZE; lia |].
  intros a Ha. apply K1; unfold s13_shz, kLowMemEnd, kHighMemBeg in Ha; lia. }
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (SIG SS_reac_segconf_init))
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md1 k STK_reac_segconf_init [(c, c + seg_spec.SEG_C_SIZE)] EV_reac_segconf_init
    (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 792)) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' (md' : Model) =>
       getr regs' 10 = w64 c /\
       sa_bytes (aview SEGS (w_H W') mem') c (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)) /\
       sa_rconf (aview SEGS (w_H W') mem') c SegModel.rconf0 /\
       sa_kept SEGS W (ms_mem ms) W' mem' (ms_regs ms) STK_reac_segconf_init
         (fun a => c <= a < c + seg_spec.SEG_C_SIZE) /\
       sa_noalloc B ly S ly' S')
    HJ ltac:(lia) Hal1 ltac:(lia) ltac:(unfold STK_reac_segconf_init, ESTACK; lia)
    ltac:(rewrite WS; unfold STK_reac_segconf_init, ESTACK; lia) P3 P4 P1 Hraw Hra4
    ltac:(replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia; rewrite Hs0c; exact Hch1)).
  - intros HPRE1. eapply SRr_mono.
    + apply (HREAC_SEGCONF_INIT fx ly S W (ms_regs ms) (ms_mem ms) md1 ch1 c HPRE1 P10 ltac:(lia)).
      * split; [lia|]. split; [exact Hc16|]. split; [exists c, seg_spec.SEG_C_SIZE; split; [exact Hcin | lia]|].
        exact Hcad1.
      * unfold EV_reac_segconf_init. pose proof HBUD as (Hb1 & Hb2 & Hb3 & _). lia.
    + intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. rewrite P1 in Hc3. split; [exact Hc3|]. split; [exact HJ3|]. split; [exact HP3|].
      exact HQ3.
  - intros a (r & Hr & Ha). cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; left. exists c, seg_spec.SEG_C_SIZE. split; [exact Hcin|]. split; [exact Hcb0|].
    change (req_size seg_spec.SEG_C_SIZE) with 16616. unfold seg_spec.SEG_C_SIZE in Ha. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha). cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    intros Ha2. exfalso. unfold seg_spec.SEG_C_SIZE in Ha. rewrite WS in Ha2. lia. }
cbv beta. intros W2 c2 HW2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (Q10 & Qzb & Qrc & Qkept & Qna)).

pose proof Qna as (Hpna & -> & (fs2 & ES2)).
assert (Ek : k + EV_reac_segconf_init = k) by (unfold EV_reac_segconf_init; lia). rewrite Ek in HJ2.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - STK_reac_segconf_init <= a < x_s1 cx) ->
  ~ (c <= a < c + seg_spec.SEG_C_SIZE) -> rdW W2 mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha H1 H2. apply Qkept; [exact Ha | rewrite Hspc; exact H1 | exact H2]. }
assert (Hs1c : alloc_ceiling + 32000 <= x_s1 cx) by (rewrite Hsp0 in *; lia).
assert (KA : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((x_s1 cx + 16 <= a < x_s1 cx + 24) \/ (x_s1 cx + 40 <= a < x_s1 cx + 56) \/ (x_s1 cx + 64 <= a < x_s1 cx + 72) \/
     (x_s1 cx + 88 <= a < x_s1 cx + 96) \/ (x_s1 cx + 112 <= a < x_s1 cx + 128) \/
     (x_s1 cx + 168 <= a < x_s1 cx + 176) \/ (x_s1 cx + 216 <= a < x_s1 cx + 224)) ->
  ~ (x_s1 cx - STK_reac_segconf_init <= a < x_s1 cx) -> ~ (c <= a < c + seg_spec.SEG_C_SIZE) ->
  rdW W2 mem2 a = rdW W mem a).
{ intros a Ha H1 H2 H3. rewrite (K2 a Ha H2 H3). exact (K1 a Ha H1). }
assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (c <= a < c + seg_spec.SEG_C_SIZE) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha H3. apply KA; [lia | | | exact H3]; unfold STK_reac_segconf_init, ESTACK; lia. }
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 ->
  ~ ((x_s1 cx + 16 <= a < x_s1 cx + 24) \/ (x_s1 cx + 40 <= a < x_s1 cx + 56) \/ (x_s1 cx + 64 <= a < x_s1 cx + 72) \/
     (x_s1 cx + 88 <= a < x_s1 cx + 96) \/ (x_s1 cx + 112 <= a < x_s1 cx + 128) \/
     (x_s1 cx + 168 <= a < x_s1 cx + 176) \/ (x_s1 cx + 216 <= a < x_s1 cx + 224)) ->
  rdW W2 mem2 a = rdW W mem a).
{ intros a Ha H1. apply KA; [lia | exact H1 | lia | unfold seg_spec.SEG_C_SIZE; lia]. }
assert (KS1 : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha. apply K2; [lia | lia | unfold seg_spec.SEG_C_SIZE; lia]. }

pose proof (sep_block_frame SEGS B LAWS ly S W mem md c seg_spec.SEG_C_SIZE _ _ HAR Hcin HinF) as HcF.
rewrite EFR, Hfb in HcF. change (req_size seg_spec.SEG_C_SIZE) with 16616 in HcF. unfold zdisjoint in HcF. cbn [fst snd] in HcF.
assert (Hmc : (m, seg_spec.SEG_M_SIZE) <> (c, seg_spec.SEG_C_SIZE)) by (intros Hq; injection Hq as _ Hq; discriminate Hq).
pose proof (sep_blocks SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE c seg_spec.SEG_C_SIZE HAR Hmin Hcin Hmc) as HmC.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HmC. change (req_size seg_spec.SEG_C_SIZE) with 16616 in HmC.
unfold zdisjoint in HmC. cbn [fst snd] in HmC.
pose proof (blk_off_imgP B ly S W mem md c seg_spec.SEG_C_SIZE HAR Hcin) as HcI.
unfold off_img in HcI. change (req_size seg_spec.SEG_C_SIZE) with 16616 in HcI.
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as (_ & _ & Hmceil & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmceil, Hmapp.
pose proof Hcapp as Hcapp'. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hcapp'.
assert (KZ : forall a, s13_shz a -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. unfold s13_shz, kLowMemEnd, kHighMemBeg in Ha. apply KL; [lia|]. unfold seg_spec.SEG_C_SIZE. lia. }
assert (KB : forall a, s13_band a -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. unfold s13_band, kImgEnd in Ha. apply KL; [lia|]. unfold seg_spec.SEG_C_SIZE. lia. }

assert (KFR : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply KL; clear - Ha HcF HFRc HFR4; unfold seg_spec.SEG_C_SIZE; lia. }
assert (KSH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply KZ. pose proof alloc_ceiling_value as [[AC1 AC2] _].
  clear - Hi HFRa HFRc HFR4 AC1 AC2. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFRa.
  unfold x_sh, shadow_addr, SHADOW_OFF, s13_shz, kLowMemEnd, kHighMemBeg. lia. }
assert (KSV : forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply KS; clear - Ha Hs1 Hsp0 Hshi H47; rewrite Hsp0 in *; lia. }
assert (KSL : forall o j, (o = 24 \/ o = 32 \/ o = 56 \/ o = 104 \/ o = 184 \/ o = 200) -> 0 <= j < 8 ->
  rdW W2 mem2 (x_s1 cx + o + j) = rdW W mem (x_s1 cx + o + j)).
{ intros o j Ho Hj. apply KS; clear - Ho Hj Hs1 Hsp0 Hshi H47; rewrite Hsp0 in *; lia. }
assert (KS1' : forall o j, 0 <= o <= 224 -> 0 <= j < 8 ->
  rdW W2 mem2 (x_s1 cx + o + j) = rdW W (ms_mem ms) (x_s1 cx + o + j)).
{ intros o j Ho Hj. apply KS1. clear - Ho Hj Hs1 Hsp0 Hshi H47; rewrite Hsp0 in *; lia. }
assert (KM : forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rdW W2 mem2 (m + i) = rdW W mem (m + i)).
{ intros i Hi. apply KL; clear - Hi HmC Hmceil Hm4; unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *; lia. }
pose proof Hcapp as Hcapp0. pose proof Hmapp as Hmapp0.
clear Hpn HcF HmC HcI Hcapp' Hcapp Hmapp HFRa Hfapp.
apply (HRET cx ly S2 W2 regs2 mem2 md2 k acc c m HB HFRM).

- split; [|split; [|split]].
  + split; [exact HJ2|].
    split; [rewrite (s13_pres (ms_regs ms) regs2 2%bv 2 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact P2|].
    split; [rewrite (s13_pres (ms_regs ms) regs2 3%bv 3 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P3; symmetry; exact Hgp0|].
    split; [rewrite (s13_pres (ms_regs ms) regs2 4%bv 4 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P4; symmetry; exact Htp0|].
    split; [rewrite (s13_pres (ms_regs ms) regs2 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact P8|].
    split; [rewrite (s13_pres (ms_regs ms) regs2 9%bv 9 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact P9|].
    split; [exact (s13_saved_kept cx (rdW W mem) (rdW W2 mem2) KSV Hsv)|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hw0 | intros j Hj; apply KFR; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hw8 | intros j Hj; apply KFR; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hw16 | intros j Hj; apply KFR; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HwF | intros j Hj; unfold LT_FLAGW; apply KFR; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact H200 | intros j Hj; apply (KSL 200 j); lia]|].
    split; [apply (s13_zs_kept (rdW W mem)); [|exact Hzs]; intros i Hi; rewrite lt_fsh_len in Hi; apply KSH; lia|].
    rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact H184 | intros j Hj; apply (KSL 184 j); lia].
  + exact (s13_img_kept B cx W W2 mem mem2 KB HIMG).
  + unfold lt_blocks. eapply Permutation_trans; [|exact HBL]. exact Hpna.
  + pose proof HBUD as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
    split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|]. split; [rewrite ES2; exact (mo_le_set_fs_r MT MTFL _ _ fs2 acc Hb4)|].
    split; [exact Hb5 | exact Hb6].

- split; [apply (Permutation_in _ (Permutation_sym Hpna)); exact Hcin|]. split; [exact Hc4|]. split; [exact Hc16|].
  apply (s13_sa_addr_kept (rdW W mem)); [exact Hcad | exact Hcapp0 | unfold seg_spec.SEG_C_SIZE; lia | exact KZ].
- split; [apply (Permutation_in _ (Permutation_sym Hpna)); exact Hmin|]. split; [exact Hm4|]. split; [exact Hm16|].
  apply (s13_sa_addr_kept (rdW W mem)); [exact Hmad | exact Hmapp0 | unfold seg_spec.SEG_M_SIZE; lia | exact KZ].
- intros i Hi. rewrite KM by exact Hi. exact (HZ i Hi).
- exact Qrc.
- rewrite (s13_pres (ms_regs ms) regs2 20%bv 20 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P20.
- rewrite (s13_pres (ms_regs ms) regs2 22%bv 22 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P22.
- rewrite (s13_pres (ms_regs ms) regs2 24%bv 24 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P24.
- apply s13_slots_app.
  + apply (s13_slots_kept cx (rdW W mem)); [|exact HSL].
    intros o v Hin j Hj. unfold LT_LH in Hin. cbn [In] in Hin.
    apply KSL; [|exact Hj]. destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- _; tauto.
  + intros o v Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
      match goal with H : rdword (rdW W (ms_mem ms)) (x_s1 cx + ?o) = Some _ |- rdword _ (x_s1 cx + ?o) = _ =>
        rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W2 mem2)); [exact H | intros j Hj; apply KS1'; lia] end|]).
    destruct Hin.
Qed.

Lemma s13_ret : LTA_K85110 B MT 0 -> s13_RET_stmt.
Proof.
intros HK cx ly S W regs mem md k acc c m HB HFRM HCORE Hhc Hhm HZ Hrc R20 R22 R24 HSL.
pose proof HB as HB0. unfold lt_base in HB0.
destruct HB0 as (HPRE & HSTP & HROD & HIMG0 & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
clear Hpn.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & Hsp & Hgp & Htp & H8 & H9 & Hsv & Hw0 & Hw8 & Hw16 & HwF & H200 & Hzs & H184).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hhc as (Hcin & Hc4 & Hc16 & Hcad). pose proof Hhm as (Hmin & Hm4 & Hm16 & Hmad).
pose proof Hcad as (Hc0 & Hc63 & _). pose proof Hmad as (Hm0 & Hm63 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite WS in Hslo, Hbot.
pose proof (s13_cap_range (x_pl cx)) as Hcap. pose proof (s13_nfiles_range (x_pl cx)) as Hnf.
assert (Hs1 : x_sp0 cx - 383 <= x_s1 cx <= x_sp0 cx - 352 /\ x_s1 cx mod 32 = 0).
{ unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)). split; [lia|].
  rewrite Zminus_mod, Z.mod_mod, Z.sub_diag, Z.mod_0_l by lia. reflexivity. }
assert (Hsp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hc63, Hm63.
assert (H104 : rdword (rdW W mem) (x_s1 cx + 104) = Some (x_nf cx)) by (apply HSL; cbn; tauto).
pose proof (s13_seed2 W regs mem (x_s1 cx) m (x_nf cx) H9 R22 ltac:(lia) Hm16 ltac:(unfold x_nf; lia) H104
  ltac:(intros a Ha; apply Hpres; rewrite WS; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (SHOK : sh_ok SEGS s13_Bx [] (s13_E regs (x_nf cx)) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s13_E regs (x_nf cx))) by (unfold s13_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (s13_E regs (x_nf cx)) n = ew (Ereg regs [Z_to_bv 64 (x_nf cx)]) n)
  by (intros n Hn; unfold s13_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s13_E regs (x_nf cx)) n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew (s13_E regs (x_nf cx)) 32 = Z_to_bv 64 (x_nf cx))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : bv_unsigned (ew (s13_E regs (x_nf cx)) 9) = x_s1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
remember (s13_E regs (x_nf cx)) as E eqn:HE. clear HE EL.
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK s13_Bspan 0x350.
{ change (ss_mem s13_ss2) with s13_rs2. unfold s13_rs2.
  repeat first [ apply awr_ok_nil
    | apply (awr_ok_cons_stack_off SEGS B E _ _ _ _ _ _ _ _ _ _ 9 (x_s1 cx - x_sp0 cx));
      [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | ] ]. }
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.

prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (14%bv : bv 5) P14. prreg HS (18%bv : bv 5) P18.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
rewrite (EEo 2%nat 2%bv eq_refl) in P2. rewrite (EEo 3%nat 3%bv eq_refl) in P3.
rewrite (EEo 4%nat 4%bv eq_refl) in P4. rewrite (EEo 8%nat 8%bv eq_refl) in P8.
rewrite (EEo 9%nat 9%bv eq_refl) in P9. rewrite E32 in P18.
rewrite (EEo 20%nat 20%bv eq_refl), R20 in P20. rewrite (EEo 22%nat 22%bv eq_refl), R22 in P22.
rewrite (EEo 24%nat 24%bv eq_refl), R24 in P24.
assert (K3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((x_s1 cx + 72 <= a < x_s1 cx + 88) \/ (x_s1 cx + 96 <= a < x_s1 cx + 104) \/ (x_s1 cx + 176 <= a < x_s1 cx + 184) \/
     (x_s1 cx + 192 <= a < x_s1 cx + 200) \/ (x_s1 cx + 208 <= a < x_s1 cx + 216)) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ apply (kept_of_frame (segs := SEGS) E (ss_mem s13_ss2) (w_H W) mem (ms_mem ms) _ HFr).
  intros b wlo whi a Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite E9 in Hrr; lia|]).
  destruct Hin. }
assert (Hs1c : alloc_ceiling + 32000 <= x_s1 cx) by (rewrite Hsp0 in *; lia).
assert (KL : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply K3; lia. }
assert (KZ : forall a, s13_shz a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply KL. unfold s13_shz, kLowMemEnd, kHighMemBeg in Ha. lia. }
assert (KB : forall a, s13_band a -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply KL. unfold s13_band, kImgEnd in Ha. lia. }
assert (KSV : forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply K3; clear - Ha Hs1 Hs1c C1 Hsp0 Hshi H47; rewrite Hsp0 in *; lia. }
assert (KSL : forall o j, (o = 16 \/ o = 24 \/ o = 32 \/ o = 40 \/ o = 48 \/ o = 56 \/ o = 64 \/ o = 88 \/ o = 104 \/
  o = 112 \/ o = 120 \/ o = 168 \/ o = 184 \/ o = 200 \/ o = 216) -> 0 <= j < 8 ->
  rdW W (ms_mem ms) (x_s1 cx + o + j) = rdW W mem (x_s1 cx + o + j)).
{ intros o j Ho Hj. apply K3; clear - Ho Hj Hs1 Hs1c C1 Hsp0 Hshi H47; rewrite Hsp0 in *; lia. }
pose proof (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR HinF) as (HFR4 & HFRc & HFRa).
assert (EFR : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr; rewrite Efa; reflexivity).
assert (Hfb : fs_frame_bytes LT_FCLS = 512) by reflexivity.
rewrite EFR in HFR4. rewrite EFR, Hfb in HFRc, HFRa.
assert (KSH : forall i, 0 <= i < 64 -> rdW W (ms_mem ms) (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply KZ. pose proof alloc_ceiling_value as [[AC1 AC2] _].
  clear - Hi HFRa HFRc HFR4 AC1 AC2. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFRa.
  unfold x_sh, shadow_addr, SHADOW_OFF, s13_shz, kLowMemEnd, kHighMemBeg. lia. }
destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR Hcin) as (_ & _ & Hcceil & Hcapp & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR Hmin) as (_ & _ & Hmceil & Hmapp & _).
change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hcceil, Hcapp.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmceil, Hmapp.
assert (E22 : ew E 22 = Z_to_bv 64 m) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (Q72 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 72) = Some (m + 0x20)).
{ s13_ck HS E9 0%nat 72; [apply s13_denot_off; [exact E22 | lia | lia] | lia]. }

assert (Q80 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 80) = Some (m + 0x10)).
{ s13_ck HS E9 0%nat 80; [apply s13_denot_off; [exact E22 | lia | lia] | lia]. }
assert (Q96 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 96) = Some 0).
{ s13_ck HS E9 1%nat 96; [rewrite denot_lit_U, U_lit by lia; reflexivity | lia]. }
assert (Q176 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 176) = Some 1).
{ s13_ck HS E9 2%nat 176; [rewrite denot_lit_U, U_lit by lia; reflexivity | lia]. }
assert (Q192 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 192) = Some m).
{ s13_ck HS E9 3%nat 192; [rewrite denot_lit_U, (U_atom E 22 m E22) by lia; reflexivity | lia]. }
assert (Q208 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 208) = Some (lt_not m)).
{ s13_ck HS E9 4%nat 208; [rewrite denot_lit_U, (YI08.U_not E 22 m E22) by lia; reflexivity | unfold lt_not; lia]. }

apply (HK fx cx ly S W (ms_regs ms) (ms_mem ms) md3 k acc c m HB HFRM).
- cbn [Z.of_nat]. unfold x_nf. lia.
- cbn [Z.of_nat]. rewrite Z.sub_0_r. split; [|split; [|split]].
  + split; [exact HJ|].
    split; [rewrite P2; exact Hsp|]. split; [rewrite P3; exact Hgp|]. split; [rewrite P4; exact Htp|].
    split; [rewrite P8; exact H8|]. split; [rewrite P9; exact H9|].
    split; [exact (s13_saved_kept cx (rdW W mem) (rdW W (ms_mem ms)) KSV Hsv)|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact Hw0 | intros j Hj; apply KL; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact Hw8 | intros j Hj; apply KL; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact Hw16 | intros j Hj; apply KL; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact HwF | intros j Hj; unfold LT_FLAGW; apply KL; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact H200 | intros j Hj; apply (KSL 200 j); lia]|].
    split; [apply (s13_zs_kept (rdW W mem)); [|exact Hzs]; intros i Hi; rewrite lt_fsh_len in Hi; apply KSH; lia|].
    rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [exact H184 | intros j Hj; apply (KSL 184 j); lia].
  + exact (s13_img_kept B cx W W mem (ms_mem ms) KB HIMG).
  + exact HBL.
  + exact HBUD.
- split; [exact Hcin|]. split; [exact Hc4|]. split; [exact Hc16|].
  apply (s13_sa_addr_kept (rdW W mem)); [exact Hcad | exact Hcapp | unfold seg_spec.SEG_C_SIZE; lia | exact KZ].
- split; [exact Hmin|]. split; [exact Hm4|]. split; [exact Hm16|].
  apply (s13_sa_addr_kept (rdW W mem)); [exact Hmad | exact Hmapp | unfold seg_spec.SEG_M_SIZE; lia | exact KZ].
- exact P14.
- exact P18.
- exact P20.
- exact P21.
- exact P22.
- exact P24.
- exact P25.
- apply s13_slots_app.
  + intros o v Hin. unfold LT_L in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-;
      first [ match goal with H : rdword (rdW W (ms_mem ms)) (x_s1 cx + ?o) = Some ?v |- rdword _ (x_s1 cx + ?o) = Some ?v => exact H end
            | rewrite (rdword_ext (rdW W mem) (rdW W (ms_mem ms))); [apply HSL; cbn; tauto | intros j Hj; apply KSL; [tauto | exact Hj]]
            | match goal with |- rdword _ (x_s1 cx + 192) = Some m => exact Q192 end ] |]).
    destruct Hin.
  + intros o v Hin. cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <-. exact Q176.
- split.
  + apply (s13_rconf_kept (rdW W mem)); [|exact Hrc]. intros i Hi. apply KL. unfold seg_spec.SEG_C_SIZE in Hi. lia.
  + apply s13_mconf0. intros i Hi. rewrite KL by (unfold seg_spec.SEG_M_SIZE in Hi; lia). exact (HZ i Hi).
- unfold lt_cnt. cbn. lia.
Qed.

Theorem lt_seg_S03 : lt_seg_S03_stmt B MT.
Proof. intros HK. exact (s13_call (s13_ret HK)). Qed.

End e.
End f.
End d.
