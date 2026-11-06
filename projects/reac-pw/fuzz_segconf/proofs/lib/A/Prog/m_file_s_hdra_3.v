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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 228 of its 272 lines of code are new or changed and 409 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of L2 (0x863ec, the header strip's backward
   loop): the check of a0 = s4 - 1 (atom 10), `lbu a2,-1(s4)` (the byte sl[r - 1], a read-only text region at atom
   20, s4, over [-1, 0)), `bltu s3,a2` (0x86404) to LEN 0x86490 when the byte is above ' ', `srl/andi/beqz` (0x86410)
   to LEN when its blank-mask bit is 0, else `addi a0,a0,-1; mv s4,a1; bltu s10,a1` (0x8641c) back to L2 with
   r - 1, or 0x86420 `j 8648c` `mv s4,s10` to LEN with r = q. By induction on r - q. No byte is written: the seed's
   slots are read-only (m_file_s_hdra_w.v). The HDRA segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e m_file_s_hdra_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the byte sl[r - 1] the loop loads, `lbu a2,0(a1)` with a1 = s4 - 1: one byte at offset -1 of atom 20 (s4), held
   by atom 52 (the seed's xs = [sl[r - 1]]) *)
Definition hda3_rg : YP09.region :=
  YP09.mkRegion (Some 20%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1%N (SOff 52 0))].

(* two regions with the same extent are apart from the same regions *)
Lemma hda3_alld_ext : forall E r1 r2 rs,
  base_val E (YP09.r_base r1) + YP09.r_lo r1 = base_val E (YP09.r_base r2) + YP09.r_lo r2 ->
  base_val E (YP09.r_base r1) + YP09.r_hi r1 = base_val E (YP09.r_base r2) + YP09.r_hi r2 ->
  all_disjoint E r1 rs -> all_disjoint E r2 rs.
Proof.
intros E r1 r2 rs Hlo Hhi. induction rs as [|r' rs IH]; cbn [all_disjoint]; [tauto|].
intros (Hd & Hr). split; [|exact (IH Hr)]. unfold extent_disjoint in *. lia.
Qed.
(* the value of a literal *)
Lemma hda3_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. unfold U. cbn [sv_denot]. apply unsigned_lit_small. lia. Qed.

(* the strip's three exits and its step *)
Lemma hda3_strip_nb : forall sl k q r, (1 <= q < r)%nat -> (r <= k)%nat -> S k = length sl ->
  hda_all_blank sl 1 q -> (q = k \/ blank (nth q sl 0) = false) -> hda_all_blank sl r k ->
  blank (nth (r - 1) sl 0) = false -> hda_strip sl 1 k q r.
Proof.
intros sl k q r Hq Hr Hk H1 H2 H3 H4. unfold hda_strip.
split; [lia|]. split; [lia|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. right; exact H4.
Qed.
Lemma hda3_blank_step : forall sl k r, (1 <= r)%nat -> (r <= k)%nat -> hda_all_blank sl r k ->
  blank (nth (r - 1) sl 0) = true -> hda_all_blank sl (r - 1) k.
Proof.
intros sl k r Hr Hk H1 H2. apply hda_all_blank_cons; [replace (S (r - 1)) with r by lia; exact H1 | exact H2 | lia].
Qed.
Lemma hda3_strip_done : forall sl k q r, (1 <= q < r)%nat -> (r <= k)%nat -> S k = length sl ->
  hda_all_blank sl 1 q -> (q = k \/ blank (nth q sl 0) = false) -> hda_all_blank sl r k ->
  blank (nth (r - 1) sl 0) = true -> (r - 1 <= q)%nat -> hda_strip sl 1 k q q.
Proof.
intros sl k q r Hq Hr Hk H1 H2 H3 H4 H5. assert (Eq : q = (r - 1)%nat) by lia.
unfold hda_strip. split; [lia|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
split; [|left; reflexivity]. rewrite Eq. apply hda3_blank_step; [lia | lia | exact H3 | exact H4].
Qed.

(* a word of an env the run extended (ewset over the seed's env) is the seed's word, below the new atoms *)
Ltac hda3_ew := repeat (rewrite ew_ewset_other by lia).
(* hda_regs at the end of a run that left the registers alone but for the pinned s3 = ' ' and s9 = the mask *)
Ltac hda3_regs HS EE E32 HR :=
  let R2 := fresh "R" in let R3 := fresh "R" in let R4 := fresh "R" in let R8 := fresh "R" in
  let R9 := fresh "R" in let R18 := fresh "R" in let R19 := fresh "R" in let R25 := fresh "R" in
  let R24 := fresh "R" in
  pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24);
  unfold hda_regs;
  split; [hda_rg HS EE 2%nat (2%bv : bv 5); exact R2|]; split; [hda_rg HS EE 3%nat (3%bv : bv 5); exact R3|];
  split; [hda_rg HS EE 4%nat (4%bv : bv 5); exact R4|]; split; [hda_rg HS EE 8%nat (8%bv : bv 5); exact R8|];
  split; [let Q := fresh "Q" in prreg HS (9%bv : bv 5) Q; rewrite Q, (EE 2%nat 2%bv eq_refl); exact R2|];
  split; [let Q := fresh "Q" in prreg HS (18%bv : bv 5) Q; rewrite Q, E32; reflexivity|];
  split; [let Q := fresh "Q" in prreg HS (19%bv : bv 5) Q; rewrite Q; reflexivity|];
  split; [let Q := fresh "Q" in prreg HS (25%bv : bv 5) Q; rewrite Q; reflexivity|];
  hda_rg HS EE 24%nat (24%bv : bv 5); exact R24.
(* the line's facts across a run that changed no byte *)
Ltac hda3_carry HL HJ HFr :=
  let KA := fresh "KA" in let HL2 := fresh "HL" in
  pose proof (hda_frame_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KA;
  pose proof (hda_line_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ KA) as HL2;
  clear KA HFr HL; rename HL2 into HL.

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
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma hda_l2 : forall n, HDA_LEN_stmt B n -> HDA_L2_stmt B n.
Proof.
intros n LEN. unfold HDA_L2_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r.
remember (r - q)%nat as d eqn:Hd. revert Hd.
revert v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r.
induction d as [|d IH];
  intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r Hd
    HL HR HH HC Hq Hrk HB0 Hq2 HBr R27 R21 R22 R26 R20 R10; [exfalso; lia|].
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & HSTR & HADR & HCOK & _).
pose proof HADR as (Hp0 & Hp1 & _ & HRA & _).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HC as (HMC & HSK).
pose proof (hda_line_le rest) as HLr.
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
rewrite Lsl in HSK.
remember (nth (i + (r - 1)) rest 0) as bt eqn:Ebt.
assert (Hbt : rdW Wc memc (p + Z.of_nat (i + (r - 1))) = Some bt)
  by (rewrite Ebt; apply hda_txt_byte; [exact HSTR | lia]).
assert (Hsl1 : nth (r - 1) (hda_sl rest i j) 0 = bt) by (rewrite Ebt; unfold hda_sl; apply hda_sl_nth; lia).
destruct (aview_byte SEGS _ _ _ _ Hbt) as (bb & _ & _ & Hbt8).
(* the seed, with xs = [sl[r - 1]] *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [bt] HDA_L2
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
(* the checked byte [s4 - 1, s4) at atom 10: its disjointness and atom fact *)
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [bt] 10%nat
  (p + Z.of_nat (i + r) - 1) 1 [] line p rest true true [] false false [] false CX CORE RB LOOP
  ltac:(rewrite (mfE_reg regs1 v lyc pos cur (mf_next p rest) [bt] 10 10%bv eq_refl), R10; reflexivity)
  ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _)) as (_ & AD10 & AF10).
pose proof CORE as (HJ & _).
pose proof (mfE_xs regs1 v lyc pos cur (mf_next p rest) [bt] 0 ltac:(unfold A_TEXT; lia)) as E52.
cbn [Nat.add nth] in E52.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) [bt]) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) [bt]) as E32. fold E in E32.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (U10 : U E (SOff 10 0) = p + Z.of_nat (i + r) - 1)
  by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]).
assert (B10 : base_val E (Some 10%nat) = p + Z.of_nat (i + r) - 1)
  by (cbn [base_val]; rewrite (EE 10%nat 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
assert (B20 : base_val E (Some 20%nat) = p + Z.of_nat (i + r))
  by (cbn [base_val]; rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
(* the loaded byte's region at atom 20 *)
assert (RO : region_ok SEGS E (mrestrict (w_H Wc) memc) hda3_rg).
{ unfold region_ok, hda3_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B20.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat (i + r)) (-1) 1%N (SOff 52 0) bt).
  - cbn [sv_denot]. rewrite E52, Z.add_0_r. rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - lia.
  - replace (p + Z.of_nat (i + r) + -1) with (p + Z.of_nat (i + (r - 1))) by lia.
    change (N.to_nat 1%N) with 1%nat. apply mf_val1_of_aview. exact Hbt. }
assert (AD : all_disjoint E hda3_rg
  (list_upd (mf_regions true true [] false false [] false MF_LOW_OFF) 1 (hda_slots_ro true true []))).
{ apply hda_alld_ro. eapply hda3_alld_ext; [| | exact AD10]; unfold hda3_rg;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?B10, ?B20; lia. }
pose proof (st_ok_pi_add_region E _ _ hda3_rg HS ltac:(vm_compute; reflexivity) RO AD) as HS1. clear HS.
pose proof (st_ok_pi_add_fact E _ _ 10%nat (mkAF 4096 (2 ^ 47 - 8) 0) HS1 AF10) as HS2. clear HS1.
(* s3 = ' ', s9 = the blank mask *)
pose proof (ast_ok_pi_set_reg_fp E _ _ (19%bv : bv 5) (SLit 32) HS2 ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_regs restrict mkst]; rewrite R19; reflexivity)) as HS3. clear HS2.
pose proof (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SLit 0x100002200) HS3 ltac:(vm_compute; reflexivity)
  ltac:(cbn [ms_regs restrict mkst]; rewrite R25; reflexivity)) as HS. clear HS3.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* the check of a0, the load of sl[r - 1], to `bltu s3,a2` 0x86404 *)
paj_run_tok RUN HS HJ SHOK Bspan;
  [ (cbn [ms_mem mkst]; try rewrite U10; eapply obl_of_range; [exact HRA | exact U32 | lia | lia]) ..
  | hda_awr_ro | ].
hda3_carry HL HJ HFr. clear HF HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* sl[r - 1] > ' ': not blank, to LEN with r *)
  rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. rewrite hda3_U_lit in Hc by lia.
  rewrite (hda_U_zext8 _ 52 bt) in Hc by first [lia | hda3_ew; exact E52].
  assert (NB : blank (nth (r - 1) (hda_sl rest i j) 0) = false) by (rewrite Hsl1; apply hda_nonblank_gt; lia).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_LEN; [hda_awr_ro|].
  hda3_carry HL HJ HFr.
  pmkst HS.
  apply (LEN v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q r HL).
  + hda3_regs HS EE E32 HR.
  + exact HH.
  + exact HC.
  + apply hda3_strip_nb; [lia | lia | rewrite Lsl; lia | exact HB0 | exact Hq2 | exact HBr | exact NB].
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  + hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
- (* sl[r - 1] <= ' ' *)
  rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc. rewrite hda3_U_lit in Hc by lia.
  rewrite (hda_U_zext8 _ 52 bt) in Hc by first [lia | hda3_ew; exact E52].
  rename Hc into Hle.
  paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
  hda3_carry HL HJ HFr. clear HF HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* its mask bit is 0: not blank, to LEN with r *)
    rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
    rewrite (hda_U_mask _ 52 bt) in Hc by first [lia | hda3_ew; exact E52].
    rewrite hda3_U_lit in Hc by lia.
    assert (NB : blank (nth (r - 1) (hda_sl rest i j) 0) = false)
      by (rewrite Hsl1; apply (hda_nonblank_of_mask bt); [lia | exact Hc]).
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_LEN; [hda_awr_ro|].
    hda3_carry HL HJ HFr.
    pmkst HS.
    apply (LEN v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q r HL).
    * hda3_regs HS EE E32 HR.
    * exact HH.
    * exact HC.
    * apply hda3_strip_nb; [lia | lia | rewrite Lsl; lia | exact HB0 | exact Hq2 | exact HBr | exact NB].
    * hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
    * hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
    * hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
    * hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  + (* blank: a0 - 1, s4 = a1 = s + r - 1, then `bltu s10,a1` *)
    rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
    rewrite (hda_U_mask _ 52 bt) in Hc by first [lia | hda3_ew; exact E52].
    rewrite hda3_U_lit in Hc by lia.
    assert (BL : blank (nth (r - 1) (hda_sl rest i j) 0) = true)
      by (rewrite Hsl1; apply (hda_blank_of_mask bt); [lia | exact Hc]).
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
    hda3_carry HL HJ HFr. clear HF HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* q < r - 1: back to L2 with r - 1 *)
      rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
      rewrite (U_atom _ 26 (p + Z.of_nat (i + q))) in Hc
        by first [lia | hda3_ew; rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity].
      rewrite (U_atom_off _ 20 (p + Z.of_nat (i + r)) (-1)) in Hc
        by first [lia | hda3_ew; rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity].
      paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L2; [hda_awr_ro|].
      hda3_carry HL HJ HFr.
      pmkst HS.
      apply (IH v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q (r - 1)%nat ltac:(lia) HL).
      -- hda3_regs HS EE E32 HR.
      -- exact HH.
      -- exact HC.
      -- lia.
      -- lia.
      -- exact HB0.
      -- exact Hq2.
      -- apply hda3_blank_step; [lia | lia | exact HBr | exact BL].
      -- hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
      -- hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
      -- hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
      -- hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
      -- prreg HS (20%bv : bv 5) Q20. rewrite Q20, (EE 20%nat 20%bv eq_refl), R20. unfold w64.
         rewrite unsigned_lit_small by lia. f_equal; lia.
      -- prreg HS (10%bv : bv 5) Q10. rewrite Q10, (EE 10%nat 10%bv eq_refl), R10. unfold w64.
         rewrite unsigned_lit_small by lia. f_equal; lia.
    * (* r - 1 <= q: r - 1 = q, `mv s4,s10`, to LEN with r = q *)
      rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
      rewrite (U_atom _ 26 (p + Z.of_nat (i + q))) in Hc
        by first [lia | hda3_ew; rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity].
      rewrite (U_atom_off _ 20 (p + Z.of_nat (i + r)) (-1)) in Hc
        by first [lia | hda3_ew; rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity].
      paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_LEN; [hda_awr_ro|].
      hda3_carry HL HJ HFr.
      pmkst HS.
      apply (LEN v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q q HL).
      -- hda3_regs HS EE E32 HR.
      -- exact HH.
      -- exact HC.
      -- apply (hda3_strip_done _ k q r); [lia | lia | rewrite Lsl; lia | exact HB0 | exact Hq2 | exact HBr |
           exact BL | lia].
      -- hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
      -- hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
      -- hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
      -- prreg HS (20%bv : bv 5) Q20. rewrite Q20, (EE 26%nat 26%bv eq_refl). exact R26.
Qed.
End e.
End f.
End d.
