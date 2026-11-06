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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 84 of its 129 lines of code are new or changed and 408 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: what the point walks m_file_s_hdra_<k>.v share. The
   seed of lib/A/Prog/m_file_sd.v at a point with its spill slots made read-only (hda_ro_slots: no HDRA run writes a
   slot before a refusal), so a token run over the state keeps every byte (hda_frame_ro) and the point's facts carry
   to the run's end (hda_line_carry, over m_file_k.v's mf_carry_eq); the value ranges the seed asks; the tactics
   that read a kept register (hda_rg) and close a run's write-permission goal over read-only regions (hda_awr_ro).
   The HDRA segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN1h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the spill slots' region (index 1 of the seed) with no write window *)
Definition hda_slots_ro (cells hnp : bool) (slx : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 24 160 0 0
  (mf_chunk112 :: (if cells then mf_cell_chunks else []) ++ (if hnp then [mf_chunk144] else []) ++ slx).

(* the write-permission goal of a run whose regions are all read-only *)
Ltac hda_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* a register the run left alone (the state holds its own atom k): its value at the seed, through EE; a token run
   extends the environment with fresh atoms from 1024 (ewset), which do not touch atom k *)
Ltac hda_ew Q := repeat (rewrite ew_ewset_other in Q by lia).
Ltac hda_rg HS EE k r := let Q := fresh "Q" in prreg HS r Q; hda_ew Q; rewrite Q; rewrite (EE k r eq_refl).
(* U of an expression over atoms below the fresh ones, in the extended environment *)
Lemma hda_U_ewset : forall E k w x, YN1h.sv_free k x = true -> U (ewset E k w) x = U E x.
Proof. intros E k w x H. unfold U. rewrite YN1h.sv_denot_ewset_free by exact H. reflexivity. Qed.
Ltac hda_U H := repeat (rewrite hda_U_ewset in H by reflexivity).

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

(* the seed's range for the next line's address *)
Lemma hda_np64 : forall v Wc memc mcc cur line p rest,
  mf_loop v Wc memc mcc cur line p rest -> 0 <= mf_next p rest < 2 ^ 64.
Proof.
intros v Wc memc mcc cur line p rest (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
unfold mf_next. pose proof (Nat.le_sub_l (length rest) (length (mf_rest rest))). lia.
Qed.
(* a run over a state whose regions are all read-only changed no byte *)
Lemma hda_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite HF; [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
(* the seed with the spill slots read-only *)
Lemma hda_ro_slots : forall E pc cells hnp slx hw lw lowcs shw lowsh ms,
  st_ok_pi SEGS VAL E (ss_mf pc cells hnp slx hw lw lowcs shw lowsh) ms ->
  regions_wf (list_upd (mf_regions cells hnp slx hw lw lowcs shw lowsh) 1 (hda_slots_ro cells hnp slx)) = true ->
  st_ok_pi SEGS VAL E (mkSS pc sr_mf (list_upd (mf_regions cells hnp slx hw lw lowcs shw lowsh) 1
    (hda_slots_ro cells hnp slx)) None mf_facts) ms.
Proof.
intros E pc cells hnp slx hw lw lowcs shw lowsh ms HS Hwf.
pose proof (st_ok_pi_region_nth E _ ms 1 _ HS eq_refl) as HR. cbn [ss_mem ss_mf mf_regions] in HR.
apply (ast_ok_pi_set_region E (ss_mf pc cells hnp slx hw lw lowcs shw lowsh) ms 1 (mf_r_slots cells hnp slx)
  (hda_slots_ro cells hnp slx) HS eq_refl eq_refl Hwf).
destruct HR as (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
intros o Ho. cbn [YP09.r_wlo YP09.r_whi hda_slots_ro] in Ho. lia.
Qed.
(* the line's facts across a run that changed no byte *)
Lemma hda_line_carry : forall n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest,
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, rdW Wc memc' a = rdW Wc memc a) ->
  hda_line B n v lyc Sc Wc memc' mdc' pos mcc cur line p rest.
Proof.
intros n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest
  (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP) HJ KA.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc memc' mdc' pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ
  (fun a _ => KA a) LOOP) as (CORE' & LOOP' & CELLSK & NPK).
exact (conj CX (conj LS (conj FRM (conj CORE' (conj (CELLSK cur CELLS) (conj Hlen (conj Hne (conj LOOP' (NPK _ NP))))))))).
Qed.
(* the shadow base atom of every seed *)
Lemma hda_E32 : forall regs1 v lyc pos cur np xs, ew (mfE regs1 v lyc pos cur np xs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
intros. pose proof (mfE_extra regs1 v lyc pos cur np xs 0 ltac:(unfold A_TEXT; lia)) as X.
cbn [Nat.add nth mf_extra map app] in X. exact X.
Qed.
(* a region apart from the seed's regions is apart from them with the slots read-only (same extents) *)
Lemma hda_alld_ro : forall E r cells hnp slx hw lw lowcs shw lowsh,
  all_disjoint E r (mf_regions cells hnp slx hw lw lowcs shw lowsh) ->
  all_disjoint E r (list_upd (mf_regions cells hnp slx hw lw lowcs shw lowsh) 1 (hda_slots_ro cells hnp slx)).
Proof. intros E r cells hnp slx hw lw lowcs shw lowsh H. exact H. Qed.
End e.
End f.
End d.

(* hda_regs (or mf_regs_at, with s10) at the end of a run that left those registers alone; s3 and s9 may have been
   pinned to their literals (SLit 32, SLit 0x100002200) *)
Ltac hda_lit_or HS EE k r R :=
  first [ hda_rg HS EE k r; exact R
        | let Q := fresh "Q" in prreg HS r Q; hda_ew Q; rewrite Q; first [reflexivity | rewrite R; reflexivity] ].
Ltac hda_regs_carry HS EE E32 HR :=
  let R2 := fresh "R" in let R3 := fresh "R" in let R4 := fresh "R" in let R8 := fresh "R" in
  let R9 := fresh "R" in let R18 := fresh "R" in let R19 := fresh "R" in let R25 := fresh "R" in
  let R24 := fresh "R" in
  pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24);
  unfold hda_regs;
  split; [hda_rg HS EE 2%nat (2%bv : bv 5); exact R2|]; split; [hda_rg HS EE 3%nat (3%bv : bv 5); exact R3|];
  split; [hda_rg HS EE 4%nat (4%bv : bv 5); exact R4|]; split; [hda_rg HS EE 8%nat (8%bv : bv 5); exact R8|];
  split; [let Q := fresh "Q" in prreg HS (9%bv : bv 5) Q; hda_ew Q; rewrite Q, (EE 2%nat 2%bv eq_refl); exact R2|];
  split; [let Q := fresh "Q" in prreg HS (18%bv : bv 5) Q; hda_ew Q; rewrite Q, E32; reflexivity|];
  split; [hda_lit_or HS EE 19%nat (19%bv : bv 5) R19|]; split; [hda_lit_or HS EE 25%nat (25%bv : bv 5) R25|];
  hda_rg HS EE 24%nat (24%bv : bv 5); exact R24.
Ltac mf_regs_carry HS EE E32 HR :=
  let R2 := fresh "R" in let R3 := fresh "R" in let R4 := fresh "R" in let R8 := fresh "R" in
  let R9 := fresh "R" in let R18 := fresh "R" in let R19 := fresh "R" in let R25 := fresh "R" in
  let R26 := fresh "R" in
  pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26);
  unfold mf_regs_at;
  split; [hda_rg HS EE 2%nat (2%bv : bv 5); exact R2|]; split; [hda_rg HS EE 3%nat (3%bv : bv 5); exact R3|];
  split; [hda_rg HS EE 4%nat (4%bv : bv 5); exact R4|]; split; [hda_rg HS EE 8%nat (8%bv : bv 5); exact R8|];
  split; [let Q := fresh "Q" in prreg HS (9%bv : bv 5) Q; hda_ew Q; rewrite Q, (EE 2%nat 2%bv eq_refl); exact R2|];
  split; [let Q := fresh "Q" in prreg HS (18%bv : bv 5) Q; hda_ew Q; rewrite Q, E32; reflexivity|];
  split; [hda_lit_or HS EE 19%nat (19%bv : bv 5) R19|]; split; [hda_lit_or HS EE 25%nat (25%bv : bv 5) R25|];
  hda_rg HS EE 26%nat (26%bv : bv 5); exact R26.
